-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.od_oext
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fe519b3f-2934-5b62-b3bc-4c8f60d86efb

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Theorems.Thm_Equiv_Perm_exists_comp_succAbove_eq_succAbove_comp_and_sign_eq
import Theorems.Thm_Tuple_succAbove_sort_comp_succAbove_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_od_oext

set_option autoImplicit false

universe u

namespace OextChainAux

open Equiv

section Comb

variable {ι : Type*} [LinearOrder ι] {n : ℕ}

theorem units_pow_mul_self (m : ℕ) : ((-1 : ℤˣ) ^ m) * ((-1 : ℤˣ) ^ m) = 1 := Int.units_mul_self _

theorem sorted_face_apply (u : Fin (n + 1) → ι) (hu : Function.Injective u) (j : Fin (n + 1)) (k : Fin n) :
    (u ∘ j.succAbove) (Tuple.sort (u ∘ j.succAbove) k) = (u ∘ Tuple.sort u) (((Tuple.sort u).symm j).succAbove k) := by
  show u (j.succAbove (Tuple.sort (u ∘ j.succAbove) k)) = u (Tuple.sort u (((Tuple.sort u).symm j).succAbove k))
  rw [Tuple.succAbove_sort_comp_succAbove_eq u hu j k]

theorem sign_sort_face (u : Fin (n + 1) → ι) (hu : Function.Injective u) (j : Fin (n + 1)) :
    Equiv.Perm.sign (Tuple.sort (u ∘ j.succAbove)) =
      (-1) ^ ((((Tuple.sort u).symm j) : ℕ) + (j : ℕ)) * Equiv.Perm.sign (Tuple.sort u) := by
  set σ := Tuple.sort u with hσ
  set i := σ.symm j with hi
  have hσi : σ i = j := by rw [hi, Equiv.apply_symm_apply]
  obtain ⟨τ, hτ, hsign⟩ := Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq σ i
  rw [hσi] at hτ hsign
  have hτeq : τ = Tuple.sort (u ∘ j.succAbove) := by
    refine Equiv.ext fun k => ?_
    apply Fin.succAbove_right_injective (p := j)
    show j.succAbove (τ k) = j.succAbove (Tuple.sort (u ∘ j.succAbove) k)
    rw [← hτ k, Tuple.succAbove_sort_comp_succAbove_eq u hu j k]
  rw [← hτeq, hsign, ← mul_assoc, units_pow_mul_self, one_mul]

theorem collision (u : Fin (n + 1) → ι) {a b : Fin (n + 1)} (hab : a ≠ b) (huab : u a = u b)
    (ha : Function.Injective (u ∘ a.succAbove)) :
    Function.Injective (u ∘ b.succAbove) ∧
    (u ∘ b.succAbove) ∘ Tuple.sort (u ∘ b.succAbove) = (u ∘ a.succAbove) ∘ Tuple.sort (u ∘ a.succAbove) ∧
    Equiv.Perm.sign (Tuple.sort (u ∘ b.succAbove)) = -((-1) ^ ((a : ℕ) + (b : ℕ)) * Equiv.Perm.sign (Tuple.sort (u ∘ a.succAbove))) := by
  obtain ⟨π, hπ, hsign⟩ := Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq (Equiv.swap a b) b
  rw [Equiv.swap_apply_right] at hπ hsign

  have hcomp : u ∘ b.succAbove = (u ∘ a.succAbove) ∘ π := by
    funext k
    show u (b.succAbove k) = u (a.succAbove (π k))
    rw [← hπ k]
    by_cases hk : b.succAbove k = a
    · rw [hk, Equiv.swap_apply_left, huab]
    · rw [Equiv.swap_apply_of_ne_of_ne hk (Fin.succAbove_ne b k)]
  have hinjb : Function.Injective (u ∘ b.succAbove) := by rw [hcomp]; exact ha.comp π.injective
  refine ⟨hinjb, ?_, ?_⟩
  · rw [hcomp]; exact Tuple.comp_perm_comp_sort_eq_comp_sort
  ·
    have hsort : π⁻¹ * Tuple.sort (u ∘ a.succAbove) = Tuple.sort (u ∘ b.succAbove) := by
      rw [Tuple.eq_sort_iff]
      refine ⟨?_, ?_⟩
      · rw [hcomp]
        intro x y hxy
        show ((u ∘ a.succAbove) ∘ π) ((π⁻¹ * Tuple.sort (u ∘ a.succAbove)) x) ≤ ((u ∘ a.succAbove) ∘ π) ((π⁻¹ * Tuple.sort (u ∘ a.succAbove)) y)
        have hππ : ∀ z, π (π⁻¹ z) = z := fun z => Equiv.apply_symm_apply π z
        simp only [Function.comp_apply, Equiv.Perm.coe_mul, hππ]
        exact Tuple.monotone_sort (u ∘ a.succAbove) hxy
      · intro x y hxy heq
        exact absurd ((π⁻¹ * Tuple.sort (u ∘ a.succAbove)).injective (hinjb heq) ▸ hxy) (lt_irrefl _)
    rw [← hsort, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Equiv.Perm.sign_swap hab] at *

    have hπs : Equiv.Perm.sign π = -((-1) ^ ((a : ℕ) + (b : ℕ))) := by
      have := hsign
      rw [add_comm] at this
      calc Equiv.Perm.sign π = ((-1) ^ ((a : ℕ) + (b : ℕ)) * (-1) ^ ((a : ℕ) + (b : ℕ))) * Equiv.Perm.sign π := by
            rw [units_pow_mul_self, one_mul]
        _ = (-1) ^ ((a : ℕ) + (b : ℕ)) * -1 := by rw [mul_assoc, ← this]
        _ = -((-1) ^ ((a : ℕ) + (b : ℕ))) := mul_neg_one _
    rw [hπs, neg_mul]

theorem exists_partner (u : Fin (n + 1) → ι) (hu : ¬ Function.Injective u) {a : Fin (n + 1)}
    (ha : Function.Injective (u ∘ a.succAbove)) :
    ∃ b, b ≠ a ∧ u a = u b ∧ ∀ c, c ≠ a → c ≠ b → ¬ Function.Injective (u ∘ c.succAbove) := by

  have : ∃ x y, x ≠ y ∧ u x = u y := by
    by_contra h; push Not at h; exact hu fun x y hxy => by_contra fun hne => h x y hne hxy
  obtain ⟨x, y, hxy, huxy⟩ := this

  have key : ∀ x y, x ≠ y → u x = u y → x = a ∨ y = a := by
    intro x y hxy huxy
    by_contra h; push Not at h
    obtain ⟨x', hx'⟩ := Fin.exists_succAbove_eq h.1
    obtain ⟨y', hy'⟩ := Fin.exists_succAbove_eq h.2
    have : x' = y' := ha (by show u (a.succAbove x') = u (a.succAbove y'); rw [hx', hy', huxy])
    exact hxy (by rw [← hx', ← hy', this])

  have hb : ∃ b, b ≠ a ∧ u a = u b := by
    rcases key x y hxy huxy with rfl | rfl
    · exact ⟨y, hxy.symm, huxy⟩
    · exact ⟨x, hxy, huxy.symm⟩
  obtain ⟨b, hba, huab⟩ := hb
  refine ⟨b, hba, huab, fun c hca hcb hinj => ?_⟩
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hca.symm
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hcb.symm
  have : a' = b' := hinj (by show u (c.succAbove a') = u (c.succAbove b'); rw [ha', hb', huab])
  exact hba (by rw [← hb', ← ha', this])

end Comb

theorem val_negOne_pow (m : ℕ) : (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) = (-1 : ℤ) ^ m := by
  have h1 : (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) ^ m := Units.val_pow_eq_pow_val _ _
  rw [h1, Units.val_neg, Units.val_one]

end OextChainAux

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme.OrderedAffineCover

namespace OextChainMain

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
  (F : OModulePresheaf π) (K : V.OrderedAffineCover) {m : ℕ} (z : F.cochain K m)

noncomputable def qb (T : K.Idx m) (W : V.Opens) (hW : W ≤ K.inter T) : F.obj W := F.res hW (z T)

theorem res_qb (T : K.Idx m) {W W' : V.Opens} (hW : W ≤ K.inter T) (hW' : W' ≤ W) (hW'' : W' ≤ K.inter T) :
    F.res hW' (qb F K z T W hW) = qb F K z T W' hW'' := by
  unfold qb; rw [F.res_res]

theorem qb_congr {T T' : K.Idx m} (e : T = T') (W : V.Opens) (hW : W ≤ K.inter T) (hW' : W ≤ K.inter T') :
    qb F K z T W hW = qb F K z T' W hW' := by
  subst e; rfl

end OextChainMain

open OextChainAux OextChainMain in
theorem od_oext_main
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.od K n (F.oext K n z) = F.oext K (n + 1) (F.d K n z) := by
  classical
  funext t
  rw [od_apply]
  have hterm : ∀ (j : Fin (n + 2)) (hj : Function.Injective (K.oface t j)),
      F.res (K.ointer_le_ointer_oface t j) (F.oext K n z (K.oface t j)) =
      ((Equiv.Perm.sign (Tuple.sort (K.oface t j)) : ℤˣ) : ℤ) •
        qb F K z (K.osort (K.oface t j) hj) (K.ointer t)
          ((K.ointer_le_ointer_oface t j).trans (K.ointer_le_inter_osort (K.oface t j) hj)) := by
    intro j hj
    rw [oext_apply_of_injective _ _ _ _ _ hj, map_zsmul]
    congr 1
    exact res_qb F K z _ _ _ _
  have hterm0 : ∀ (j : Fin (n + 2)) (hj : ¬ Function.Injective (K.oface t j)),
      F.res (K.ointer_le_ointer_oface t j) (F.oext K n z (K.oface t j)) = 0 := by
    intro j hj
    rw [oext_apply_of_not_injective _ _ _ _ _ hj, map_zero]
  by_cases hinj : Function.Injective t
  · set σ := Tuple.sort t with hσ
    set S := K.osort t hinj with hS
    have hle : K.ointer t ≤ K.inter S := K.ointer_le_inter_osort t hinj
    have hfinj : ∀ j : Fin (n + 2), Function.Injective (K.oface t j) := fun j =>
      hinj.comp Fin.succAbove_right_injective
    have hface : ∀ j : Fin (n + 2), K.osort (K.oface t j) (hfinj j) = K.face S (σ.symm j) := by
      intro j
      apply Subtype.ext
      funext k
      show ((t ∘ Fin.succAbove j) ∘ Tuple.sort (t ∘ Fin.succAbove j)) k = ((t ∘ Tuple.sort t) ∘ Fin.succAbove (σ.symm j)) k
      exact sorted_face_apply t hinj j k
    have hleS : ∀ i, K.ointer t ≤ K.inter (K.face S i) := fun i => hle.trans (K.inter_le_inter_face S i)
    have hL : ∀ j : Fin (n + 2),
        (-1 : ℤ) ^ (j : ℕ) • F.res (K.ointer_le_ointer_oface t j) (F.oext K n z (K.oface t j)) =
        ((-1 : ℤ) ^ (j : ℕ) * ((((-1) ^ (((σ.symm j) : ℕ) + (j : ℕ)) * Equiv.Perm.sign σ : ℤˣ)) : ℤ)) •
          qb F K z (K.face S (σ.symm j)) (K.ointer t) (hleS (σ.symm j)) := by
      intro j
      rw [hterm j (hfinj j), qb_congr F K z (hface j) _ _ (hleS (σ.symm j)),
        show Tuple.sort (K.oface t j) = Tuple.sort (t ∘ j.succAbove) from rfl, sign_sort_face t hinj j, smul_smul]
    rw [Finset.sum_congr rfl (fun j _ => hL j)]
    rw [oext_apply_of_injective _ _ _ _ _ hinj, d_apply]
    symm
    rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv σ _ _ fun i => ?_
    rw [map_zsmul, smul_smul, Equiv.symm_apply_apply]
    rw [show F.res hle (F.res (K.inter_le_inter_face S i) (z (K.face S i))) = qb F K z (K.face S i) (K.ointer t) (hleS i) from
      by unfold qb; rw [F.res_res]]
    congr 1
    rw [Units.val_mul, val_negOne_pow, pow_add]
    have h2 : ((-1 : ℤ) ^ ((σ i : Fin (n + 2)) : ℕ)) * ((-1 : ℤ) ^ ((σ i : Fin (n + 2)) : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination (-((-1 : ℤ) ^ (i : ℕ)) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) * h2
  · rw [oext_apply_of_not_injective _ _ _ _ _ hinj]
    by_cases hnone : ∀ j : Fin (n + 2), ¬ Function.Injective (K.oface t j)
    · exact Finset.sum_eq_zero fun j _ => by rw [hterm0 j (hnone j), smul_zero]
    push Not at hnone
    obtain ⟨a, ha⟩ := hnone
    obtain ⟨b, hba, huab, hothers⟩ := exists_partner t hinj (a := a) ha
    obtain ⟨hb, hsorted, hsignb⟩ := collision t hba.symm huab ha
    rw [Fintype.sum_eq_add a b hba.symm (fun c hc => by rw [hterm0 c (hothers c hc.1 hc.2), smul_zero]),
      hterm a ha, hterm b hb]
    have hidx : K.osort (K.oface t b) hb = K.osort (K.oface t a) ha := by
      apply Subtype.ext
      exact hsorted
    have hlea : K.ointer t ≤ K.inter (K.osort (K.oface t a) ha) :=
      (K.ointer_le_ointer_oface t a).trans (K.ointer_le_inter_osort (K.oface t a) ha)
    rw [qb_congr F K z hidx _ _ hlea]
    show (-1 : ℤ) ^ (a : ℕ) • (((Equiv.Perm.sign (Tuple.sort (t ∘ a.succAbove)) : ℤˣ) : ℤ) •
          qb F K z (K.osort (K.oface t a) ha) (K.ointer t) hlea) +
        (-1 : ℤ) ^ (b : ℕ) • (((Equiv.Perm.sign (Tuple.sort (t ∘ b.succAbove)) : ℤˣ) : ℤ) •
          qb F K z (K.osort (K.oface t a) ha) (K.ointer t) hlea) = 0
    rw [smul_smul, smul_smul, ← add_smul, hsignb, Units.val_neg, Units.val_mul, val_negOne_pow, pow_add]
    have h2 : ((-1 : ℤ) ^ (b : ℕ)) * ((-1 : ℤ) ^ (b : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have : (-1 : ℤ) ^ (a : ℕ) * ((Equiv.Perm.sign (Tuple.sort (t ∘ a.succAbove)) : ℤˣ) : ℤ) +
        (-1 : ℤ) ^ (b : ℕ) * -((-1 : ℤ) ^ (a : ℕ) * (-1 : ℤ) ^ (b : ℕ) * ((Equiv.Perm.sign (Tuple.sort (t ∘ a.succAbove)) : ℤˣ) : ℤ)) = 0 := by
      linear_combination (-((-1 : ℤ) ^ (a : ℕ)) * ((Equiv.Perm.sign (Tuple.sort (t ∘ a.succAbove)) : ℤˣ) : ℤ)) * h2
    rw [this, zero_smul]

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.od K n (F.oext K n z) = F.oext K (n + 1) (F.d K n z) :=
  od_oext_main F K n z

end S_AlgebraicGeometry_OModulePresheaf_od_oext
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_od_oext (solution)
