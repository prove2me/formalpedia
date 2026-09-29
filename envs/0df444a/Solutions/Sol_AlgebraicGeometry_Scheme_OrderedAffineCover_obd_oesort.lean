-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.obd_oesort
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8ca71485-fee6-57bb-ac58-8c7ca5ed462b

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains
import Theorems.Thm_Equiv_Perm_exists_comp_succAbove_eq_succAbove_comp_and_sign_eq
import Theorems.Thm_Tuple_succAbove_sort_comp_succAbove_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_oesort

set_option autoImplicit false

universe u

namespace SortChainAux

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

end SortChainAux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.OrderedAffineCover SortChainAux

theorem SortChainAux.val_negOne_pow (m : ℕ) : (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) = (-1 : ℤ) ^ m := by
  have h1 : (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) ^ m := Units.val_pow_eq_pow_val _ _
  rw [h1, Units.val_neg, Units.val_one]

theorem solution
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (n : ℕ) (x : K.OCh (n + 1)) :
    K.obd n (K.oesort (n + 1) x) = K.oesort n (K.obd n x) := by
  classical

  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single u a =>
    rw [← mul_one a, ← Finsupp.smul_single', map_zsmul, map_zsmul, map_zsmul, map_zsmul]
    congr 1

    rw [K.obd_single, map_sum]
    by_cases hinj : Function.Injective u
    ·
      set σ := Tuple.sort u with hσ
      have hfinj : ∀ j : Fin (n + 2), Function.Injective (K.oface u j) := fun j => hinj.comp Fin.succAbove_right_injective
      rw [K.oesort_single_of_injective (n + 1) u hinj, map_zsmul, K.obd_single, Finset.smul_sum]

      have hR : ∀ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) • K.oesort n (Finsupp.single (K.oface u j) 1) =
          ((-1 : ℤ) ^ (j : ℕ) * ((((-1) ^ (((σ.symm j) : ℕ) + (j : ℕ)) * Equiv.Perm.sign σ : ℤˣ)) : ℤ)) •
            Finsupp.single (K.oface (u ∘ σ : K.OIdx (n + 1)) (σ.symm j)) (1 : ℤ) := by
        intro j
        rw [K.oesort_single_of_injective n _ (hfinj j), smul_smul,
          show Tuple.sort (K.oface u j) = Tuple.sort (u ∘ j.succAbove) from rfl, sign_sort_face u hinj j]
        congr 1
        change Finsupp.single ((u ∘ j.succAbove) ∘ Tuple.sort (u ∘ j.succAbove) : K.OIdx n) (1 : ℤ) =
          Finsupp.single ((u ∘ Tuple.sort u) ∘ Fin.succAbove (σ.symm j) : K.OIdx n) 1
        congr 1
        funext k
        exact sorted_face_apply u hinj j k
      have hRHS : ∑ j : Fin (n + 2), K.oesort n (((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (K.oface u j) (1 : ℤ)) =
          ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ) * ((((-1) ^ (((σ.symm j) : ℕ) + (j : ℕ)) * Equiv.Perm.sign σ : ℤˣ)) : ℤ)) •
            Finsupp.single (K.oface (u ∘ σ : K.OIdx (n + 1)) (σ.symm j)) (1 : ℤ) :=
        Finset.sum_congr rfl (fun j _ => by rw [map_zsmul]; exact hR j)
      rw [hRHS]

      symm
      refine Fintype.sum_equiv σ.symm _ _ fun j => ?_
      rw [smul_smul]
      congr 1
      rw [Units.val_mul, val_negOne_pow, pow_add]
      have h2 : ((-1 : ℤ) ^ (j : ℕ)) * ((-1 : ℤ) ^ (j : ℕ)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      linear_combination ((-1 : ℤ) ^ ((σ.symm j : Fin (n + 2)) : ℕ) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) * h2
    ·
      rw [K.oesort_single_of_not_injective (n + 1) u hinj, map_zero]
      symm
      have hterm0 : ∀ j : Fin (n + 2), ¬ Function.Injective (K.oface u j) →
          K.oesort n (((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (K.oface u j) 1) = 0 := by
        intro j hj
        rw [map_zsmul, K.oesort_single_of_not_injective n _ hj, smul_zero]
      by_cases hnone : ∀ j : Fin (n + 2), ¬ Function.Injective (K.oface u j)
      · exact Finset.sum_eq_zero fun j _ => hterm0 j (hnone j)
      push Not at hnone
      obtain ⟨a, ha⟩ := hnone
      obtain ⟨b, hba, huab, hothers⟩ := exists_partner u hinj (a := a) ha
      obtain ⟨hb, hsorted, hsignb⟩ := collision u hba.symm huab ha
      have hb' : Function.Injective (K.oface u b) := hb
      rw [Fintype.sum_eq_add a b hba.symm (fun c hc => hterm0 c (hothers c hc.1 hc.2)), map_zsmul, map_zsmul,
        K.oesort_single_of_injective n _ ha, K.oesort_single_of_injective n _ hb']
      have hidx : (K.oface u b ∘ Tuple.sort (K.oface u b) : K.OIdx n) = (K.oface u a ∘ Tuple.sort (K.oface u a) : K.OIdx n) := hsorted
      rw [hidx, smul_smul, smul_smul, ← add_smul,
        show Tuple.sort (K.oface u b) = Tuple.sort (u ∘ b.succAbove) from rfl,
        show Tuple.sort (K.oface u a) = Tuple.sort (u ∘ a.succAbove) from rfl, hsignb,
        Units.val_neg, Units.val_mul, val_negOne_pow, pow_add]
      have h2 : ((-1 : ℤ) ^ (b : ℕ)) * ((-1 : ℤ) ^ (b : ℕ)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      have : (-1 : ℤ) ^ (a : ℕ) * ((Equiv.Perm.sign (Tuple.sort (u ∘ a.succAbove)) : ℤˣ) : ℤ) +
          (-1 : ℤ) ^ (b : ℕ) * -((-1 : ℤ) ^ (a : ℕ) * (-1 : ℤ) ^ (b : ℕ) * ((Equiv.Perm.sign (Tuple.sort (u ∘ a.succAbove)) : ℤˣ) : ℤ)) = 0 := by
        linear_combination (-((-1 : ℤ) ^ (a : ℕ)) * ((Equiv.Perm.sign (Tuple.sort (u ∘ a.succAbove)) : ℤˣ) : ℤ)) * h2
      rw [this, zero_smul]

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_oesort
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_oesort (solution)
