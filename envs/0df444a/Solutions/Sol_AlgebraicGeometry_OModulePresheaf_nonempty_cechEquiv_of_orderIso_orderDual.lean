-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_of_orderIso_orderDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a2f59bed-8686-559f-a317-19240a61da30

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry OrderDual

namespace P2mCechReverse

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)
  (K K' : V.OrderedAffineCover) (e : K.ι ≃o (K'.ι)ᵒᵈ)

def idx (i : ℕ) : K.Idx i ≃ K'.Idx i where
  toFun s := ⟨fun k => ofDual (e (s.1 (Fin.rev k))), fun k k' h =>
    ofDual_lt_ofDual.mpr (e.strictMono (s.2 (Fin.rev_lt_rev.mpr h)))⟩
  invFun s' := ⟨fun k => e.symm (toDual (s'.1 (Fin.rev k))), fun k k' h =>
    e.symm.strictMono (toDual_lt_toDual.mpr (s'.2 (Fin.rev_lt_rev.mpr h)))⟩
  left_inv s := Subtype.ext (funext fun j => by simp [Fin.rev_rev])
  right_inv s' := Subtype.ext (funext fun j => by simp [Fin.rev_rev])

theorem idx_apply {i : ℕ} (s : K.Idx i) (k : Fin (i + 1)) : (idx K K' e i s).1 k = ofDual (e (s.1 (Fin.rev k))) :=
  rfl

theorem idx_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    idx K K' e i (K.face s j) = K'.face (idx K K' e (i + 1) s) (Fin.rev j) := by
  apply Subtype.ext
  funext k
  show ofDual (e ((s.1 ∘ Fin.succAbove j) (Fin.rev k))) = ofDual (e (s.1 (Fin.rev (Fin.succAbove (Fin.rev j) k))))
  rw [Function.comp_apply, Fin.rev_succAbove, Fin.rev_rev]

variable (hU : ∀ i, K'.U (ofDual (e i)) = K.U i)

include hU in
theorem inter_idx {i : ℕ} (s : K.Idx i) : K'.inter (idx K K' e i s) = K.inter s := by
  show (⨅ k, K'.U (ofDual (e (s.1 (Fin.rev k))))) = ⨅ k, K.U (s.1 k)
  simp_rw [hU]
  exact Fin.rev_surjective.iInf_comp (fun k => K.U (s.1 k))

include hU in
theorem inter_symm {i : ℕ} (s' : K'.Idx i) : K'.inter s' = K.inter ((idx K K' e i).symm s') := by
  conv_lhs => rw [← (idx K K' e i).apply_symm_apply s']
  exact inter_idx K K' e hU _

def sgn : ℕ → ℤ
  | 0 => 1
  | n + 1 => (-1) ^ (n + 1) * sgn n

theorem sgn_succ (n : ℕ) : sgn (n + 1) = (-1) ^ (n + 1) * sgn n := rfl

theorem sgn_mul_self (n : ℕ) : sgn n * sgn n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sgn_succ, mul_mul_mul_comm, ih, mul_one, ← mul_pow, neg_mul_neg, one_mul, one_pow]

def phi (i : ℕ) : F.cochain K i →ₗ[R] F.cochain K' i :=
  (sgn i : ℤ) • LinearMap.pi fun s' =>
    (F.res (le_of_eq (inter_symm K K' e hU s'))).comp (LinearMap.proj ((idx K K' e i).symm s'))

theorem phi_apply (i : ℕ) (c : F.cochain K i) (s' : K'.Idx i) :
    phi F K K' e hU i c s' =
      (sgn i : ℤ) • F.res (le_of_eq (inter_symm K K' e hU s')) (c ((idx K K' e i).symm s')) := rfl

theorem res_eq_of_eq {U W : V.Opens} (h : U ≤ W) (h' : W ≤ U) (x : F.obj U) : F.res h (F.res h' x) = x := by
  rw [F.res_res, F.res_refl_apply]

theorem phi_apply_idx (i : ℕ) (c : F.cochain K i) (s : K.Idx i) (h : K'.inter (idx K K' e i s) ≤ K.inter s) :
    phi F K K' e hU i c (idx K K' e i s) = (sgn i : ℤ) • F.res h (c s) := by
  rw [phi_apply]
  have hs : (idx K K' e i).symm (idx K K' e i s) = s := Equiv.symm_apply_apply _ _
  generalize_proofs h1
  revert h1
  rw [hs]
  intro h1
  rfl

theorem phi_apply_face (i : ℕ) (c : F.cochain K i) (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (h : K'.inter (K'.face (idx K K' e (i + 1) s) (Fin.rev j)) ≤ K.inter (K.face s j)) :
    phi F K K' e hU i c (K'.face (idx K K' e (i + 1) s) (Fin.rev j)) = (sgn i : ℤ) • F.res h (c (K.face s j)) := by
  have key : ∀ (t : K'.Idx i) (ht : t = idx K K' e i (K.face s j)) (h' : K'.inter t ≤ K.inter (K.face s j)),
      phi F K K' e hU i c t = (sgn i : ℤ) • F.res h' (c (K.face s j)) := by
    intro t ht h'
    subst ht
    exact phi_apply_idx F K K' e hU i c (K.face s j) h'
  exact key _ (idx_face K K' e s j).symm h

include hU in
theorem inter_face_le (i : ℕ) (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K'.inter (K'.face (idx K K' e (i + 1) s) (Fin.rev j)) ≤ K.inter (K.face s j) := by
  rw [← idx_face]; exact le_of_eq (inter_idx K K' e hU (K.face s j))

theorem phi_surjective (i : ℕ) : Function.Surjective (phi F K K' e hU i) := by
  intro c'
  refine ⟨fun s => (sgn i : ℤ) • F.res (le_of_eq (inter_idx K K' e hU s).symm) (c' (idx K K' e i s)),
    funext fun s' => ?_⟩
  obtain ⟨s, rfl⟩ := (idx K K' e i).surjective s'
  rw [phi_apply_idx F K K' e hU i _ s (le_of_eq (inter_idx K K' e hU s)), LinearMap.map_smul_of_tower,
    res_eq_of_eq, smul_smul, sgn_mul_self, one_smul]

theorem phi_injective (i : ℕ) : Function.Injective (phi F K K' e hU i) := by
  intro c₁ c₂ h
  funext s
  have := congrFun h (idx K K' e i s)
  rw [phi_apply_idx F K K' e hU i _ s (le_of_eq (inter_idx K K' e hU s)),
    phi_apply_idx F K K' e hU i _ s (le_of_eq (inter_idx K K' e hU s))] at this
  have := congrArg (fun x => (sgn i : ℤ) • F.res (le_of_eq (inter_idx K K' e hU s).symm) x) this
  simp only [LinearMap.map_smul_of_tower, res_eq_of_eq, smul_smul, sgn_mul_self, one_smul] at this
  exact this

theorem neg_one_pow_rev {i : ℕ} (j : Fin (i + 2)) :
    ((-1 : ℤ) ^ ((Fin.rev j : Fin (i + 2)) : ℕ)) * sgn i = sgn (i + 1) * (-1) ^ (j : ℕ) := by
  rw [sgn_succ, Fin.val_rev]
  have hj : (j : ℕ) ≤ i + 1 := Nat.lt_succ_iff.mp j.2
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hj
  have h2 : i + 2 = m + ((j : ℕ) + 1) := by
    calc i + 2 = (i + 1) + 1 := rfl
      _ = ((j : ℕ) + m) + 1 := congrArg (· + 1) hm
      _ = m + ((j : ℕ) + 1) := by ring
  rw [Nat.sub_eq_of_eq_add h2, hm, pow_add]
  ring_nf
  rw [show (j : ℕ) * 2 = 2 * (j : ℕ) by ring, pow_mul, neg_one_sq, one_pow, mul_one]

theorem d_phi (i : ℕ) (c : F.cochain K i) :
    F.d K' i (phi F K K' e hU i c) = phi F K K' e hU (i + 1) (F.d K i c) := by
  funext s'
  obtain ⟨s, rfl⟩ := (idx K K' e (i + 1)).surjective s'
  rw [phi_apply_idx F K K' e hU (i + 1) _ s (le_of_eq (inter_idx K K' e hU s)), OModulePresheaf.d_apply,
    OModulePresheaf.d_apply, map_sum, Finset.smul_sum]

  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.revPerm_apply, LinearMap.map_smul_of_tower,
    phi_apply_face F K K' e hU i c s j (inter_face_le K K' e hU i s j),
    LinearMap.map_smul_of_tower, F.res_res, F.res_res, smul_smul, smul_smul, neg_one_pow_rev]

include hU in

theorem main : Nonempty (F.H0 K ≃ₗ[R] F.H0 K') ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] F.HSucc K' i) := by
  have key := LinearMap.exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
    (R := R) (C := fun n => F.cochain K n) (D := fun n => F.cochain K' n)
    (fun n => F.d K n) (fun n => F.d K' n) (fun n => phi F K K' e hU n)
    (fun n x => (d_phi F K K' e hU n x).symm)
    (fun n x => by
      have := LinearMap.congr_fun (F.d_comp_d K n) x
      exact this)
    (fun n => phi_surjective F K K' e hU n)
    (fun x hx _ => phi_injective F K K' e hU 0 (by rw [hx, map_zero]))
    (fun n x hx _ => ⟨0, map_zero _, by rw [map_zero]; exact (phi_injective F K K' e hU (n + 1) (by rw [hx, map_zero])).symm⟩)
  obtain ⟨⟨e0, -⟩, hS⟩ := key
  exact ⟨⟨e0⟩, fun i => by obtain ⟨eS, -⟩ := hS i; exact ⟨eS⟩⟩

end P2mCechReverse

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)
    (K K' : V.OrderedAffineCover) (e : K.ι ≃o (K'.ι)ᵒᵈ) (hU : ∀ i, K'.U (OrderDual.ofDual (e i)) = K.U i) :
    Nonempty (F.H0 K ≃ₗ[R] F.H0 K') ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] F.HSucc K' i) :=
  P2mCechReverse.main F K K' e hU

end

end S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual (solution)
