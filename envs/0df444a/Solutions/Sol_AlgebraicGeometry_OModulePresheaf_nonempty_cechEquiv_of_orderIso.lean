-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_of_orderIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/355e2ff4-5202-54a3-8ad0-e685c5ab6ede

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mCechReindex

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)
  (K K' : V.OrderedAffineCover) (e : K.ι ≃o K'.ι)

def idx (i : ℕ) : K.Idx i ≃ K'.Idx i where
  toFun s := ⟨e ∘ s.1, e.strictMono.comp s.2⟩
  invFun s' := ⟨e.symm ∘ s'.1, e.symm.strictMono.comp s'.2⟩
  left_inv s := Subtype.ext (funext fun j => e.symm_apply_apply (s.1 j))
  right_inv s' := Subtype.ext (funext fun j => e.apply_symm_apply (s'.1 j))

theorem idx_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    idx K K' e i (K.face s j) = K'.face (idx K K' e (i + 1) s) j := rfl

variable (hU : ∀ i, K'.U (e i) = K.U i)

include hU in
theorem inter_idx {i : ℕ} (s : K.Idx i) : K'.inter (idx K K' e i s) = K.inter s := by
  show (⨅ j, K'.U ((e ∘ s.1) j)) = ⨅ j, K.U (s.1 j)
  exact iInf_congr fun j => by rw [Function.comp_apply, hU]

include hU in
theorem inter_symm {i : ℕ} (s' : K'.Idx i) : K'.inter s' = K.inter ((idx K K' e i).symm s') := by
  conv_lhs => rw [← (idx K K' e i).apply_symm_apply s']
  exact inter_idx K K' e hU _

def phi (i : ℕ) : F.cochain K i →ₗ[R] F.cochain K' i :=
  LinearMap.pi fun s' => (F.res (le_of_eq (inter_symm K K' e hU s'))).comp (LinearMap.proj ((idx K K' e i).symm s'))

theorem phi_apply (i : ℕ) (c : F.cochain K i) (s' : K'.Idx i) :
    phi F K K' e hU i c s' = F.res (le_of_eq (inter_symm K K' e hU s')) (c ((idx K K' e i).symm s')) := rfl

theorem res_eq_of_eq {U W : V.Opens} (h : U ≤ W) (h' : W ≤ U) (x : F.obj U) : F.res h (F.res h' x) = x := by
  rw [F.res_res, F.res_refl_apply]

theorem phi_apply_idx (i : ℕ) (c : F.cochain K i) (s : K.Idx i) (h : K'.inter (idx K K' e i s) ≤ K.inter s) :
    phi F K K' e hU i c (idx K K' e i s) = F.res h (c s) := by
  rw [phi_apply]
  have hs : (idx K K' e i).symm (idx K K' e i s) = s := Equiv.symm_apply_apply _ _
  generalize_proofs h1
  revert h1
  rw [hs]
  intro h1
  rfl

theorem phi_surjective (i : ℕ) : Function.Surjective (phi F K K' e hU i) := by
  intro c'
  refine ⟨fun s => F.res (le_of_eq (inter_idx K K' e hU s).symm) (c' (idx K K' e i s)), funext fun s' => ?_⟩
  obtain ⟨s, rfl⟩ := (idx K K' e i).surjective s'
  rw [phi_apply_idx F K K' e hU i _ s (le_of_eq (inter_idx K K' e hU s)), res_eq_of_eq]

theorem phi_injective (i : ℕ) : Function.Injective (phi F K K' e hU i) := by
  intro c₁ c₂ h
  funext s
  have := congrFun h (idx K K' e i s)
  rw [phi_apply_idx F K K' e hU i _ s (le_of_eq (inter_idx K K' e hU s)),
    phi_apply_idx F K K' e hU i _ s (le_of_eq (inter_idx K K' e hU s))] at this
  have := congrArg (F.res (le_of_eq (inter_idx K K' e hU s).symm)) this
  rwa [res_eq_of_eq, res_eq_of_eq] at this

theorem phi_apply_face (i : ℕ) (c : F.cochain K i) (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (h : K'.inter (K'.face (idx K K' e (i + 1) s) j) ≤ K.inter (K.face s j)) :
    phi F K K' e hU i c (K'.face (idx K K' e (i + 1) s) j) = F.res h (c (K.face s j)) :=
  phi_apply_idx F K K' e hU i c (K.face s j) h

theorem d_phi (i : ℕ) (c : F.cochain K i) :
    F.d K' i (phi F K K' e hU i c) = phi F K K' e hU (i + 1) (F.d K i c) := by
  funext s'
  obtain ⟨s, rfl⟩ := (idx K K' e (i + 1)).surjective s'
  rw [phi_apply_idx F K K' e hU (i + 1) _ s (le_of_eq (inter_idx K K' e hU s)), OModulePresheaf.d_apply,
    OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul_of_tower,
    phi_apply_face F K K' e hU i c s j (le_of_eq (inter_idx K K' e hU (K.face s j))), F.res_res, F.res_res]

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

end P2mCechReindex

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)
    (K K' : V.OrderedAffineCover) (e : K.ι ≃o K'.ι) (hU : ∀ i, K'.U (e i) = K.U i) :
    Nonempty (F.H0 K ≃ₗ[R] F.H0 K') ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] F.HSucc K' i) :=
  P2mCechReindex.main F K K' e hU

end

end S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso (solution)
