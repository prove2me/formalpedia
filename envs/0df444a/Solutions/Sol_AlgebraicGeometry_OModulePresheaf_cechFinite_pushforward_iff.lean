-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6cb15231-79c8-557c-bf94-0d58832d5c8a

import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Finiteness.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme IsClosedImmersion OModulePresheaf.pushforward OModulePresheaf OModulePresheaf.d_apply OModulePresheaf.cechFinite_iff_of_cochain_equiv"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "zero pushforward pushforward_res cochain d d_apply CechFinite res res_refl obj res_comp cechFinite_iff_of_cochain_equiv"
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section Transport

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {ρ : Z ⟶ Spec (.of R)} (H : OModulePresheaf ρ)

def resEq {U U' : Z.Opens} (h : U = U') : H.obj U ≃ₗ[R] H.obj U' where
  toFun := H.res h.ge
  invFun := H.res h.le
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    show (H.res h.le ∘ₗ H.res h.ge) x = x
    rw [← H.res_comp]; exact LinearMap.congr_fun (H.res_refl U) x
  right_inv x := by
    show (H.res h.ge ∘ₗ H.res h.le) x = x
    rw [← H.res_comp]; exact LinearMap.congr_fun (H.res_refl U') x

theorem resEq_apply {U U' : Z.Opens} (h : U = U') (x : H.obj U) : resEq H h x = H.res h.ge x := rfl

theorem res_res_apply {U₁ U₂ U₃ : Z.Opens} (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂) (x : H.obj U₁) :
    H.res h₂ (H.res h₁ x) = H.res (h₂.trans h₁) x := by
  rw [← LinearMap.comp_apply, ← H.res_comp]

end Transport

section Pushforward

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} {π : V ⟶ Spec (.of R)} (i : Z ⟶ V) [IsClosedImmersion i]
variable (H : OModulePresheaf (i ≫ π)) (K : V.OrderedAffineCover)

theorem map_iInf_fin' {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ} (U : Fin (n + 1) → Y.Opens) :
    (Opens.map f.base).obj (⨅ j, U j) = ⨅ j, (Opens.map f.base).obj (U j) := by
  have hsplit : ∀ {α : Type u} [CompleteLattice α] {m : ℕ} (g : Fin (m + 2) → α),
      (⨅ j : Fin (m + 2), g j) = g 0 ⊓ (⨅ j : Fin (m + 1), g j.succ) := fun g =>
    le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
      (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  induction n with
  | zero => simp only [show (⨅ j : Fin 1, U j) = U 0 from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl),
      show (⨅ j : Fin 1, (Opens.map f.base).obj (U j)) = (Opens.map f.base).obj (U 0) from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)]
  | succ m ih =>
    rw [hsplit U, show (Opens.map f.base).obj (U 0 ⊓ (⨅ j : Fin (m + 1), U j.succ))
        = (Opens.map f.base).obj (U 0) ⊓ (Opens.map f.base).obj (⨅ j : Fin (m + 1), U j.succ)
      from rfl, ih (fun j => U j.succ), hsplit (fun j => (Opens.map f.base).obj (U j))]

theorem inter_preimage {q : ℕ} (s : (K.preimage i).Idx q) :
    (K.preimage i).inter s = i ⁻¹ᵁ K.inter (show K.Idx q from s) :=
  (map_iInf_fin' i _).symm

def pushforwardCochainEquiv (q : ℕ) : H.cochain (K.preimage i) q ≃ₗ[R] (pushforward π i H).cochain K q :=
  LinearEquiv.piCongrRight fun s => resEq H (inter_preimage i K s)

theorem pushforwardCochainEquiv_d (q : ℕ) (x : H.cochain (K.preimage i) q) :
    pushforwardCochainEquiv i H K (q + 1) (H.d (K.preimage i) q x)
      = (pushforward π i H).d K q (pushforwardCochainEquiv i H K q x) := by
  funext s
  show resEq H (inter_preimage i K s) (H.d (K.preimage i) q x s) = (pushforward π i H).d K q _ s
  rw [resEq_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pushforward_res, res_res_apply]
  congr 1
  show _ = H.res _ (resEq H (inter_preimage i K _) (x _))
  rw [resEq_apply, res_res_apply]
  rfl

end Pushforward

end AlgebraicGeometry.OModulePresheaf

end

theorem solution
    {R : Type u} [CommRing R] {V Z : Scheme.{u}} {π : V ⟶ Spec (.of R)} (i : Z ⟶ V) [IsClosedImmersion i]
    (H : OModulePresheaf (i ≫ π)) (K : V.OrderedAffineCover) :
    (OModulePresheaf.pushforward π i H).CechFinite K ↔ H.CechFinite (K.preimage i) :=
  (AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochain_equiv H (OModulePresheaf.pushforward π i H)
    (K.preimage i) K (AlgebraicGeometry.OModulePresheaf.pushforwardCochainEquiv i H K)
    (AlgebraicGeometry.OModulePresheaf.pushforwardCochainEquiv_d i H K)).symm

end S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff (solution)
