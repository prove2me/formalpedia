-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPullbackFaithful
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPullbackFaithful
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:33.71064+00:00
-- url     : https://prove2.me/theorems/201f6be7-9339-4a0a-9cfa-23e8517a63a4
-- title:
--   PPullback Faithful
-- statement:
--   Definitions and structural lemmas for PPullback Faithful, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPullbackFaithful.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullbackFaithful
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
section Coordinates
variable {X : Scheme.{u}} {B : X.Modules} {n : ℕ} {s : Fin n → Γ(B, ⊤)}
variable (B s) in

def basisExpand (W : X.Opens) : (Fin n → Γ(X, W)) →ₗ[Γ(X, W)] Γ(B, W) :=
  Fintype.linearCombination Γ(X, W)
    (fun i => (B.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom (s i))
lemma basisExpand_apply (W : X.Opens) (r : Fin n → Γ(X, W)) :
    basisExpand B s W r = ∑ i, r i • (B.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom (s i) :=
  Fintype.linearCombination_apply _ _ _
lemma basisExpand_map {W W' : X.Opens} (i : W' ≤ W) (r : Fin n → Γ(X, W)) :
    (B.presheaf.map (homOfLE i).op).hom (basisExpand B s W r) =
      basisExpand B s W' (fun k => (X.presheaf.map (homOfLE i).op).hom (r k)) := by
  rw [basisExpand_apply, basisExpand_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Scheme.Modules.map_smul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl
def basisEquiv (hs : IsBasisOn B ⊤ s) (W : X.Opens) :
    (Fin n → Γ(X, W)) ≃ₗ[Γ(X, W)] Γ(B, W) :=
  LinearEquiv.ofBijective (basisExpand B s W) (by
    have := hs W le_top
    convert this using 1
    funext r
    exact basisExpand_apply W r)
lemma basisEquiv_symm_map (hs : IsBasisOn B ⊤ s) {W W' : X.Opens} (i : W' ≤ W) (x : Γ(B, W))
    (k : Fin n) :
    (basisEquiv hs W').symm ((B.presheaf.map (homOfLE i).op).hom x) k =
      (X.presheaf.map (homOfLE i).op).hom ((basisEquiv hs W).symm x k) := by
  obtain ⟨r, rfl⟩ := (basisEquiv hs W).surjective x
  rw [LinearEquiv.symm_apply_apply]
  have : (B.presheaf.map (homOfLE i).op).hom (basisEquiv hs W r) =
      basisEquiv hs W' (fun k => (X.presheaf.map (homOfLE i).op).hom (r k)) :=
    basisExpand_map i r
  rw [this, LinearEquiv.symm_apply_apply]
def basisCoord (hs : IsBasisOn B ⊤ s) (j : Fin n) : B ⟶ structureModule X :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        ((LinearMap.proj j ∘ₗ (basisEquiv hs W.unop).symm.toLinearMap).toAddMonoidHom)
      naturality := fun W W' f => by
        ext x
        exact basisEquiv_symm_map hs (leOfHom f.unop) x j }
    (fun W r x =>
      (LinearMap.proj j ∘ₗ (basisEquiv hs W.unop).symm.toLinearMap).map_smul r x)⟩
end Coordinates
end
end GroundTheory.Heights₂.Heights.Model


