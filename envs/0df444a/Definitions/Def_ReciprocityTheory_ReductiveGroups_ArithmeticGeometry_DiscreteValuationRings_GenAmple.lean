-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:25.808927+00:00
-- url     : https://prove2.me/theorems/ac79446f-9d10-4a1e-b8a5-fe32e5f1e854
-- title:
--   Gen Ample
-- statement:
--   Definitions and structural lemmas for Gen Ample, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
section Flat
variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
lemma flat_le {K : Type} [Fintype K] (p : (K → L₁.ι) × (K → L₂.ι)) (k : K) :
    LB.wchart L₁ (fun _ : K => f₁) p.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) p.2 ≤
      (L₂.pull f₂).U (fun _ => p.2 k) ⊓ (L₁.pull f₁).U (fun _ => p.1 k) := by
  intro x hx
  simp only [LB.pull, LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_mk,
    Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hx ⊢
  exact ⟨fun _ => hx.2 k, fun _ => hx.1 k⟩
def flatIso (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) {K : Type} [Fintype K] (ε : K → ℤ) :
    LB.Iso (LB.LinComb L₂ (fun _ : K => f₂) ε) (LB.LinComb L₁ (fun _ : K => f₁) ε) :=
  ⟨fun p => ∏ k, res (flat_le L₁ L₂ f₁ f₂ p k) (w.s (fun _ => p.2 k, fun _ => p.1 k)) ^ (-ε k)⟩
end Flat
section NZ
variable {Y : Scheme.{0}}
end NZ
section Main
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
end Main
end ReciprocityTheory.ChartRestriction.G.DVR


