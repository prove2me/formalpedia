-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjDeg
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:43:24.732454+00:00
-- url     : https://prove2.me/theorems/b3e85416-a77e-5ee1-a3af-93bc7fe61b71
-- title:
--   Proj Deg
-- statement:
--   Definitions and structural lemmas for Proj Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjDeg.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
section Relabel
variable {K K' : Type} {ι : K → Type} {ι' : K' → Type} {κ : K → K'}
  {v : (Σ k, ι k) → (Σ k', ι' k')}
def blockVar (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) (p : Σ k, ι k) : Σ k, ι' (κ k) :=
  ⟨p.1, cast (congrArg ι' (hb.2.2.1 p)) (v p).2⟩
theorem blockIncl_blockVar (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    blockIncl ⟨κ, hb.1⟩ ι' (blockVar hb p) = v p := by
  refine Sigma.ext (hb.2.2.1 p).symm ?_
  exact (cast_heq _ _)
def blockVarEquiv (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) : (Σ k, ι k) ≃ (Σ k, ι' (κ k)) :=
  Equiv.ofBijective (blockVar hb) (by
    have hI : Function.Injective (blockIncl ⟨κ, hb.1⟩ ι') := by
      rintro ⟨a, x⟩ ⟨b, y⟩ h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      cases hb.1 h1
      cases eq_of_heq h2
      rfl
    refine ⟨fun p q h => hb.2.1 ?_, fun ⟨k, a⟩ => ?_⟩
    · rw [← blockIncl_blockVar hb p, ← blockIncl_blockVar hb q, h]
    · obtain ⟨p, hp⟩ := hb.2.2.2 ⟨κ k, a⟩ ⟨k, rfl⟩
      exact ⟨p, hI ((blockIncl_blockVar hb p).trans hp)⟩)
end Relabel
end
end GroundTheory.Heights₂.Heights.Targets


