-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyGermPointPow
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyGermPointPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:47.017414+00:00
-- url     : https://prove2.me/theorems/aac5b5ae-d2e7-4f71-add2-5925980c517e
-- title:
--   PPoly Germ Point Pow
-- statement:
--   Definitions and structural lemmas for PPoly Germ Point Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolyGermPointPow.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter Asymptotics
noncomputable section
namespace PolyGermPointPow
variable {σ : Type} [Fintype σ] (w : σ → ℂ)
def bigOIdeal (k : ℕ) : Ideal (holGerms w) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, (f : Germ (𝓝 w) ℂ) = (φ : Germ (𝓝 w) ℂ) ∧
    f =O[𝓝 w] fun z => ‖z - w‖ ^ k}
  add_mem' := by
    rintro φ ψ ⟨f, hf, hfO⟩ ⟨g, hg, hgO⟩
    exact ⟨f + g, by rw [Subring.coe_add, ← hf, ← hg]; rfl, hfO.add hgO⟩
  zero_mem' := ⟨0, rfl, isBigO_zero _ _⟩
  smul_mem' := by
    rintro c φ ⟨f, hf, hfO⟩
    obtain ⟨a, ha, hac⟩ := c.2
    refine ⟨a * f, ?_, ?_⟩
    · rw [smul_eq_mul, Subring.coe_mul, ← hf, ← hac]; rfl
    · show (fun z => a z * f z) =O[𝓝 w] fun z => ‖z - w‖ ^ k
      simpa using (ha.continuousAt.tendsto.isBigO_one ℝ).mul hfO
end PolyGermPointPow
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


