-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexTaylor
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexTaylor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:35.108598+00:00
-- url     : https://prove2.me/theorems/9a968ea6-4f5f-4074-9166-ecad288679bd
-- title:
--   Statements Complex Taylor
-- statement:
--   Definitions and structural lemmas for Statements Complex Taylor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsComplexTaylor.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix
noncomputable section
def ComplexTaylorTwo.Statement : Prop :=
  ∀ (D : ℕ) (ψ : (Fin D → ℂ) → ℝ) (y₀ : Fin D → ℂ), ContDiffAt ℝ 2 ψ y₀ →
    ∃ (a : Fin D → ℂ) (b : Matrix (Fin D) (Fin D) ℂ),
      (fun z : Fin D → ℂ => ψ (y₀ + z) - ψ y₀ - (a ⬝ᵥ z + z ⬝ᵥ (b *ᵥ z)).re -
          (z ⬝ᵥ (hessC ψ y₀ *ᵥ star z)).re) =o[𝓝 0] fun z => ‖z‖ ^ 2
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


