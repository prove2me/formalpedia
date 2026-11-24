-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogNormEnergyDensNonneg
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogNormEnergyDensNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:41.312706+00:00
-- url     : https://prove2.me/theorems/c83c21f0-e9b6-4f8b-96dc-12a8d81f01a6
-- title:
--   St Log Norm Energy Dens Nonneg
-- statement:
--   Definitions and structural lemmas for St Log Norm Energy Dens Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLogNormEnergyDensNonneg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
def LogNormEnergyDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (h : HermNorm n) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ)
    (v : (Fin (d + 1) → ℂ) → ℝ), AnalyticAt ℂ s y → s y ≠ 0 →
      0 ≤ gradDens (fun _ : Fin d => (fun x => Real.log (h.dualNorm x)) ∘ s) v v y
end
end GroundTheory.Heights₂.Heights


