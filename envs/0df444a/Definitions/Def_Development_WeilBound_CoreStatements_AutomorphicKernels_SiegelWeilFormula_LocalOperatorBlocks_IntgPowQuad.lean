-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:24.458843+00:00
-- url     : https://prove2.me/theorems/c6f4f060-f892-4780-91e6-068a617f4c05
-- title:
--   Intg Pow Quad
-- statement:
--   Definitions and structural lemmas for Intg Pow Quad, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/IntgPowQuad.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
namespace PositivityTheory.SiegelWeilFormula.KLI
def pk (b : ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.C (-(2 * b)⁻¹) * Polynomial.X
  | (k + 2) => Polynomial.C (-(2 * b)⁻¹) * (Polynomial.X * pk b (k + 1) + Polynomial.C ((k + 1 : ℕ) : ℂ) * pk b k)
def J (b : ℂ) (k : ℕ) (c : ℂ) : ℂ := ∫ x : ℝ, (x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)
end PositivityTheory.SiegelWeilFormula.KLI
end


