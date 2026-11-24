-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:18.575323+00:00
-- url     : https://prove2.me/theorems/e62a6ad4-c534-4e81-9d0f-74e4b7f0233c
-- title:
--   Eval Monomial2
-- statement:
--   Definitions and structural lemmas for Eval Monomial2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/EvalMonomial2.lean

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex MvPolynomial
namespace PositivityTheory.SiegelWeilFormula.KLI
def toMv {σ : Type} (i : σ) (p : Polynomial ℂ) : MvPolynomial σ ℂ :=
  ∑ j ∈ Finset.range (p.natDegree + 1), C (p.coeff j) * X i ^ j
def G2 (b l μ : ℂ) (p : ℝ × ℝ) : ℂ := cexp (b * (p.1 : ℂ) ^ 2 + l * p.1) * cexp (b * (p.2 : ℂ) ^ 2 + μ * p.2)
end PositivityTheory.SiegelWeilFormula.KLI
end


