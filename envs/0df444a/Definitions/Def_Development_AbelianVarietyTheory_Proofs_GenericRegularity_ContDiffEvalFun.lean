-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContDiffEvalFun
-- name    : Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContDiffEvalFun
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:11:01.37259+00:00
-- url     : https://prove2.me/theorems/520c03f2-a8da-4384-a374-e0b267b7a922
-- title:
--   Cont Diff Eval Fun
-- statement:
--   Definitions and structural lemmas for Cont Diff Eval Fun, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContDiffEvalFun.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.SmoothPolynomialEvaluation
noncomputable def evalFun {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (v : (Fin d → ℂ) × ℂ) : ℂ :=
  Polynomial.eval v.2 (Polynomial.map (MvPolynomial.eval v.1) p)
end GlobalTheory.SmoothPolynomialEvaluation


