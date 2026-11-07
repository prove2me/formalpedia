-- Prove2me | Definitions.Def_FreeSpencer_Admissible
-- name    : FreeSpencer_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:04.614091+00:00
-- url     : https://prove2.me/theorems/64f664d7-a18e-4f41-a070-088a60457c97
-- title:
--   Programs of the arithmetic model (Definition B.1)
-- statement:
--   A program of the published real RAM `MatMulTimeLP.RealRAM` is admissible when every real literal in it is rational and it contains no Gaussian draw. Admissible programs use exactly the operations of the paper's arithmetic model without its eigendecomposition primitive: scalar real arithmetic, comparisons, nonnegative square roots and uniform draws, each at unit cost, plus index arithmetic and array access.
--
--   **Formalization Note** Under an existential quantifier over programs, an arbitrary real literal could hold unbounded advice, read out by doubling and comparing, and a Gaussian draw is not an operation of the model. The restriction falls on the program only.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Definition B.1, p.74; Appendix F, p.90

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM

namespace FreeSpencer

/-- An instruction of the published real RAM is admissible when it is an operation of the paper's
model: a real literal must be rational, and `gauss` is not allowed.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Definition B.1, p.74. -/
def InstrAdmissible : MatMulTimeLP.Instr → Prop
  | MatMulTimeLP.Instr.rconst _ c => ∃ q : ℚ, c = (q : ℝ)
  | MatMulTimeLP.Instr.gauss _ => False
  | _ => True

/-- The restriction of the published `MatMulTimeLP.RealRAM` to the arithmetic model of Definition B.1
without its eigendecomposition primitive (Appendix F, p.90): scalar real arithmetic, comparisons,
nonnegative square roots, uniform draws.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Definition B.1, p.74; Appendix F, p.90.

**Formalization Note** The published machine allows any real `rconst` and a Gaussian draw. Under
`∃ program` both would weaken the goal: a real literal can hold unbounded advice, read out by
doubling and comparing, and a Gaussian draw is not an operation of Definition B.1. This restricts
the existentially chosen program only, so nothing is added to the input. -/
def Admissible (P : MatMulTimeLP.Program) : Prop :=
  ∀ i ∈ P, InstrAdmissible i

end FreeSpencer


