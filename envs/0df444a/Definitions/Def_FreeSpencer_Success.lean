-- Prove2me | Definitions.Def_FreeSpencer_Success
-- name    : FreeSpencer_Success
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:19.114404+00:00
-- url     : https://prove2.me/theorems/2c575f8c-4beb-4e43-8178-400e266152af
-- title:
--   The status cell and the output signs
-- statement:
--   A halted run reports a signing when the first output cell holds $1$; anything else is a report of failure. The following $n$ output cells hold the signs.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM

namespace FreeSpencer

/-- The status cell: the run halted at step `t` reports a signing when output cell `0` holds `1`;
anything else is "reports failure".
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 1.1, p.2. -/
def Success (P : MatMulTimeLP.Program) (input : List ℝ) (ω : MatMulTimeLP.Tape) (t n : ℕ) : Prop :=
  MatMulTimeLP.outputAt P input ω t (n + 1) 0 = 1

/-- The signs written by the machine: output cells `1, …, n`. -/
noncomputable def outSigns (P : MatMulTimeLP.Program) (input : List ℝ) (ω : MatMulTimeLP.Tape)
    (t n : ℕ) : Fin n → ℝ :=
  fun i => MatMulTimeLP.outputAt P input ω t (n + 1) i.succ

end FreeSpencer


