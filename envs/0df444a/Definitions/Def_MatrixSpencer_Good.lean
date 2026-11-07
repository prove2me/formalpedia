-- Prove2me | Definitions.Def_MatrixSpencer_Good
-- name    : MatrixSpencer_Good
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:02.428499+00:00
-- url     : https://prove2.me/theorems/45cf9fff-8b76-4473-91fd-e75194913203
-- title:
--   A coloring within the discrepancy bound
-- statement:
--   For a constant $C$, an instance $I$ and a list of bits $m$: the list has $n$ bits, and with $x_i=+1$ for the bit true and $x_i=-1$ for the bit false,
--   $$\Bigl\|\sum_{i=1}^n x_iA_i\Bigr\|\le C\sqrt n\,\sqrt{\max\{1,\log(d/n)\}},$$
--   in the operator norm.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 1.3, p.1

import Mathlib
import Definitions.Def_MatrixSpencer_MatInst
open scoped Matrix.Norms.L2Operator

namespace MatrixSpencer

/-- **The sign of a bit**: `true ↦ 1`, `false ↦ −1`. -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

/-- **A good output: a coloring of discrepancy at most `C√n·√max{1, log(d/n)}`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 1.3, p.1.

The output has one bit per matrix, and the signed sum has the printed bound, in the operator norm. -/
def Good (C : ℝ) (I : MatInst) (m : List Bool) : Prop :=
  m.length = I.n ∧
    ‖∑ i : Fin I.n, signOf (m.getD i false) • (I.A i).map (fun q : ℚ => (q : ℝ))‖ ≤
      C * √(I.n : ℝ) * √(max 1 (Real.log ((I.d : ℝ) / I.n)))

end MatrixSpencer


