-- Prove2me | Definitions.Def_BlumRivest_Training_Thresholds
-- name    : BlumRivest_Training_Thresholds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:40:39.158385+00:00
-- url     : https://prove2.me/theorems/0c995e78-3700-4ab7-9f4a-a89bf4599d9d
-- title:
--   Section 2 — real linear threshold nodes with strict positive output
-- statement:
--   A linear threshold node on $n$ real inputs consists of a real weight vector $w$ and a real threshold $t$. It outputs the positive label exactly when
--
--   $$t<\sum_{i=0}^{n-1} w_i x_i.$$
--
--   The negative label is returned otherwise, including equality. All weights and thresholds are unrestricted real numbers. Boolean coordinates are interpreted as 0 and 1 by `bitValue`; Boolean labels and node outputs are interpreted as −1 and +1 by `signValue`, with `true` positive. These are distinct numerical interpretations. The empty sum is zero when $n=0$.
--
--   This reusable node definition supplies both layers of the three-node network and the two cuts in the positive-quadrant problem.
-- source:
--   Blum and Rivest (1992), Section 2, printed p. 119 (PDF p. 3), DOI 10.1016/S0893-6080(05)80010-3.

import Mathlib

namespace BlumRivest.Training

/-- Numerical value of a Boolean input coordinate. -/
def bitValue (b : Bool) : ℝ := if b then 1 else 0

/-- Numerical value of a node output or a training label. -/
def signValue (b : Bool) : ℝ := if b then 1 else -1

/-- A linear threshold node on `n` real inputs, with unrestricted real parameters. -/
structure Threshold (n : ℕ) where
  weight : Fin n → ℝ
  threshold : ℝ

/-- The positive output is strict; equality gives the negative output. -/
noncomputable def Threshold.eval {n : ℕ} (p : Threshold n) (x : Fin n → ℝ) : Bool :=
  decide (p.threshold < ∑ i, p.weight i * x i)

end BlumRivest.Training


