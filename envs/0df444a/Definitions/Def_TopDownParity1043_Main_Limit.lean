-- Prove2me | Definitions.Def_TopDownParity1043_Main_Limit
-- name    : TopDownParity1043_Main_Limit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:19:13.964853+00:00
-- url     : https://prove2.me/theorems/f8a95256-ce40-4965-b971-0df8baf8c71e
-- title:
--   Definition 2 — quantitative limit points of a set
-- statement:
--   For a finite coordinate set $V$, $p\in[0,1]$, real $k$, a set $Y\subseteq\{0,1\}^V$ and a word $x$, the quantitative limit condition is
--   $$\Pr_{P\subseteq_p V}\bigl[|[x]_P\cap Y|\ge2^{|P|-k}\bigr]\ge\frac34.$$
--
--   The rectangle $X\times Y$ satisfies the left condition if every $x\in X$ satisfies this condition for $Y$, and the right condition if every $y\in Y$ satisfies it for $X$.
--
--   This is the invariant's set-theoretic interface. The exponent is real, so $k$ need not be an integer, and the threshold is inclusive. No monotonicity in the bias is assumed.
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Definition 2, p. 10

import Mathlib
import Definitions.Def_TopDownParity1043_Main_RandomSets
import Definitions.Def_TopDownParity1043_Main_Subcubes

set_option autoImplicit false

namespace TopDownParity1043.Main

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Definition 2, p.10: at least 3/4 probability of a fibre with at least 2^(|P|-k)
points. The count threshold uses a real exponent, even for nonintegral k. -/
noncomputable def IsPKLimit (p : Bias) (k : ℝ) (Y : Finset (V → Bool))
    (x : V → Bool) : Prop :=
  (3 : ℝ) / 4 ≤ setProb p (fun P =>
    (2 : ℝ) ^ ((P.card : ℝ) - k) ≤ ((fibre Y x P).card : ℝ))

noncomputable def LeftLimit (p : Bias) (k : ℝ) (X Y : Finset (V → Bool)) : Prop :=
  ∀ x ∈ X, IsPKLimit p k Y x

noncomputable def RightLimit (p : Bias) (k : ℝ) (X Y : Finset (V → Bool)) : Prop :=
  ∀ y ∈ Y, IsPKLimit p k X y

end TopDownParity1043.Main


