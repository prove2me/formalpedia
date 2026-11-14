-- Prove2me | Definitions.Def_NarrowDNF_FiberShift
-- name    : NarrowDNF_FiberShift
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:58:57.959555+00:00
-- url     : https://prove2.me/theorems/30c448ac-7250-490f-a814-82910713af2f
-- title:
--   Two-point Boolean fibers and bias-matched shift error
-- statement:
--   A Boolean fiber is an ordered pair $(v_0,v_1)$, giving a function's values when one coordinate is zero and one. For Boolean values $a,b$, let $\delta(a,b)$ be zero when they agree and one when they differ. Given target fiber $f$, approximation fiber $v$, and bias $p$, the conditional disagreement error is
--   $$E_p(f,v)=(1-p)\delta(f_0,v_0)+p\delta(f_1,v_1).$$
--   For $0\le p\le1$ this is the error under a Bernoulli-$p$ input on the fiber.
--
--   The upper shift sends $v$ to $(v_0,v_0\lor v_1)$, and the lower shift sends it to $(v_0\land v_1,v_1)$. Thus the decreasing fiber $(1,0)$ becomes $(1,1)$ under the upper choice and $(0,0)$ under the lower choice. These explicit two-point quantities underlie the later randomized calculation that chooses the upper shift with probability $1-p$ and the lower shift with probability $p$. Passing from a fiber calculation to a full cube is a separate finite-sum argument.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/FiberShift.lean#L30-L31
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/FiberShift.lean#L33-L34
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/FiberShift.lean#L20-L21
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/FiberShift.lean#L23-L24
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/FiberShift.lean#L26-L28

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift


/-!
# Bias-matched shifts on a Boolean fiber

This file proves the two-point calculation used in Lemma 3.1 of
the 2026-11-06 STOC revision. The probability of the upper shift is `1 - p` and the
probability of the lower shift is `p`; the input fiber has the same bias `p`.

The error theorem is a conditional, single-fiber statement. Passing to an
arbitrary Boolean cube requires a separate summation/integration argument.
-/

namespace NarrowDNF.FiberShift



/-- Values at the lower and upper endpoints of one coordinate fiber. -/
abbrev Fiber := Bool × Bool

/-- The real-valued indicator that two Boolean values disagree. -/
def mismatch (a b : Bool) : ℝ := if a = b then 0 else 1

/-- Conditional error on one fiber under a `p`-biased input. -/
def error (p : ℝ) (f v : Fiber) : ℝ :=
  (1 - p) * mismatch f.1 v.1 + p * mismatch f.2 v.2

/-- The upper shift changes the decreasing fiber `10` to `11`. -/
def upper (v : Fiber) : Fiber := (v.1, v.1 || v.2)

/-- The lower shift changes the decreasing fiber `10` to `00`. -/
def lower (v : Fiber) : Fiber := (v.1 && v.2, v.2)

















end NarrowDNF.FiberShift


