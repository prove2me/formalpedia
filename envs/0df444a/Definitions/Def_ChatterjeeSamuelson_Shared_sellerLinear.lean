-- Prove2me | Definitions.Def_ChatterjeeSamuelson_Shared_sellerLinear
-- name    : ChatterjeeSamuelson_Shared_sellerLinear
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:06:01.860662+00:00
-- url     : https://prove2.me/theorems/d8445d66-7ed0-4159-af09-497a22e362af
-- title:
--   The seller's linear offer rule $v_s/(2-k) + ((1-k)/2)\bar v$
-- statement:
--   For $0 \le k \le 1$ and $\bar v > 0$, the **linear seller rule** of Example 1(a) is the affine map
--
--   $$
--   S_{\mathrm{lin}}(v) = \frac{v}{2-k} + \frac{1-k}{2}\,\bar v .
--   $$
--
--   In the equilibrium of Example 1(a) the seller asks $S_{\mathrm{lin}}(v_s)$ whenever $0 \le v_s \le \frac{2-k}{2}\bar v$, and at least $S_{\mathrm{lin}}(v_s)$ above that. Its lowest value on $[0, \bar v]$, $S_{\mathrm{lin}}(0) = \frac{1-k}{2}\bar v$, is the lowest serious ask.
--
--   This definition is shared by two missions of this series: 2 (the linear equilibrium of the uniform example, Example 1(a), p. 842 [PDF 8], and the check against equations (3a), (3b), pp. 842–843 [PDF 8–9]) and 3 (trade probability and ex ante profits of the uniform example, Example 1(b) and 1(c), p. 842 [PDF 8], with p. 843 [PDF 9]).
--
--   **Formalization Note** Only the formula is defined, for every real $v$; where the equilibrium strategy equals it is a hypothesis of each theorem.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), https://doi.org/10.1287/opre.31.5.835, p. 842 [PDF 8], Example 1(a), first line

import Mathlib

namespace ChatterjeeSamuelson.Shared

/-- The seller's linear offer rule of Example 1(a) (Chatterjee & Samuelson, *Bargaining
under Incomplete Information*, Oper. Res. 31(5) 1983, §3, Example 1(a), p. 842 [PDF 8]:
"S(v_s) = v_s/(2 − k) + ((1 − k)/2)v̄").

`sellerLinear k v̄ v = v / (2 − k) + ((1 − k) / 2) · v̄`, for all real `v`.

*Formalization Note.* This is only the formula; on which values the equilibrium strategy
equals it (and on which it is merely bounded below by it) is part of each theorem's
hypotheses. For `0 ≤ k ≤ 1` the divisor `2 − k` lies in `[1, 2]`. -/
noncomputable def sellerLinear (k vbar v : ℝ) : ℝ :=
  v / (2 - k) + (1 - k) / 2 * vbar

end ChatterjeeSamuelson.Shared


