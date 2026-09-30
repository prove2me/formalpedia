-- Prove2me | Definitions.Def_ChatterjeeSamuelson_Shared_buyerLinear
-- name    : ChatterjeeSamuelson_Shared_buyerLinear
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:06:23.349018+00:00
-- url     : https://prove2.me/theorems/4304ce21-9f98-41bf-b01f-54356dc1e50b
-- title:
--   The buyer's linear offer rule $v_b/(1+k) + (k(1-k)/(2(1+k)))\bar v$
-- statement:
--   For $0 \le k \le 1$ and $\bar v > 0$, the **linear buyer rule** of Example 1(a) is the affine map
--
--   $$
--   B_{\mathrm{lin}}(v) = \frac{v}{1+k} + \frac{k(1-k)}{2(1+k)}\,\bar v .
--   $$
--
--   In the equilibrium of Example 1(a) the buyer offers $B_{\mathrm{lin}}(v_b)$ whenever $\frac{1-k}{2}\bar v \le v_b \le \bar v$, and at most $B_{\mathrm{lin}}(v_b)$ below that. At $v_b = \frac{1-k}{2}\bar v$ it equals $\frac{1-k}{2}\bar v$, the seller's lowest serious ask, and at $v_b = \bar v$ it equals $\frac{2-k}{2}\bar v$, the seller's ask at value $\frac{2-k}{2}\bar v$.
--
--   This definition is shared by two missions of this series: 2 (the linear equilibrium of the uniform example, Example 1(a), p. 842 [PDF 8], and the check against equations (3a), (3b), pp. 842–843 [PDF 8–9]) and 3 (trade probability and ex ante profits of the uniform example, Example 1(b) and 1(c), p. 842 [PDF 8], with p. 843 [PDF 9]).
--
--   **Formalization Note** The paper prints the coefficient inline as $(k(1-k)/2(1+k))\bar v$; it is read as $\frac{k(1-k)}{2(1+k)}\bar v$, the only reading under which the two boundary values above hold (and they are the geometry shown in the paper's Figure 1). Only the formula is defined, for every real $v$.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), https://doi.org/10.1287/opre.31.5.835, p. 842 [PDF 8], Example 1(a), fourth line

import Mathlib

namespace ChatterjeeSamuelson.Shared

/-- The buyer's linear offer rule of Example 1(a) (Chatterjee & Samuelson, *Bargaining
under Incomplete Information*, Oper. Res. 31(5) 1983, §3, Example 1(a), p. 842 [PDF 8]:
"B(v_b) = v_b/(1 + k) + (k(1 − k)/2(1 + k))v̄").

`buyerLinear k v̄ v = v / (1 + k) + (k (1 − k) / (2 (1 + k))) · v̄`, for all real `v`.

*Formalization Note.* The printed coefficient `k(1 − k)/2(1 + k)` is read as
`k(1 − k) / (2(1 + k))`: with this reading the buyer with value `((1 − k)/2)v̄` offers
exactly `((1 − k)/2)v̄` (the seller's lowest offer, `sellerLinear k v̄ 0`) and the buyer with
value `v̄` offers `((2 − k)/2)v̄` (the seller's offer at value `((2 − k)/2)v̄`), which is the
geometry the paper describes (p. 843, Figure 1). For `0 ≤ k ≤ 1` the divisor `1 + k` lies in
`[1, 2]`. -/
noncomputable def buyerLinear (k vbar v : ℝ) : ℝ :=
  v / (1 + k) + k * (1 - k) / (2 * (1 + k)) * vbar

end ChatterjeeSamuelson.Shared


