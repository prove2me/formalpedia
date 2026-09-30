-- Prove2me | Definitions.Def_ChatterjeeSamuelson_UniformEfficiency_IsExample1Pair
-- name    : ChatterjeeSamuelson_UniformEfficiency_IsExample1Pair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T08:04:57.880438+00:00
-- url     : https://prove2.me/theorems/21576eb2-774d-4088-a1ab-5e0d0b3937d2
-- title:
--   Offer strategies of the shape of Example 1(a)
-- statement:
--   Let $k$ be the rule parameter and $\bar v$ the upper end of the value range. A seller strategy $S$ and a buyer strategy $B$ (functions from reservation prices to offers) **have the shape of Example 1(a)** if
--
--   1. $S(v_s) = \dfrac{v_s}{2-k} + \dfrac{1-k}{2}\bar v$ for $0 \le v_s \le \dfrac{2-k}{2}\bar v$;
--   2. $S(v_s) \ge \dfrac{v_s}{2-k} + \dfrac{1-k}{2}\bar v$ for $\dfrac{2-k}{2}\bar v < v_s \le \bar v$;
--   3. $B(v_b) \le \dfrac{v_b}{1+k} + \dfrac{k(1-k)}{2(1+k)}\bar v$ for $0 \le v_b < \dfrac{1-k}{2}\bar v$;
--   4. $B(v_b) = \dfrac{v_b}{1+k} + \dfrac{k(1-k)}{2(1+k)}\bar v$ for $\dfrac{1-k}{2}\bar v \le v_b \le \bar v$.
--
--   These are the equilibrium offer strategies that Chatterjee and Samuelson give in Example 1(a) for the sealed-offer rule with values uniform on $[0, \bar v]$. On the ranges of clauses 2 and 3 a seller asks so much, or a buyer bids so little, that no trade can occur, and the strategy there is free apart from the bound.
--
--   **Formalization Note** The predicate records the shape only; it does not assert that the pair is an equilibrium, and the results about trade probability and profits in Example 1(b)–(c) use only this shape. Values outside $[0,\bar v]$ are unconstrained. No measurability of $S$ or $B$ is required.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), DOI 10.1287/opre.31.5.835, p. 842 [PDF 8], Example 1(a)

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerLinear
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerLinear

namespace ChatterjeeSamuelson.UniformEfficiency

/-- The offer strategies of Example 1(a) (Chatterjee & Samuelson, *Bargaining under Incomplete
Information*, Oper. Res. 31(5) 1983, §3, Example 1(a), p. 842 [PDF 8]):

* `S(v_s) = v_s/(2 − k) + ((1 − k)/2)v̄` for `0 ≤ v_s ≤ ((2 − k)/2)v̄`;
* `S(v_s) ≥ v_s/(2 − k) + ((1 − k)/2)v̄` for `((2 − k)/2)v̄ < v_s ≤ v̄`;
* `B(v_b) ≤ v_b/(1 + k) + (k(1 − k)/2(1 + k))v̄` for `0 ≤ v_b < ((1 − k)/2)v̄`;
* `B(v_b) = v_b/(1 + k) + (k(1 − k)/2(1 + k))v̄` for `((1 − k)/2)v̄ ≤ v_b ≤ v̄`.

`IsExample1Pair k v̄ S B` holds when the seller strategy `S` and the buyer strategy `B` satisfy
exactly these four clauses. On the no-trade ranges (a high-value seller, a low-value buyer)
the strategy is any function obeying the bound; outside `[0, v̄]` it is unconstrained.

*Formalization Note.* This records only the shape of the strategies; it does not assert that
they form an equilibrium (that is Example 1(a) itself, a separate mission). The parameters
`0 ≤ k ≤ 1` and `0 < v̄` are hypotheses of each theorem, not part of this predicate. No
measurability of `S` or `B` is required. -/
def IsExample1Pair (k vbar : ℝ) (S B : ℝ → ℝ) : Prop :=
  (∀ v, 0 ≤ v → v ≤ (2 - k) / 2 * vbar → S v = Shared.sellerLinear k vbar v) ∧
  (∀ v, (2 - k) / 2 * vbar < v → v ≤ vbar → Shared.sellerLinear k vbar v ≤ S v) ∧
  (∀ v, 0 ≤ v → v < (1 - k) / 2 * vbar → B v ≤ Shared.buyerLinear k vbar v) ∧
  (∀ v, (1 - k) / 2 * vbar ≤ v → v ≤ vbar → B v = Shared.buyerLinear k vbar v)

end ChatterjeeSamuelson.UniformEfficiency


