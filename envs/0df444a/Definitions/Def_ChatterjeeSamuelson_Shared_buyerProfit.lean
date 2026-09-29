-- Prove2me | Definitions.Def_ChatterjeeSamuelson_Shared_buyerProfit
-- name    : ChatterjeeSamuelson_Shared_buyerProfit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:44:25.905414+00:00
-- url     : https://prove2.me/theorems/ab7b915f-2e1b-4644-96e3-b86463697f8b
-- title:
--   The buyer's expected profit $\pi_b(b, v_b)$
-- statement:
--   Under the sealed-offer **Bargaining Rule**, the seller and buyer submit offers $s$ and $b$; if $b \ge s$ the good is sold at price $P = kb + (1-k)s$, where $0 \le k \le 1$, and otherwise there is no trade and both earn zero.
--
--   Let the seller use the offer strategy $S$ (a seller with value $v_s$ offers $S(v_s)$), and let the buyer's belief about $v_s$ be the probability measure $\mu_b$. The expected profit of a buyer with reservation price $v$ who offers $b$ is
--
--   $$
--   \pi_b(b, v) = \int \mathbf 1\{S(v_s) \le b\}\,\bigl(v - k b - (1-k) S(v_s)\bigr)\,d\mu_b(v_s).
--   $$
--
--   This is equation (1) of the paper, $\pi_b(b, v_b) = \int_{\underline s}^{b} (v_b - P)\, g_b(s)\,ds$ for $b \ge \underline s$ and $0$ otherwise, where $g_b$ is the density of seller offers induced by $S$ and $F_b$.
--
--   This definition is shared by two missions of this series: 1 (the linked differential equations, Theorem 2 and its proof, p. 840 [PDF 6]) and 2 (the linear equilibrium of the uniform example, Example 1(a), p. 842 [PDF 8]).
--
--   **Formalization Note** The expectation is taken over the seller's value rather than against the offer density $g_b$; the two agree whenever $g_b$ exists, and this form needs no density. Ties $b = s$ trade.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), p. 838 [PDF 4], Bargaining Rule and equation (1)

import Mathlib

open MeasureTheory

namespace ChatterjeeSamuelson.Shared

/-- The buyer's expected profit (Chatterjee & Samuelson, *Bargaining under Incomplete
Information*, Oper. Res. 31(5) 1983, §1, p. 838 [PDF 4], equation (1)), under the
Bargaining Rule of p. 838: offers `s` and `b` trade iff `b ≥ s`, at price
`P = k b + (1 − k) s`.

`buyerProfit k μb S b v` is the expected profit of a buyer with reservation price `v`
who offers `b` against a seller using the offer strategy `S`, when the buyer's belief
about the seller's value `v_s` is `μb`:
`∫ (if S v_s ≤ b then v − (k b + (1 − k) S v_s) else 0) dμb(v_s)`.

*Formalization Note.* The paper writes (1) as `∫_{s̲}^{b} (v_b − P) g_b(s) ds` (and `0` if
`b < s̲`) against the density `g_b` of seller offers induced by `S` and `F_b`. Here the
same expectation is written against the distribution of the seller's value; the two
agree whenever `g_b` exists, and this form needs no density. Ties (`b = s`) trade. -/
noncomputable def buyerProfit (k : ℝ) (μb : Measure ℝ) (S : ℝ → ℝ) (b v : ℝ) : ℝ :=
  ∫ vs, (if S vs ≤ b then v - (k * b + (1 - k) * S vs) else 0) ∂μb

end ChatterjeeSamuelson.Shared


