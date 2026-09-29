-- Prove2me | Definitions.Def_ChatterjeeSamuelson_Shared_sellerProfit
-- name    : ChatterjeeSamuelson_Shared_sellerProfit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:44:47.628933+00:00
-- url     : https://prove2.me/theorems/7057317e-a604-436a-8811-12246cd66dcf
-- title:
--   The seller's expected profit $\pi_s(s, v_s)$
-- statement:
--   Under the Bargaining Rule (trade iff $b \ge s$, at price $P = kb + (1-k)s$ with $0 \le k \le 1$), let the buyer use the offer strategy $B$ and let the seller's belief about the buyer's value $v_b$ be the probability measure $\mu_s$. The expected profit of a seller with reservation price $v$ who asks $s$ is
--
--   $$
--   \pi_s(s, v) = \int \mathbf 1\{s \le B(v_b)\}\,\bigl(k B(v_b) + (1-k)s - v\bigr)\,d\mu_s(v_b).
--   $$
--
--   This is the paper's $\pi_s(s, v_s) = \int_s^{\hat b} (P - v_s)\, g_s(b)\,db$ for $s \le \hat b$ and $0$ for $s > \hat b$, where $g_s$ is the density of buyer offers.
--
--   This definition is shared by two missions of this series: 1 (the linked differential equations, Theorem 2 and its proof, p. 840 [PDF 6]) and 2 (the linear equilibrium of the uniform example, Example 1(a), p. 842 [PDF 8]).
--
--   **Formalization Note** The expectation is over the buyer's value rather than against the offer density $g_s$; the two agree whenever $g_s$ exists. Ties trade.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), p. 839 [PDF 5], unnumbered display for π_s(s, v_s)

import Mathlib

open MeasureTheory

namespace ChatterjeeSamuelson.Shared

/-- The seller's expected profit (Chatterjee & Samuelson, *Bargaining under Incomplete
Information*, Oper. Res. 31(5) 1983, §1, p. 839 [PDF 5], unnumbered display
`π_s(s, v_s) = ∫_s^{b̂} (P − v_s) g_s(b) db` if `s ≤ b̂`, `= 0` if `s > b̂`), under the
Bargaining Rule of p. 838: trade iff `b ≥ s`, at price `P = k b + (1 − k) s`.

`sellerProfit k μs B s v` is the expected profit of a seller with reservation price `v`
who asks `s` against a buyer using the offer strategy `B`, when the seller's belief
about the buyer's value `v_b` is `μs`:
`∫ (if s ≤ B v_b then k B v_b + (1 − k) s − v else 0) dμs(v_b)`.

*Formalization Note.* Written against the distribution of the buyer's value instead of
the density `g_s` of buyer offers; the two agree whenever `g_s` exists. Ties trade. -/
noncomputable def sellerProfit (k : ℝ) (μs : Measure ℝ) (B : ℝ → ℝ) (s v : ℝ) : ℝ :=
  ∫ vb, (if s ≤ B vb then k * B vb + (1 - k) * s - v else 0) ∂μs

end ChatterjeeSamuelson.Shared


