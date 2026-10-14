-- Prove2me | Definitions.Def_Shoppertainment_OptimalBandwidth_Model
-- name    : Shoppertainment_OptimalBandwidth_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:49:21.837984+00:00
-- url     : https://prove2.me/theorems/ae006aed-3f5a-4bf7-8de2-d8dce7c8f3b0
-- title:
--   §3–§4, pp. 13–31 — fit-signal prices pH, pL, demand (8), the manufacturer pricing rule, traffic T (13), profitability π (14) and streamer payoff Π = T·π
-- statement:
--   This file sets up the shoppertainment live-streaming model of Gu, Zhao and Wu (§3–§4).
--
--   A streamer sells, in each session, one product drawn at random from a pool of contracted manufacturers. A product's **quality** $q \in [0,1]$ is the probability that it fits a consumer; a good fit is worth $v > 0$, a bad fit $0$. Qualities are uniform on $[\underline q, 1]$, where $\underline q$ is the streamer's **quality threshold**. The streamer devotes a share $t_e \in [0,1]$ of the session's bandwidth to entertainment and $1 - t_e$ to product information, so that each attending consumer's fit signal has posterior fit probability $1 - t_e + t_e q$ after a good signal and $t_e q$ after a bad one. The following objects are defined.
--
--   1. The two willingness-to-pay levels (6)–(7):
--   $$p_H = (1 - t_e + t_e q)\,v, \qquad p_L = t_e q v.$$
--   2. The demand (8) when $T$ consumers attend: $D(p) = T$ if $p \le p_L$, $D(p) = qT$ if $p_L < p \le p_H$, and $D(p) = 0$ if $p > p_H$; and the manufacturer's profit $\pi_M = (1-\alpha)\,p\,D(p)$, where $\alpha$ is the streamer's commission rate.
--   3. The thresholds $\hat t_e = 1/(2 - \underline q)$ and $\hat q = 2 - 1/t_e$ of (9)–(10).
--   4. The equilibrium price of a manufacturer of quality $q$: $p_L$ if $t_e > 1/(2-q)$, and $p_H$ otherwise.
--   5. The proportion $\psi(t_e)$ of manufacturers that price low: the Lebesgue measure of $\{q \in [\underline q, 1] : 1/(2-q) < t_e\}$ divided by $1 - \underline q$.
--   6. The consumer's ex-ante surplus at price $p$, $q\max(p_H - p, 0) + (1-q)\max(p_L - p, 0)$ (a consumer buys iff the posterior utility (5) is nonnegative), and its average under the equilibrium prices,
--   $$Eu_p(t_e) = \frac{1}{1-\underline q}\int_{\underline q}^{1} \Big(q\max(p_H - p^*(q), 0) + (1-q)\max(p_L - p^*(q), 0)\Big)\,dq.$$
--   7. The attending traffic (13), $T(t_e) = (v_e t_e + Eu_p)/K$, where $v_e$ is the entertaining capability and attending costs are uniform on $[0, K]$.
--   8. The revenue per attending consumer $p \cdot D(p)/T$, the individual profitability $\pi(t_e) = \alpha \cdot \frac{1}{1-\underline q}\int_{\underline q}^1 p^*(q)\,D(p^*(q))/T\,dq$, and the streamer's payoff $\Pi = T\cdot \pi$.
--
--   Every later statement of the mission is about these objects; $Eu_p$ and $\pi$ are built from the manufacturers' pricing rule, so their closed forms (12) and (14) are theorems.
--
--   **Formalization Note** All parameters are real numbers and the functions are total; the standing ranges ($0 < \alpha < 1$, $v > 0$, $K > 0$, $0 \le \underline q < 1$, $t_e \in [0,1]$) are hypotheses of the theorems. The demand (8) is extended by $0$ above $p_H$, where (8) is silent. The pricing rule uses the manufacturer's own threshold $1/(2-q)$ (Online Supplementary A.2), not the printed $1/(2-\underline q)$ of (10); see Lemma 2. Ties $t_e = 1/(2-q)$ are priced high, as in (10). The uniform law $dF(q)$ is $dq/(1-\underline q)$ on $[\underline q, 1]$, so $\underline q < 1$ is needed for it to be a probability law.
-- source:
--   Gu, Zhao & Wu, A Model of Shoppertainment Live Streaming, accepted manuscript (Management Science, forthcoming, Oct. 2024), pp. 13–31, §3 and §4: (5) p. 20, (6)–(7) p. 22, (8) and π_M p. 23, (9)–(10) p. 24, (11) p. 25, (13) p. 27, Π = T·π p. 31

import Mathlib

namespace Shoppertainment.OptimalBandwidth

/-!
Gu, Zhao & Wu, *A Model of Shoppertainment Live Streaming*, accepted manuscript (Management
Science, forthcoming, Oct. 2024), §3 (pp. 13–21) and §4 (pp. 21–31).

Notation: `v` is the good-fit consumption value, `te ∈ [0, 1]` the entertainment bandwidth,
`q ∈ [0, 1]` a product's quality (its fit probability), `ql` the quality threshold q̲ (qualities
are uniform on `[ql, 1]`), `α` the commission rate, `ve` the entertaining capability and `K` the
range of the uniform attending cost `k ∼ U[0, K]`.
-/

/-- (6), p. 22: highest willingness to pay after a good fit signal, `pH = (1 − te + te q) v`. -/
noncomputable def pH (v te q : ℝ) : ℝ := (1 - te + te * q) * v

/-- (7), p. 22: highest willingness to pay after a bad fit signal, `pL = te q v`. -/
noncomputable def pL (v te q : ℝ) : ℝ := te * q * v

/-- (8), p. 23: demand at price `p` when `T` consumers attend: `T` if `p ≤ pL`, `q T` if
`pL < p ≤ pH`, and `0` above `pH` (no attending consumer's willingness to pay reaches `p`). -/
noncomputable def demand (v te q T p : ℝ) : ℝ :=
  if p ≤ pL v te q then T else if p ≤ pH v te q then q * T else 0

/-- p. 23: profit of a manufacturer of quality `q` charging `p`, `π_M = (1 − α) p D(p)`. -/
noncomputable def mfrProfit (α v te q T p : ℝ) : ℝ := (1 - α) * p * demand v te q T p

/-- (10), p. 24: the bandwidth threshold `t̂e = 1/(2 − q̲)`. -/
noncomputable def teHat (ql : ℝ) : ℝ := 1 / (2 - ql)

/-- (9), p. 24: the strategy-indifference quality `q̂ = 2 − 1/te`. -/
noncomputable def qHat (te : ℝ) : ℝ := 2 - 1 / te

/-- Lemma 2's equilibrium price of a manufacturer of quality `q` (with its own threshold
`1/(2 − q)`, as in Online Supplementary A.2): `pL` if `te > 1/(2 − q)`, otherwise `pH`
(ties priced high, as in (10)). -/
noncomputable def eqPrice (v te q : ℝ) : ℝ :=
  if 1 / (2 - q) < te then pL v te q else pH v te q

/-- Proposition 1, p. 25: the proportion of manufacturers (qualities uniform on `[q̲, 1]`) that
price low, i.e. the Lebesgue measure of `{q ∈ [q̲, 1] : 1/(2 − q) < te}` divided by `1 − q̲`. -/
noncomputable def psi (ql te : ℝ) : ℝ :=
  (MeasureTheory.volume {q : ℝ | q ∈ Set.Icc ql 1 ∧ 1 / (2 - q) < te}).toReal / (1 - ql)

/-- (5), p. 20: ex-ante expected surplus of an attending consumer facing price `p` for a product
of quality `q`: with probability `q` the signal is good and the consumer buys iff `pH − p ≥ 0`;
with probability `1 − q` it is bad and the consumer buys iff `pL − p ≥ 0`. -/
noncomputable def buyerSurplus (v te q p : ℝ) : ℝ :=
  q * max (pH v te q - p) 0 + (1 - q) * max (pL v te q - p) 0

/-- p. 26: the consumer's expected shopping surplus `Eu_p` under the equilibrium prices, with
`dF(q) = dq/(1 − q̲)` on `[q̲, 1]`. -/
noncomputable def Eup (v ql te : ℝ) : ℝ :=
  (1 / (1 - ql)) * ∫ q in ql..1, buyerSurplus v te q (eqPrice v te q)

/-- (13), p. 27: attending consumer traffic `T(te) = (ve te + Eu_p)/K`. -/
noncomputable def traffic (v ve K ql te : ℝ) : ℝ := (ve * te + Eup v ql te) / K

/-- p. 31: expected sales revenue per attending consumer at price `p`, i.e. `p · D(p)/T` by (8)
(extended by `0` above `pH`). -/
noncomputable def revenuePerConsumer (v te q p : ℝ) : ℝ :=
  p * (if p ≤ pL v te q then 1 else if p ≤ pH v te q then q else 0)

/-- p. 31: individual profitability `π(te)`, the streamer's expected commission from one
attending consumer under the equilibrium prices, with `dF(q) = dq/(1 − q̲)`. -/
noncomputable def profitability (α v ql te : ℝ) : ℝ :=
  α * ((1 / (1 - ql)) * ∫ q in ql..1, revenuePerConsumer v te q (eqPrice v te q))

/-- p. 31: the streamer's total payoff `Π = T · π`. -/
noncomputable def payoff (α v ve K ql te : ℝ) : ℝ :=
  traffic v ve K ql te * profitability α v ql te

end Shoppertainment.OptimalBandwidth


