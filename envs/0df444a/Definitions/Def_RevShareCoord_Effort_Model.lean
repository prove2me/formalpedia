-- Prove2me | Definitions.Def_RevShareCoord_Effort_Model
-- name    : RevShareCoord_Effort_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:40:38.109974+00:00
-- url     : https://prove2.me/theorems/f371c76b-1f60-4292-955a-6bf8598e17de
-- title:
--   Sec. 4.2.1 — the model with retailer effort: revenue R(q, e), effort cost g(e), unit cost c, and the profits Π, π_r, π_s
-- statement:
--   **The model with retailer effort.** A supplier sells to one retailer. After observing the supplier's revenue-sharing contract $\{\phi, w\}$ the retailer chooses an order quantity $q \ge 0$ and an effort level $e \ge 0$. Effort is not contractible. The retailer's expected revenue is $R(q, e)$, the retailer incurs the effort cost $g(e)$, and the supplier produces each unit at cost $c > 0$. The standing assumptions are:
--
--   1. $R$ is continuous and differentiable, with partial derivatives $\partial R/\partial q$ and $\partial R/\partial e$;
--   2. $R$ is strictly increasing in $e$ and concave in $q$;
--   3. $g$ is continuous, increasing, differentiable (derivative $g'$) and convex, with $g(0) = 0$.
--
--   Under the contract $\{\phi, w\}$ the retailer keeps the share $\phi$ of revenue and pays $w$ per unit. The integrated channel's, the retailer's and the supplier's profits are
--
--   $$
--   \Pi(q, e) = R(q, e) - g(e) - qc, \qquad \pi_r(q, e) = \phi R(q, e) - g(e) - qw, \qquad \pi_s(q, e) = (1-\phi) R(q, e) + q(w - c).
--   $$
--
--   These objects are used by the two general statements of the mission: under revenue sharing the retailer under-invests in effort, and only the wholesale-price contract at marginal cost coordinates the channel.
--
--   **Formalization Note.** $R$, $g$ and their derivatives are real functions constrained only on $q, e \ge 0$. Differentiability is encoded by one-sided (within $[0,\infty)$) partial derivatives `Rq`, `Re` and a derivative `g'`, together with joint continuity of $R$ on the quadrant; joint (Fréchet) differentiability is not assumed, since only the partial derivatives enter the paper's argument. The effort domain $e \ge 0$ is implicit on the page. $c > 0$ is the standing assumption of Sec. 1 (p. 5). The paper does not display $\pi_s$ in the general model; it is read off the sequence of events of Sec. 1.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 21 (PDF p. 22), Section 4.2.1 (model paragraph and display of Π(q, e)); p. 22 (PDF p. 23), display of π_r(q, e); p. 5 (PDF p. 6), Section 1 (c > 0, sequence of events)

import Mathlib

namespace RevShareCoord.Effort

/-- The model with retailer effort of Sec. 4.2.1 (Cachon–Lariviere, June 2000 working paper,
pp. 21–22). The retailer chooses an order quantity `q ≥ 0` and an effort level `e ≥ 0`.
`R q e` is expected revenue, `Rq q e` and `Re q e` its partial derivatives in `q` and in `e`
(one-sided at the boundary of `[0, ∞)`), `g e` the retailer's effort cost with derivative `g'`,
and `c` the supplier's unit production cost. -/
structure Model where
  /-- Expected revenue `R(q, e)`. -/
  R : ℝ → ℝ → ℝ
  /-- Partial derivative `∂R/∂q`. -/
  Rq : ℝ → ℝ → ℝ
  /-- Partial derivative `∂R/∂e`. -/
  Re : ℝ → ℝ → ℝ
  /-- Effort cost `g(e)`. -/
  g : ℝ → ℝ
  /-- Derivative `g'(e)`. -/
  g' : ℝ → ℝ
  /-- Supplier's unit production cost `c`. -/
  c : ℝ
  /-- `c > 0` (Sec. 1, p. 5). -/
  c_pos : 0 < c
  /-- `R` is continuous on `q, e ≥ 0`. -/
  R_cont : ContinuousOn (fun x : ℝ × ℝ => R x.1 x.2) (Set.Ici 0 ×ˢ Set.Ici 0)
  /-- `R` is differentiable in `q`, with partial derivative `Rq` (one-sided at `q = 0`). -/
  hasDeriv_q : ∀ q e : ℝ, 0 ≤ q → 0 ≤ e →
    HasDerivWithinAt (fun q' => R q' e) (Rq q e) (Set.Ici 0) q
  /-- `R` is differentiable in `e`, with partial derivative `Re` (one-sided at `e = 0`). -/
  hasDeriv_e : ∀ q e : ℝ, 0 ≤ q → 0 ≤ e →
    HasDerivWithinAt (fun e' => R q e') (Re q e) (Set.Ici 0) e
  /-- `R` is strictly increasing in `e`. -/
  strictMono_e : ∀ q : ℝ, 0 ≤ q → StrictMonoOn (fun e => R q e) (Set.Ici 0)
  /-- `R` is concave in `q`. -/
  concave_q : ∀ e : ℝ, 0 ≤ e → ConcaveOn ℝ (Set.Ici 0) (fun q => R q e)
  /-- `g` is continuous. -/
  g_cont : ContinuousOn g (Set.Ici 0)
  /-- `g` is increasing. -/
  g_mono : MonotoneOn g (Set.Ici 0)
  /-- `g` is differentiable, with derivative `g'` (one-sided at `0`). -/
  hasDeriv_g : ∀ e : ℝ, 0 ≤ e → HasDerivWithinAt g (g' e) (Set.Ici 0) e
  /-- `g` is convex. -/
  g_convex : ConvexOn ℝ (Set.Ici 0) g
  /-- `g(0) = 0`. -/
  g_zero : g 0 = 0

namespace Model

variable (M : Model)

/-- The integrated channel's profit `Π(q, e) = R(q, e) − g(e) − qc` (p. 21). -/
def Pi (q e : ℝ) : ℝ := M.R q e - M.g e - q * M.c

/-- The retailer's profit under the revenue-sharing contract `{φ, w}`:
`π_r(q, e) = φR(q, e) − g(e) − qw` (p. 22). -/
def retailerProfit (φ w q e : ℝ) : ℝ := φ * M.R q e - M.g e - q * w

/-- The supplier's profit under `{φ, w}` when the retailer chooses `(q, e)`:
`(1 − φ)R(q, e) + q(w − c)` (sequence of events of Sec. 1, p. 5). -/
def supplierProfit (φ w q e : ℝ) : ℝ := (1 - φ) * M.R q e + q * (w - M.c)

end Model

end RevShareCoord.Effort


