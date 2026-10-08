-- Prove2me | Definitions.Def_CachonCoord_EffortNewsvendor_Contracts
-- name    : CachonCoord_EffortNewsvendor_Contracts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:17:40.762989+00:00
-- url     : https://prove2.me/theorems/ca270521-c132-43e5-abe2-e719ced05c64
-- title:
--   §6.4.1, pp. 42–43 — retailer profits under buy-back, quantity-flexibility, revenue-sharing, sales-rebate and quantity-discount contracts with effort
-- statement:
--   In the effort model of §6.4.1 (expected sales $S(q, e)$, demand distribution $F(\cdot \mid e)$, effort cost $g$), the retailer's expected profit at order quantity $q$ and effort $e$ under each contract of §6.2 is:
--
--   1. **Buy back** $\{w_b, b\}$ (p. 42): $\pi_r(q, e, w_b, b) = (p - b)S(q, e) - (w_b - b)q - g(e)$.
--   2. **Quantity flexibility** $\{w_q, \delta\}$ (p. 42): $\pi_r(q, e, w_q, \delta) = pS(q, e) - w_q\big(q - \int_{(1-\delta)q}^q F(y \mid e)\,dy\big) - g(e)$.
--   3. **Revenue sharing** $\{w_r, \phi\}$: $\pi_r(q, e, w_r, \phi) = \phi p S(q, e) - w_r q - g(e)$. This is §6.2.4's profit (p. 21) with $v = g_r = c_r = 0$, less the effort cost.
--   4. **Sales rebate** $\{w_s, r, t\}$: $\pi_r = pS(q, e) - T_s(q, w_s, r, t) - g(e)$, with §6.2.6's transfer (p. 27) computed under $F(\cdot \mid e)$:
--   $$
--   T_s(q, w_s, r, t) = \begin{cases} w_s q, & q < t,\\ (w_s - r)q + r\big(t + \int_t^q F(y \mid e)\,dy\big), & q \ge t.\end{cases}
--   $$
--   5. **Quantity discount** (p. 43): for $q > 0$, a share $\lambda$ and the optimal effort $e^o$,
--   $$
--   w_d(q) = (1 - \lambda)p\,\frac{S(q, e^o)}{q} + \lambda c - (1 - \lambda)\frac{g(e^o)}{q},
--   $$
--   with transfer $T_d(q) = w_d(q)q$, retailer profit $\pi_r(q, e) = pS(q, e) - w_d(q)q - g(e)$ and supplier profit $\pi_s(q) = w_d(q)q - cq$.
--
--   These are the objects compared with the channel profit $\Pi(q, e)$ in the section.
--
--   **Formalization Note** The page prints the last term of $w_d$ as $+(1 - \lambda)g(e^o)/q$. With that sign, $T_d$ contradicts the page's own displays $\pi_r(q, e) = pS(q, e) - (1 - \lambda)pS(q, e^o) - \lambda cq - g(e) + (1 - \lambda)g(e^o)$ and $\pi_r(q, e^o) = \lambda\Pi(q, e^o)$: it gives $\pi_r(q, e^o) = \lambda\Pi(q, e^o) - 2(1 - \lambda)g(e^o)$. The definition therefore uses the sign $-(1 - \lambda)g(e^o)/q$, the one under which both displays hold. $w_d$ divides by $q$, and every statement about it assumes $q > 0$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.4.1, pp. 42–43; revenue sharing §6.2.4, p. 21; sales rebate §6.2.6, p. 27

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model

namespace CachonCoord.EffortNewsvendor

namespace Model

variable (M : Model)

/-- Retailer's profit with a buy back contract `{w_b, b}` (p. 42):
`π_r(q, e, w_b, b) = (p − b)S(q, e) − (w_b − b)q − g(e)`. -/
noncomputable def bbRetailerProfit (wb b q e : ℝ) : ℝ :=
  (M.p - b) * M.S q e - (wb - b) * q - M.effortCost e

/-- Retailer's profit with a quantity-flexibility contract `{w_q, δ}` (p. 42):
`π_r(q, e, w_q, δ) = pS(q, e) − w_q (q − ∫_{(1−δ)q}^q F(y|e) dy) − g(e)`. -/
noncomputable def qfRetailerProfit (wq δ q e : ℝ) : ℝ :=
  M.p * M.S q e - wq * (q - ∫ y in (1 - δ) * q..q, M.F y e) - M.effortCost e

/-- Retailer's profit with a revenue sharing contract `{w_r, φ}`: §6.2.4's
`π_r = (φ(p − v) + g_r)S(q) − (w_r + c_r − φv)q − g_r μ` (p. 21) with `v = g_r = c_r = 0`,
less the effort cost: `φ p S(q, e) − w_r q − g(e)`. -/
noncomputable def rsRetailerProfit (wr φ q e : ℝ) : ℝ :=
  φ * M.p * M.S q e - wr * q - M.effortCost e

/-- The sales rebate transfer `T_s(q, w_s, r, t)` of §6.2.6 (p. 27), with demand distribution
`F(·|e)`: `w_s q` if `q < t`, and `(w_s − r)q + r(t + ∫_t^q F(y|e) dy)` if `q ≥ t`. -/
noncomputable def srTransfer (ws r t q e : ℝ) : ℝ :=
  if q < t then ws * q else (ws - r) * q + r * (t + ∫ y in t..q, M.F y e)

/-- Retailer's profit with a sales rebate contract `{w_s, r, t}`: §6.2.6's
`π_r = (p − v + g_r)S(q) − (c_r − v)q − g_r μ − T_s` (p. 27) with `v = g_r = c_r = 0`,
less the effort cost: `pS(q, e) − T_s(q, w_s, r, t) − g(e)`. -/
noncomputable def srRetailerProfit (ws r t q e : ℝ) : ℝ :=
  M.p * M.S q e - M.srTransfer ws r t q e - M.effortCost e

/-- The quantity discount schedule of p. 43, for `q > 0`, built on the optimal effort `e°`
(argument `eo`) and a share `λ` (argument `lam`):
`w_d(q) = (1 − λ)p (S(q, e°)/q) + λc − (1 − λ) g(e°)/q`.
The sign of the last term is the one under which the page's displayed `π_r(q, e)` and
`π_r(q, e°) = λΠ(q, e°)` hold; the page prints `+ (1 − λ) g(e°)/q`. -/
noncomputable def qdWholesale (lam eo q : ℝ) : ℝ :=
  (1 - lam) * M.p * (M.S q eo / q) + lam * M.c - (1 - lam) * M.effortCost eo / q

/-- Retailer's profit with the quantity discount, transfer `T_d(q) = w_d(q) q`:
`π_r(q, e) = pS(q, e) − w_d(q) q − g(e)`. -/
noncomputable def qdRetailerProfit (lam eo q e : ℝ) : ℝ :=
  M.p * M.S q e - M.qdWholesale lam eo q * q - M.effortCost e

/-- Supplier's profit with the quantity discount: `π_s(q) = w_d(q) q − cq`. -/
noncomputable def qdSupplierProfit (lam eo q : ℝ) : ℝ :=
  M.qdWholesale lam eo q * q - M.c * q

end Model

end CachonCoord.EffortNewsvendor


