-- Prove2me | Definitions.Def_CachonCoord_Newsvendor_Contracts
-- name    : CachonCoord_Newsvendor_Contracts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:53:49.613362+00:00
-- url     : https://prove2.me/theorems/a082f040-1c42-451a-bf07-2e25dba5c4f9
-- title:
--   §6.2, pp. 7–29 — Cachon’s newsvendor data, profits, and contract transfers
-- statement:
--   Cachon’s newsvendor has price $p$, unit costs $c_s,c_r$, goodwill penalties $g_s,g_r$, and net salvage $v<c_s+c_r<p$. Demand has mean $\mu$ and cdf $F$. Expected sales, leftover inventory, and profits are defined from the demand law. Transfers flow from the retailer to the supplier.
--
--   $$S(q)=E[\min(q,D)],\quad I(q)=E[(q-D)^+],\quad \Pi(q)=(p-v+g_s+g_r)S(q)-(c_s+c_r-v)q-(g_s+g_r)\mu.$$
--
--   The file also defines wholesale, buy-back, revenue-sharing, quantity-flexibility, sales-rebate, and quantity-discount transfers and the realized payments used in §6.2.
--
--   **Formalization Note** The local model preserves $v<c_s+c_r$ and allows negative net salvage. Goodwill penalty costs are nonnegative. The published Snyder–Shen model required $0\le v<c_r$ and was too narrow for this chapter. At $q=0$, $S(q)/q$ takes Lean’s zero value; $w_d(q)q=0$ there.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.2.1–6.2.7, pp. 7–29

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CachonCoord.Newsvendor

/-- The parameters of Cachon's §6.2 newsvendor. In particular, the net salvage value
only has to be below the *combined* unit cost; it may be negative. -/
structure ContractData where
  r : ℝ
  cs : ℝ
  cr : ℝ
  ps : ℝ
  pr : ℝ
  v : ℝ
  ps_nonneg : 0 ≤ ps
  pr_nonneg : 0 ≤ pr
  profitable : cs + cr < r
  v_lt_c : v < cs + cr

namespace ContractData

def c (P : ContractData) : ℝ := P.cs + P.cr
def p (P : ContractData) : ℝ := P.ps + P.pr

end ContractData

/-- Expected sales `S(q) = E[min(q,D)]` (p. 10). -/
noncomputable def expSales (D : Measure ℝ) (q : ℝ) : ℝ := ∫ d, min q d ∂D

/-- Expected unsold inventory `I(q) = E[(q-D)⁺]` (p. 10). -/
noncomputable def expLeftover (D : Measure ℝ) (q : ℝ) : ℝ := ∫ d, max (q - d) 0 ∂D

/-- Mean demand `μ = E[D]` (p. 7). -/
noncomputable def meanDemand (D : Measure ℝ) : ℝ := ∫ d, d ∂D

/-- Retailer's expected profit in Eq. (1), with a transfer paid to the supplier. -/
noncomputable def retailerProfit (P : ContractData) (D : Measure ℝ) (T : ℝ → ℝ) (q : ℝ) : ℝ :=
  (P.r - P.v + P.pr) * expSales D q - (P.cr - P.v) * q - P.pr * meanDemand D - T q

/-- Supplier's expected profit in Eq. (1). -/
noncomputable def supplierProfit (P : ContractData) (D : Measure ℝ) (T : ℝ → ℝ) (q : ℝ) : ℝ :=
  P.ps * expSales D q - P.cs * q - P.ps * meanDemand D + T q

/-- Integrated channel profit in Eq. (1). -/
noncomputable def chainProfit (P : ContractData) (D : Measure ℝ) (q : ℝ) : ℝ :=
  (P.r - P.v + P.p) * expSales D q - (P.c - P.v) * q - P.p * meanDemand D

/-- The wholesale payment and its retailer-inducing price (pp. 12–14). -/
def wholesaleTransfer (w q : ℝ) : ℝ := w * q

noncomputable def wholesaleInducing (P : ContractData) (D : Measure ℝ) (q : ℝ) : ℝ :=
  (P.r - P.v + P.pr) * (1 - cdf D q) - (P.cr - P.v)

/-- Expected payment under the buy-back contract (p. 17). -/
noncomputable def buybackTransfer (D : Measure ℝ) (w b : ℝ) (q : ℝ) : ℝ :=
  w * q - b * expLeftover D q

/-- Expected payment under revenue sharing (p. 21). -/
noncomputable def revenueShareTransfer (P : ContractData) (D : Measure ℝ) (w phi : ℝ) (q : ℝ) : ℝ :=
  (w + (1 - phi) * P.v) * q + (1 - phi) * (P.r - P.v) * expSales D q

/-- Quantity-flexibility transfer on p. 24, with the printed `w` read as `w_q`. -/
noncomputable def quantityFlexTransfer (P : ContractData) (D : Measure ℝ)
    (w delta : ℝ) (q : ℝ) : ℝ :=
  w * q - (w + P.cr - P.v) * ∫ y in (1 - delta) * q..q, cdf D y

/-- The coordinating wholesale price displayed after Eq. (11) on p. 24. -/
noncomputable def quantityFlexPrice (P : ContractData) (D : Measure ℝ)
    (q0 delta : ℝ) : ℝ :=
  (P.r - P.v + P.pr) * (1 - cdf D q0) /
    (1 - cdf D q0 + (1 - delta) * cdf D ((1 - delta) * q0)) - P.cr + P.v

/-- Cachon (2003), 3rd draft, §6.2.6, p. 27: the sales rebate transfer `T_s(q, w_s, r, t)`.
The supplier charges `w_s` per unit and gives a rebate `r` (here `rebate`; Cachon's letter `r` is
not the retail price `P.r` of `ContractData`) per unit sold above the threshold `t`:
`T_s = w_s q` for `q < t` and `T_s = (w_s − r) q + r (t + ∫_t^q F(y) dy)` for `q ≥ t`,
where `F = cdf D` is the demand distribution function. -/
noncomputable def salesRebateTransfer (D : Measure ℝ) (ws rebate t : ℝ) (q : ℝ) : ℝ :=
  if q < t then ws * q else (ws - rebate) * q + rebate * (t + ∫ y in t..q, cdf D y)

/-- Cachon (2003), §6.2.6, Eq. (13), p. 27: the sales rebate wholesale price
`w_s(r) = (p − v + g_r + r) F̄(q°) − c_r + v` for the chain-optimal quantity `q0 = q°`
(`P.r` = Cachon's retail price `p`, `P.pr` = his `g_r`, `rebate` = his `r`). -/
noncomputable def salesRebatePrice (P : ContractData) (D : Measure ℝ) (q0 rebate : ℝ) : ℝ :=
  (P.r - P.v + P.pr + rebate) * (1 - cdf D q0) - P.cr + P.v

/-- Cachon (2003), §6.2.7, p. 29: the all-unit quantity discount schedule
`w_d(q) = ((1 − λ)(p − v + g) − g_s) (S(q)/q) + λ(c − v) − c_r + v`
(`P.r` = `p`, `P.p` = `g = g_s + g_r`, `P.ps` = `g_s`, `P.c` = `c = c_s + c_r`). At `q = 0` the
quotient `S(q)/q` takes Lean's junk value `0`; the transfer `w_d(q) q` is `0` there anyway. -/
noncomputable def quantityDiscountPrice (P : ContractData) (D : Measure ℝ) (lam q : ℝ) : ℝ :=
  ((1 - lam) * (P.r - P.v + P.p) - P.ps) * (expSales D q / q) + lam * (P.c - P.v) - P.cr + P.v

/-- Cachon (2003), §6.2.7, p. 28: the quantity discount transfer `T_d(q) = w_d(q) q`. -/
noncomputable def quantityDiscountTransfer (P : ContractData) (D : Measure ℝ) (lam q : ℝ) : ℝ :=
  quantityDiscountPrice P D lam q * q

/-- Realized retailer profit for order `q`, realized demand `x` and realized transfer `T`:
`p min(q, x) + v (q − x)⁺ − g_r (x − q)⁺ − c_r q − T` (the realization of Cachon's p. 11
`π_r = pS(q) + vI(q) − g_r L(q) − c_r q − T`). -/
def realizedRetailerProfit (P : ContractData) (q x T : ℝ) : ℝ :=
  P.r * min q x + P.v * max (q - x) 0 - P.pr * max (x - q) 0 - P.cr * q - T

/-- Realized supplier profit for order `q`, realized demand `x` and realized transfer `T`:
`T − c_s q − g_s (x − q)⁺` (the realization of Cachon's p. 11 `π_s = g_s S(q) − c_s q − g_s μ + T`). -/
def realizedSupplierProfit (P : ContractData) (q x T : ℝ) : ℝ :=
  T - P.cs * q - P.ps * max (x - q) 0

/-- Cachon (2003), §6.2.4, p. 22: the realized revenue sharing payment under `{w_r, φ}`: the
retailer pays `w_r + (1 − φ)v` per unit purchased and `(1 − φ)(p − v)` per unit sold. -/
def revenueShareRealizedTransfer (P : ContractData) (wr phi q x : ℝ) : ℝ :=
  (wr + (1 - phi) * P.v) * q + (1 - phi) * (P.r - P.v) * min q x

/-- Cachon (2003), §6.2.4, p. 22: the realized buy back payment under `{w_b, b}`: the retailer
pays `w_b` per unit purchased and receives a credit `b` per unit not sold. -/
def buybackRealizedTransfer (wb b q x : ℝ) : ℝ :=
  wb * q - b * max (q - x) 0

end CachonCoord.Newsvendor


