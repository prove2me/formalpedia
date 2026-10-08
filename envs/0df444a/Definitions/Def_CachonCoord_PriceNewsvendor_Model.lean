-- Prove2me | Definitions.Def_CachonCoord_PriceNewsvendor_Model
-- name    : CachonCoord_PriceNewsvendor_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:17:16.858722+00:00
-- url     : https://prove2.me/theorems/27d75229-c0be-4ca4-a727-807daec3bbb3
-- title:
--   §6.3.1, pp. 34–37 — price-dependent newsvendor profits and contingent contract terms
-- statement:
--   One retailer chooses a stocking quantity $q\ge0$ and a retail price $p\in P$ before demand is observed. Write $c_s,c_r$ for the supplier's and retailer's unit costs, $g_s,g_r$ for their goodwill penalties per unit of unmet demand, $v$ for the salvage value of a leftover unit, $c=c_s+c_r$ and $g=g_s+g_r$. As in §6.2, $c_s+c_r<p$ for every admissible price and $v<c$. At price $p$, expected sales and mean demand are
--
--   $$S(q,p)=\mathbb E_p[\min(q,D)],\qquad \mu(p)=\mathbb E_p[D].$$
--
--   The integrated profit is
--
--   $$\Pi(q,p)=(p-v+g)S(q,p)-(c-v)q-g\mu(p).$$
--
--   The model also defines the firms' expected profits under each contract of §6.3.1:
--
--   1. buy-back $(w_b,b)$: $\pi_r=(p-v+g_r-b)S(q,p)-(w_b-b+c_r-v)q-g_r\mu(p)$ and $\pi_s=(b+g_s)S(q,p)+(w_b-b-c_s)q-g_s\mu(p)$;
--   2. revenue sharing $(w_r,\phi)$: $\pi_r=(\phi(p-v)+g_r)S(q,p)-(w_r+c_r-\phi v)q-g_r\mu(p)$;
--   3. quantity flexibility $(w_q,\delta)$: $\pi_r=(p-v+g_r)S(q,p)-(w_q+c_r-v)q+(w_q+c_r-v)\int_{(1-\delta)q}^{q}F(y\mid p)\,dy-\mu(p)g_r$;
--   4. quantity discount designed at a price $p^\circ$: $w_d(q)=\bigl((1-\lambda)(p^\circ-v+g)-g_s\bigr)\frac{S(q,p^\circ)}{q}+\lambda(c-v)-c_r+v$, with $\pi_r=(p-v+g_r)S(q,p)-(w_d(q)+c_r-v)q-g_r\mu(p)$ and $\pi_s=g_sS(q,p)+(w_d(q)-c_s)q-g_s\mu(p)$.
--
--   It also records the printed price-contingent buy-back terms
--
--   $$b(p)=(1-\lambda)(p-v+g)-g_s,\qquad w_b(p)=\lambda c_s+(1-\lambda)(p+g-c_r)-g_s,$$
--
--   and the zero-goodwill coordinating revenue-sharing wholesale price $w_r=\lambda(c-v)-c_r+\lambda v$. These functions are the common source of every statement in this mission.
--
--   **Formalization Note** The feasible action set is $q\ge0$, $p\in P$. The costs and goodwill penalties are nonnegative. Expected sales are the expectation $\mathbb E_p[\min(q,D)]$ (the reused `SupplyChainTheory.expSales`), which equals the page's $q-\int_0^qF(y\mid p)\,dy$ for nonnegative demand. The mean $\mu(p)$ is computed from the price-indexed law, so it varies with $p$. Supplier profits use the §6.2 transfer sign (the retailer pays the supplier). The quantity-discount schedule divides by $q$; at $q=0$ Lean's $x/0=0$ makes $w_d(0)$ a junk value, but it enters the profits only multiplied by $q=0$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §§6.2.1, 6.3.1, pp. 7, 10, 34–38; Eqs. (1), (5)–(7), (14)–(16)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CachonCoord_PriceNewsvendor_Demand

namespace CachonCoord.PriceNewsvendor

/-- The one-supplier, one-retailer price-dependent newsvendor of §6.3. -/
structure Model where
  demand : DemandFamily
  cs : ℝ
  cr : ℝ
  gs : ℝ
  gr : ℝ
  v : ℝ
  cs_nonneg : 0 ≤ cs
  cr_nonneg : 0 ≤ cr
  gs_nonneg : 0 ≤ gs
  gr_nonneg : 0 ≤ gr
  price_above_cost : ∀ p ∈ demand.prices, cs + cr < p
  salvage_below_cost : v < cs + cr

namespace Model

variable (M : Model)

/-- Total per-unit production and procurement cost. -/
def c : ℝ := M.cs + M.cr

/-- Total goodwill penalty per unit of unmet demand. -/
def g : ℝ := M.gs + M.gr

/-- Jointly feasible stocking quantities and retail prices. -/
def feasible : Set (ℝ × ℝ) := Set.Ici 0 ×ˢ M.demand.prices

/-- Expected sales `S(q,p) = E_p[min(q,D)]`. -/
noncomputable def S (q p : ℝ) : ℝ :=
  SupplyChainTheory.expSales (M.demand.law p) q

/-- Price-dependent mean demand `μ(p) = E_p[D]`. -/
noncomputable def mu (p : ℝ) : ℝ :=
  SupplyChainTheory.meanDemand (M.demand.law p)

/-- Integrated channel profit on p. 34. -/
noncomputable def Pi (q p : ℝ) : ℝ :=
  (p - M.v + M.g) * M.S q p - (M.c - M.v) * q - M.g * M.mu p

/-- Retailer profit with wholesale price `wb` and buyback payment `b`, p. 35. -/
noncomputable def buybackRetailer (wb b q p : ℝ) : ℝ :=
  (p - M.v + M.gr - b) * M.S q p -
    (wb - b + M.cr - M.v) * q - M.gr * M.mu p

/-- Supplier profit with the same buyback contract, by the p. 17 transfer convention. -/
noncomputable def buybackSupplier (wb b q p : ℝ) : ℝ :=
  (b + M.gs) * M.S q p + (wb - b - M.cs) * q - M.gs * M.mu p

/-- Retailer profit with revenue share `phi` and wholesale price `wr`, p. 36. -/
noncomputable def revenueRetailer (wr phi q p : ℝ) : ℝ :=
  (phi * (p - M.v) + M.gr) * M.S q p -
    (wr + M.cr - phi * M.v) * q - M.gr * M.mu p

/-- The price-dependent buyback rate printed on p. 35. -/
def contingentB (lam p : ℝ) : ℝ :=
  (1 - lam) * (p - M.v + M.g) - M.gs

/-- The price-dependent wholesale price printed on p. 35. -/
def contingentW (lam p : ℝ) : ℝ :=
  lam * M.cs + (1 - lam) * (p + M.g - M.cr) - M.gs

/-- Coordinating revenue-sharing wholesale price when goodwill penalties vanish, p. 37. -/
def revenueW (lam : ℝ) : ℝ :=
  lam * (M.c - M.v) - M.cr + lam * M.v

/-- Retailer profit under the quantity-flexibility contract `(w_q, δ)`, printed on p. 34. -/
noncomputable def qfRetailer (wq δ q p : ℝ) : ℝ :=
  (p - M.v + M.gr) * M.S q p - (wq + M.cr - M.v) * q +
    (wq + M.cr - M.v) * (∫ y in (1 - δ) * q..q, cdfOf (M.demand.law p) y) - M.mu p * M.gr

/-- The quantity-discount schedule `w_d(q)` of p. 38, designed at the price `p0`. -/
noncomputable def qdW (lam p0 q : ℝ) : ℝ :=
  ((1 - lam) * (p0 - M.v + M.g) - M.gs) * (M.S q p0 / q) + lam * (M.c - M.v) - M.cr + M.v

/-- Retailer profit under the quantity discount `w_d(q)`, p. 37. -/
noncomputable def qdRetailer (lam p0 q p : ℝ) : ℝ :=
  (p - M.v + M.gr) * M.S q p - (M.qdW lam p0 q + M.cr - M.v) * q - M.gr * M.mu p

/-- Supplier profit under the quantity discount `w_d(q)`: wholesale revenue less
production cost and the supplier's goodwill cost on expected lost sales. -/
noncomputable def qdSupplier (lam p0 q p : ℝ) : ℝ :=
  M.gs * M.S q p + (M.qdW lam p0 q - M.cs) * q - M.gs * M.mu p

end Model
end CachonCoord.PriceNewsvendor


