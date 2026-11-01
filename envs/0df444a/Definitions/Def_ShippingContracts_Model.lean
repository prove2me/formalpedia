-- Prove2me | Definitions.Def_ShippingContracts_Model
-- name    : ShippingContracts_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:23.614682+00:00
-- url     : https://prove2.me/theorems/2a6d15c4-e1e4-4ff5-8653-54d44a6af928
-- title:
--   Seller–shipper model: parameters, demand law, contracts $(\nu,p_o,p_u)$, profits (3.2), (4.5), (5.7), cost (5.8), best responses, coordination, $\nu_C$
-- statement:
--   This module defines the model of Song and Zhao's e-commerce supply chain: one online seller, one third-party shipper, one selling season.
--
--   **Parameters** (pp. 9–10, Assumption 2 p. 14). The selling price $p$, procurement cost $c$ and salvage value $s$ satisfy $p>c>s$; the seller's overage and underage costs are $c_o=c-s$ and $c_u=p-c$. The shipper builds regular capacity at unit cost $u$ before the season and emergency capacity at unit cost $u'$ in season, with $0<u\le u'$.
--
--   **Demand.** The demand $D$ has law $\mu$ on $\mathbb R$ with $D\ge0$ almost surely, finite mean, and c.d.f. $F$ continuous and strictly increasing on $\{x\ge0:F(x)<1\}$.
--
--   **Contracts** (p. 10, p. 15). A contract $\kappa=(\nu,p_o,p_u)$ charges $\nu$ per unit shipped, $p_o$ per unit of over-reservation and $p_u$ per unit of under-reservation. It is feasible when $u\le\nu$, $0\le p_u\le c_u-\nu$ and $0\le p_o\le\nu$. The flat rate is $p_o=p_u=0$.
--
--   **Objectives.** With reservation $r$, inventory $q$, capacity $c$ and shipment $S=\min(q,D)$:
--
--   1. the seller's expected profit, eqs. (3.2)–(3.3):
--   $$\Pi_{\rm Seller}(r,q)=E[D](p-c-\nu)-E\big[c_o(q-D)^++(c_u-\nu)(D-q)^+\big]-E\big[p_o(r-S)^++p_u(S-r)^+\big];$$
--   2. the shipper's expected profit, eq. (4.5) (and (4.6) when $p_o=p_u=0$):
--   $$\Pi_{\rm Shipper}(r,q,c)=\nu E[S]+E\big[p_o(r-S)^++p_u(S-r)^+\big]-\big(uc+u'E[(S-c)^+]\big);$$
--   3. the integrated chain's expected profit, eq. (5.7), and total cost, eq. (5.8):
--   $$\Pi_{SC}(c,q)=E[D](p-c)-E\big[c_o(q-D)^++c_u(D-q)^+\big]-\big(uc+u'E[(S-c)^+]\big),$$
--   $$H(c,q)=E\big[c_o(q-D)^++c_u(D-q)^+\big]+uc+u'E[(S-c)^+].$$
--
--   **Decisions** (sequence of events, p. 10). The seller's best response to $\kappa$ is any $(r,q)$ with $r,q\ge0$ maximizing $\Pi_{\rm Seller}$ over $r',q'\ge0$; the shipper's best response to $(r,q)$ is any capacity $c\ge0$ maximizing $\Pi_{\rm Shipper}(r,q,\cdot)$ over $c'\ge0$; a first best is any $(c,q)$ with $c,q\ge0$ maximizing $\Pi_{SC}$ over $c',q'\ge0$. A contract **coordinates** the supply chain when best responses exist and every seller best response $(r,q)$ together with every shipper best response $c$ to it gives a first best $(c,q)$.
--
--   **Switch condition and coordinating rate** (Theorems 4, 7). Case a is $c_o(u'-u)<u(c_u-u')$, the multiplied form of $\frac{c_o}{c_u-u'}<\frac{u}{u'-u}$; case b is its negation. The coordinating flat rate is $\nu_C=u'$ in case a and $\nu_C=\frac{c_o+c_u}{c_o+u}\,u$ in case b.
--
--   These objects carry every statement of the mission: the first best (Lemma 2, Theorem 4), the seller's and the shipper's responses (eq. (3.4), Theorem 2, Proposition 3), coordination (Theorem 7) and the profit split (Theorem 8).
--
--   **Formalization Note** The paper writes $c$ for both the procurement cost and the capacity; Lean uses `cProc` and an argument `cap`, and `uE` for $u'$. No density is assumed. The positivity $u>0$ is stated only in the proofs (App. p. 2) and is part of `Params.Shipping`. Expectations are Bochner integrals against $\mu$; every integrand is bounded by a constant plus a multiple of $|D|$, so finite mean makes them honest. The optimal decisions are argmax predicates, never closed forms; $\nu_C$ is the one closed form, as Theorem 7 specifies it.
-- source:
--   Song–Zhao, Supply Chain Coordination for E-Commerce: Risk Penalty vs. Flat Rate (SSRN manuscript 3129499, titled 'Supply Chain Integration for Online Shopping Holidays: Risk Penalty vs. Flat Rate'; version of record MSOM 2021, doi:10.1287/msom.2021.1008), §3 pp. 9–11 (p > c > s, c_o, c_u, contract, eqs. (3.2)–(3.3), Assumption 1), §4 pp. 14–15 (Assumption 2, eq. (4.5)–(4.6), constraints), §5 p. 17 (eqs. (5.7)–(5.8)), Theorem 4 p. 17 and Theorem 7 p. 19 (switch condition, ν_C); printed page = PDF page

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ShippingContracts

/-- **Parameters of the seller–shipper model**, Song–Zhao, *Supply Chain Coordination for
E-Commerce: Risk Penalty vs. Flat Rate* (SSRN 3129499), §3 p. 9 and p. 10 (PDF 9–10), and
Assumption 2, p. 14 (PDF 14).

* `p` is the selling price, `cProc` the procurement cost and `s` the salvage value (p. 9);
* `u` is the unit cost of regular shipping capacity and `uE` the unit cost of emergency
  shipping capacity `u'` (Assumption 2, p. 14).

**Formalization Note.** The paper writes `c` both for the procurement cost (§3) and for the
shipper's capacity (§4–§5); here the procurement cost is `cProc` and the capacity is an argument
`cap` of the objectives. `u'` is written `uE`. -/
structure Params where
  p : ℝ
  cProc : ℝ
  s : ℝ
  u : ℝ
  uE : ℝ

/-- The seller's inventory overage cost `c_o = c − s` (p. 10, PDF 10). -/
def Params.co (P : Params) : ℝ := P.cProc - P.s

/-- The seller's inventory underage cost `c_u = p − c` (p. 10, PDF 10). -/
def Params.cu (P : Params) : ℝ := P.p - P.cProc

/-- The price assumption `p > c > s` of §3, p. 9 (PDF 9). -/
structure Params.Prices (P : Params) : Prop where
  s_lt_cProc : P.s < P.cProc
  cProc_lt_p : P.cProc < P.p

/-- The shipping-cost assumptions: `u' ≥ u` (Assumption 2 (3), p. 14, PDF 14) and `u > 0`.

**Formalization Note.** `u > 0` is not printed in a statement; the proofs use it
("`= u > 0`", proof of Proposition 3, App. p. 2, PDF 31), and without it the fractile
`(u' − u)/u'` is undefined at `u' = 0`. -/
structure Params.Shipping (P : Params) : Prop where
  u_pos : 0 < P.u
  u_le_uE : P.u ≤ P.uE

/-- **The demand law.** `μ` is the law of the demand `D` (p. 9, PDF 9): `D ≥ 0` almost surely,
`D` has a finite mean (the objectives contain `E[D]`), and its c.d.f. `F = cdf μ` is continuous
and strictly increasing on `{x ≥ 0 : F(x) < 1}`.

**Formalization Note.** The paper assumes a density `f` and a c.d.f. `F`, "both being continuous
and differentiable", and uses `F⁻¹` as an honest inverse on `[0, 1)` with `F⁻¹(0) = 0`. Here no
density is assumed; the conditions above are exactly what makes "`x ≥ 0` with `F x = t`" have a
unique solution for every `t ∈ [0, 1)`. `F(0) = 0` follows from `D ≥ 0` and continuity. The
probability-measure property of `μ` is an instance argument of each theorem. -/
structure DemandLaw (μ : Measure ℝ) : Prop where
  nonneg : ∀ᵐ x ∂μ, 0 ≤ x
  integrable : Integrable (fun x : ℝ => x) μ
  continuous_cdf : Continuous (cdf μ)
  strictMonoOn_cdf : StrictMonoOn (cdf μ) {x : ℝ | 0 ≤ x ∧ cdf μ x < 1}

/-- **A shipping contract** `κ = (ν, p_o, p_u)` (p. 10, PDF 10): the base shipping rate `ν` per
unit shipped, the penalty `p_o` per unit of over-reservation and the penalty `p_u` per unit of
under-reservation. The flat rate is `p_o = p_u = 0` (p. 10). -/
structure Contract where
  nu : ℝ
  po : ℝ
  pu : ℝ

/-- **Feasible contracts**: the shipper's constraints `u ≤ ν`, `0 ≤ p_u ≤ c_u − ν`,
`0 ≤ p_o ≤ ν` (p. 15, PDF 15), which contain Assumption 1 (p. 11, PDF 11). -/
def Feasible (P : Params) (κ : Contract) : Prop :=
  P.u ≤ κ.nu ∧ 0 ≤ κ.pu ∧ κ.pu ≤ P.cu - κ.nu ∧ 0 ≤ κ.po ∧ κ.po ≤ κ.nu

/-- **The seller's expected profit**, eqs. (3.2)–(3.3), p. 11 (PDF 11), at reservation `r` and
inventory `q`, with shipment `S = min(q, D)`:
`Π_Seller(r, q) = E[D](p − c − ν) − E[c_o (q − D)⁺ + (c_u − ν)(D − q)⁺]
  − E[p_o (r − S)⁺ + p_u (S − r)⁺]`.

**Formalization Note.** Expectations are Bochner integrals against `μ`; every integrand is
bounded by a constant plus a multiple of `|D|`, so `DemandLaw.integrable` makes them honest. -/
noncomputable def sellerProfit (P : Params) (μ : Measure ℝ) (κ : Contract) (r q : ℝ) : ℝ :=
  (∫ x, x ∂μ) * (P.p - P.cProc - κ.nu)
    - (∫ x, (P.co * max (q - x) 0 + (P.cu - κ.nu) * max (x - q) 0) ∂μ)
    - (∫ x, (κ.po * max (r - min q x) 0 + κ.pu * max (min q x - r) 0) ∂μ)

/-- **The shipper's expected profit**, eq. (4.5), p. 15 (PDF 15), at the seller's decisions
`(r, q)` and the shipper's regular capacity `cap`, with shipment `S = min(q, D)`:
`Π_Shipper = ν E[S] + E[p_o (r − S)⁺ + p_u (S − r)⁺] − (u·cap + u' E[(S − cap)⁺])`.
Eq. (4.6) is the case `p_o = p_u = 0`.

**Formalization Note.** The paper evaluates (4.5) at the seller's response `(r*, q*)`; here
`(r, q)` are arguments, and `SellerBR` supplies the response. -/
noncomputable def shipperProfit (P : Params) (μ : Measure ℝ) (κ : Contract) (r q cap : ℝ) : ℝ :=
  κ.nu * (∫ x, min q x ∂μ)
    + (∫ x, (κ.po * max (r - min q x) 0 + κ.pu * max (min q x - r) 0) ∂μ)
    - (P.u * cap + P.uE * ∫ x, max (min q x - cap) 0 ∂μ)

/-- **The integrated supply chain's expected profit**, eq. (5.7), p. 17 (PDF 17), at capacity
`cap` and inventory `q`, with `S = min(q, D)`:
`Π_SC = E[D](p − c) − E[c_o (q − D)⁺ + c_u (D − q)⁺] − (u·cap + u' E[(S − cap)⁺])`. -/
noncomputable def chainProfit (P : Params) (μ : Measure ℝ) (cap q : ℝ) : ℝ :=
  (∫ x, x ∂μ) * (P.p - P.cProc)
    - (∫ x, (P.co * max (q - x) 0 + P.cu * max (x - q) 0) ∂μ)
    - (P.u * cap + P.uE * ∫ x, max (min q x - cap) 0 ∂μ)

/-- **The supply chain's total cost** `H(c, q)`, eq. (5.8), p. 17 (PDF 17):
`H(c, q) = E[c_o (q − D)⁺ + c_u (D − q)⁺] + (u·c + u' E[(S − c)⁺])`, `S = min(q, D)`. -/
noncomputable def totalCost (P : Params) (μ : Measure ℝ) (cap q : ℝ) : ℝ :=
  (∫ x, (P.co * max (q - x) 0 + P.cu * max (x - q) 0) ∂μ)
    + (P.u * cap + P.uE * ∫ x, max (min q x - cap) 0 ∂μ)

/-- **The seller's best response** to a contract `κ` (sequence of events, p. 10, PDF 10): the
reservation `r ≥ 0` and inventory `q ≥ 0` maximize `Π_Seller(κ; ·, ·)` over all `r', q' ≥ 0`. -/
def SellerBR (P : Params) (μ : Measure ℝ) (κ : Contract) (r q : ℝ) : Prop :=
  0 ≤ r ∧ 0 ≤ q ∧
    ∀ r' q' : ℝ, 0 ≤ r' → 0 ≤ q' → sellerProfit P μ κ r' q' ≤ sellerProfit P μ κ r q

/-- **The shipper's best response** in capacity (p. 10, PDF 10): having observed `(r, q)`, the
shipper's capacity `cap ≥ 0` maximizes `Π_Shipper(κ; r, q, ·)` over all `cap' ≥ 0`. -/
def ShipperBR (P : Params) (μ : Measure ℝ) (κ : Contract) (r q cap : ℝ) : Prop :=
  0 ≤ cap ∧ ∀ cap' : ℝ, 0 ≤ cap' → shipperProfit P μ κ r q cap' ≤ shipperProfit P μ κ r q cap

/-- **The first best** (p. 17, PDF 17): `(cap, q)` with `cap, q ≥ 0` maximizes the integrated
chain's profit (5.7) over all `cap', q' ≥ 0`. -/
def FirstBest (P : Params) (μ : Measure ℝ) (cap q : ℝ) : Prop :=
  0 ≤ cap ∧ 0 ≤ q ∧
    ∀ cap' q' : ℝ, 0 ≤ cap' → 0 ≤ q' → chainProfit P μ cap' q' ≤ chainProfit P μ cap q

/-- **The contract coordinates the supply chain** (§5, pp. 19–20, PDF 19–20; the meaning of the
last sentence of Theorem 5): the seller and the shipper have best responses, and every pair of
best responses `(r, q)`, `cap` gives the first-best capacity and inventory.

**Formalization Note.** The existence clause excludes a contract that "coordinates" vacuously
because no best response exists. -/
def Coordinates (P : Params) (μ : Measure ℝ) (κ : Contract) : Prop :=
  (∃ r q cap : ℝ, SellerBR P μ κ r q ∧ ShipperBR P μ κ r q cap) ∧
    ∀ r q cap : ℝ, SellerBR P μ κ r q → ShipperBR P μ κ r q cap → FirstBest P μ cap q

/-- **The switch condition, case a** of Theorems 4 and 7 (p. 17 and p. 19, PDF 17, 19):
`c_o/(c_u − u') < u/(u' − u)`, written multiplied out as `c_o (u' − u) < u (c_u − u')`.
Case b is its negation.

**Formalization Note.** The printed quotients have zero denominators at `u = u'` or `c_u = u'`.
The multiplied form agrees with them under `a/0 = +∞` for `a > 0`; at `u = u' = c_u` (`0/0` on both
sides) it gives case b, where Theorem 4's `q = c = 0` is correct. -/
def CaseA (P : Params) : Prop :=
  P.co * (P.uE - P.u) < P.u * (P.cu - P.uE)

/-- **The coordinating flat rate** `ν_C` of Theorem 7, p. 19 (PDF 19): `ν_C = u'` in case a and
`ν_C = ((c_o + c_u)/(c_o + u))·u` in case b.

**Formalization Note.** The `if` tests `CaseA P` written out, so that it is decidable. -/
noncomputable def nuC (P : Params) : ℝ :=
  if P.co * (P.uE - P.u) < P.u * (P.cu - P.uE) then P.uE else (P.co + P.cu) / (P.co + P.u) * P.u

end ShippingContracts


