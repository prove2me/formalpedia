-- Prove2me | Definitions.Def_PrefDeals_boughtSet
-- name    : PrefDeals_boughtSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:37.900065+00:00
-- url     : https://prove2.me/theorems/dff5f6c4-0a6b-4bd7-8333-94270b0eafd6
-- title:
--   What a buyer buys under a preferred deal
-- statement:
--   Let buyer $j$ be offered the deal $d=(\rho,\mu,\mathcal I)$ when the impressions in $U$ are still unsold. He receives $R=\mathcal I\cap U$. Let
--
--   $$
--   q=\sup\{x\in\mathbb R:\ P(R\cap\{v_j\ge x\})\ge\mu\,P(R)\}
--   $$
--
--   be the top-$\mu$ quantile of his valuation on $R$, and $t=\min(\rho,q)$ his **purchase threshold** ($t=\rho$ when $\mu=0$ or $P(R)=0$). Buying $B=R\cap\{v_j\ge t\}$ is his cheapest way to meet the minimum purchase requirement while buying every impression worth at least $\rho$ to him. He **accepts** the deal iff his expected utility is nonnegative,
--
--   $$
--   \int_B (v_j-\rho)\,dP\ \ge\ 0,
--   $$
--
--   and then buys $B$; otherwise he buys nothing.
--
--   This is the buyer behaviour of §2 (p.6): the requirement is met in expectation, the buyer buys all impressions with $v\ge\theta$ where $\theta=F^{-1}(1-\mu)$, and always buys when $v\ge\rho$, so the requirement binds only when $1-F(\rho)<\mu$. In a priority sequence, the impressions he receives are those not bought by higher-priority buyers (§3).
--
--   **Formalization Note** Expectations are unnormalized (multiplied by $P(R)$), and the fraction $\mu$ refers to the impressions $R$ that reach the buyer. A buyer with zero expected utility accepts, as in the paper's surplus-extracting deals (p.10). When $\mu=0$ or $P(R)=0$ the quantile set is all of $\mathbb R$, whose supremum Lean sets to $0$; the threshold is then $\rho$.
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, §2, p.6 (minimum purchase in expectation, buyer utility) and §3, pp.8–9 (sequence of deals)

import Mathlib
import Definitions.Def_PrefDeals_ValuationModel
import Definitions.Def_PrefDeals_Deal

open MeasureTheory

namespace PrefDeals

open Classical in
/-- **What a buyer buys under a preferred deal (the buyer's behaviour of §2).**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, §2, p.6: "We assume that the minimum
purchase constraint has to be met (only) in expectation. … In order to purchase a fraction `µ` of
the impressions, the buyer will have to purchase all impressions with `v ≥ θ` where
`θ = F⁻¹(1 − µ)` (i.e., `µ = 1 − F(θ)`). Note that under the first-look deal `(ρ, µ)`, the buyer will
always purchase an impression if `v ≥ ρ`. Hence, the minimum purchase requirement constraint is
binding only if `1 − F(ρ) < µ`. The per-impression expected utility of the buyer from the contract
`(µ, ρ)` is equal to `(1 − F(θ))(E[v|v ≥ θ] − ρ)` if the minimum purchase requirement constraint is
binding; otherwise, it is equal to `(1 − F(ρ))(E[v|v ≥ ρ] − ρ)`", with utility `v − ρ` per impression
(p.6), and §3, p.8–9: "Each buyer receives impressions that are not purchased by the buyers with
higher priorities."

`boughtSet M j d U` is the set of impressions buyer `j` buys when offered the deal
`d = (ρ, µ, 𝓘)` while the impressions in `U` are still unsold:
1. he receives `R = 𝓘 ∩ U`;
2. `q = sup {x : P(R ∩ {vⱼ ≥ x}) ≥ µ · P(R)}` is the top-`µ` quantile of `vⱼ` on `R`;
3. his purchase threshold is `t = min(ρ, q)` (and `t = ρ` when `µ = 0` or `P(R) = 0`), and he would
   buy `B = R ∩ {vⱼ ≥ t}`;
4. he accepts the deal, and buys `B`, iff his expected utility `∫_B (vⱼ − ρ) dP` is `≥ 0`; otherwise he
   buys nothing.

**Formalization Note.** Utilities and the purchase requirement are expectations over the stream
`(Ω, P)` (unnormalized, i.e. multiplied by `P(R)`), as on p.6. The fraction `µ` is a fraction of the
impressions `R` that reach the buyer. A buyer indifferent between accepting and rejecting accepts:
the paper's deals are set "such that the deal extracts the buyer's surplus" (p.10). When `µ = 0` or
`P(R) = 0` the quantile set is all of `ℝ` (its `sSup` is a junk `0`), so the threshold is `ρ`, the
buyer's unconstrained choice. -/
noncomputable def boughtSet {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (j : Fin n) (d : Deal Ω) (U : Set Ω) : Set Ω :=
  let R := d.impressions ∩ U
  let q := sSup {x : ℝ | d.minFrac * P.real R ≤ P.real (R ∩ {ω | x ≤ M.v j ω})}
  let t := if d.minFrac = 0 ∨ P R = 0 then d.price else min d.price q
  let B := R ∩ {ω | t ≤ M.v j ω}
  if 0 ≤ ∫ ω in B, (M.v j ω - d.price) ∂P then B else ∅

end PrefDeals


