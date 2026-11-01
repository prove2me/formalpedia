-- Prove2me | Definitions.Def_PrefDeals_dealRevenue
-- name    : PrefDeals_dealRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:27.537545+00:00
-- url     : https://prove2.me/theorems/a33eebe0-5b76-4702-9a7e-35f0ee6cd984
-- title:
--   Expected per-impression revenue of a priority sequence of deals
-- statement:
--   A priority sequence is a list $((j_1,d_1),\dots,(j_m,d_m))$ of buyers and deals. Process it in order, starting with every impression unsold, $U_0=\Omega$: buyer $j_k$ buys $B_k$ (his purchase under $d_k$, given the unsold impressions $U_{k-1}$, as defined by `boughtSet`) and $U_k=U_{k-1}\setminus B_k$. The **revenue** of the sequence is
--
--   $$
--   \mathrm{Rev}=\sum_{k=1}^m \rho_k\,P(B_k),
--   $$
--
--   where $\rho_k$ is the price of $d_k$. The helper `revenueFrom` computes the same sum starting from an arbitrary set $U_0$ of unsold impressions.
--
--   Since $P(\Omega)=1$, this is the expected per-impression revenue of the paper: each buyer pays his price on the fraction of impressions he buys, and each buyer receives only the impressions the buyers before him did not buy.
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, §3, pp.8–9 (priority list, sequence of preferred deals)

import Mathlib
import Definitions.Def_PrefDeals_boughtSet

open MeasureTheory

namespace PrefDeals

/-- The revenue of a priority sequence of deals processed on the unsold impressions `U`:
each buyer in turn buys `boughtSet` from what is still unsold, pays its price per impression on
the bought impressions, and the bought impressions are removed. -/
noncomputable def revenueFrom {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) : List (Fin n × Deal Ω) → Set Ω → ℝ
  | [], _ => 0
  | (j, d) :: rest, U =>
      d.price * P.real (boughtSet M j d U) + revenueFrom M rest (U \ boughtSet M j d U)

/-- **Expected per-impression revenue of a sequence of preferred deals.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, §3, pp.8–9: "The seller chooses a
priority list `(π₁, π₂, …, πₙ)` … The seller offers to each buyer `i` a preferred deal
`(ρᵢ, µᵢ, 𝓘ᵢ)`. … Each buyer receives impressions that are not purchased by the buyers with higher
priorities. For example, all the impressions are sent to `π₁`, the buyer with the highest
priority. The buyer with the second highest priority receives all the impressions that are not
purchased by `π₁`, and so on."

`dealRevenue M seq` is `Σ_k ρ_k · P(B_k)` where the list `seq` of (buyer, deal) pairs is processed in
order, starting with all impressions unsold, and `B_k = boughtSet` of the `k`-th buyer on the
impressions still unsold when his turn comes.

**Formalization Note.** Revenue is expected revenue per impression: `P(Ω) = 1` for a probability
measure, so `ρ_k · P(B_k)` is the price times the fraction of impressions bought. -/
noncomputable def dealRevenue {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (seq : List (Fin n × Deal Ω)) : ℝ :=
  revenueFrom M seq Set.univ

end PrefDeals


