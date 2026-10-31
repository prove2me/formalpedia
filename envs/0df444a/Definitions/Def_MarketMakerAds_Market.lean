-- Prove2me | Definitions.Def_MarketMakerAds_Market
-- name    : MarketMakerAds_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:28.82862+00:00
-- url     : https://prove2.me/theorems/121eb032-aa00-4db9-85f5-22c9dd881e73
-- title:
--   The market — $I$ units, random unit values, and the outcomes with and without the contract
-- statement:
--   A seller sells $I$ identical units. On a probability space $(\Omega,\mathbb P)$, an outcome $\omega$ gives a random number $N(\omega)$ of **units demanded** and their values $V_0(\omega),\dots,V_{N(\omega)-1}(\omega)\ge0$. A buyer of demand $k$ and value $v$ contributes $k$ copies of $v$, the paper's per-unit reduction (Assumption 2). Values may be correlated and $N$ is random; no independence is assumed. $N$ and each $V_j$ are measurable.
--
--   **Without the contract.** The clearing price $c$ is the $(I+1)$-th highest unit value, and $0$ if at most $I$ units are demanded. The $I$ highest units win and each pays $c$. So:
--
--   - the efficiency $\mathrm{Eff}_0$ is the sum of the $I$ highest unit values;
--   - the revenue is $R_0=I\,c$;
--   - every unit of value $v$ gets $U_A(v)$, computed with the law $g$ of $c$; $B_0$ is the sum of these utilities;
--   - the welfare is $W_0=B_0+R_0$.
--
--   **With the contract at $p=p^*_M(g)$.** The units whose value satisfies the purchase rule buy the contract. There are $\ell$ of them, and they pay $p$ each. The other units take part in the $(I-\ell+1)$-th price auction for the remaining $I-\ell$ units, with clearing price $c_1$. So:
--
--   - the efficiency $\mathrm{Eff}_1$ is the contract units plus the $I-\ell$ highest other units;
--   - the revenue is $R_1=\ell\,p+(I-\ell)\,c_1$;
--   - $B_1$ sums $U_{\mathrm{buy}}(v,p)$ over contract units and $U_A(v)$ over the others;
--   - the welfare is $W_1=B_1+R_1$.
--
--   Efficiency is the sum of the allocated values, welfare is the buyers' utilities plus the revenue, and revenue is the sum of prices paid (§3.4).
--
--   **Formalization Note** $I-\ell$ is truncated natural subtraction, cast to $\mathbb R$; Theorem 3 proves $\ell\le I$ almost surely. The law $g$ is the unconditional law of $c$, the same for every buyer.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, §3.1, pp.9–10; Assumptions 1–2, pp.10–11; §3.4, p.13; Proof of Theorem 3, pp.18–19

import Mathlib
import Definitions.Def_MarketMakerAds_buysMM
import Definitions.Def_MarketMakerAds_pStar
import Definitions.Def_MarketMakerAds_sortDesc

open MeasureTheory

namespace MarketMakerAds

/-- **The market: `I` identical units and a random list of unit values.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, §3.1, pp.9–10
("A seller intends to sell I identical units of a good … There are N buyers (where N can
potentially be a random variable) whose values … are drawn from a joint distribution F(·), which
is not necessarily independent across bidders. Buyer i has a demand of k_i units"), Assumption 1
(identical units) and Assumption 2, p.11 ("the multi-unit auction's payment is assumed to be
v_{I+1} per unit … this allows us to have all further discussions on a per-unit basis").

On a probability space `Ω`, the market outcome `ω` gives a number `N ω` of **units demanded**
and their values `V ω 0, …, V ω (N ω − 1)`, all nonnegative. A buyer with value `v` and demand
`k` contributes `k` copies of `v`; this is the paper's per-unit reduction (Assumption 2), and every
demand profile is such a list. The values may be correlated and `N` is random; no independence
or identical distribution is assumed.

**Formalization Note** Values at indices `≥ N ω` are ignored. -/
structure Market (Ω : Type*) [MeasurableSpace Ω] where
  /-- Number of identical units the seller sells. -/
  I : ℕ
  /-- Number of units demanded (with multiplicities), random. -/
  N : Ω → ℕ
  /-- Unit values; `V ω j` for `j < N ω` is the value of the `j`-th unit demanded. -/
  V : Ω → ℕ → ℝ
  measurable_N : Measurable N
  measurable_V : ∀ j, Measurable fun ω => V ω j
  nonneg_V : ∀ ω j, 0 ≤ V ω j

namespace Market

variable {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω)

/-- The list of unit values of outcome `ω`. -/
def units (ω : Ω) : List ℝ :=
  List.ofFn fun j : Fin (M.N ω) => M.V ω j

/-- **Clearing price `c = v_{I+1}`** (p.10, p.11): the `(I+1)`-th highest unit value, and `0`
when at most `I` units are demanded (supply is not exhausted). -/
noncomputable def c (ω : Ω) : ℝ :=
  (sortDesc (M.units ω)).getD M.I 0

/-- **Efficiency without the contract** (§3.4, p.13: "the sum of valuations of the allocated
buyers"): the `I` highest unit values win the `(I+1)`-th price auction (p.11). -/
noncomputable def eff0 (ω : Ω) : ℝ :=
  ((sortDesc (M.units ω)).take M.I).sum

/-- **Revenue without the contract** (§3.4, p.13: "the sum of prices paid to the seller"):
`I · c`, each of the `I` allocated units paying `v_{I+1}` (p.11). It is `0` when at most `I`
units are demanded, since then `c = 0`. -/
noncomputable def rev0 (ω : Ω) : ℝ :=
  (M.I : ℝ) * M.c ω

/-- **The law `g` of the clearing price** (p.10: each buyer knows "the distribution of v_{I+1}
… with pdf g(·)"). It is the unconditional law `P ∘ c⁻¹`, the same for every buyer. -/
noncomputable def priceLaw (P : Measure Ω) : Measure ℝ :=
  P.map M.c

/-- **Sum of the buyers' utilities without the contract**: every unit of value `v` gets the
auction utility `U_A(v)` under the clearing-price law `g` (eq. (1), p.12). -/
noncomputable def util0 (m : RiskModel) (P : Measure Ω) (ω : Ω) : ℝ :=
  ((M.units ω).map (UA m (M.priceLaw P))).sum

/-- **Welfare without the contract** (§3.4, p.13: "the sum of utilities of all buyers and the
seller's revenue"). -/
noncomputable def welfare0 (m : RiskModel) (P : Measure Ω) (ω : Ω) : ℝ :=
  M.util0 m P ω + M.rev0 ω

/-- **The Market-Maker price offered: `p*_M` of the clearing-price law** (eq. (3), p.17). -/
noncomputable def mmPrice (m : RiskModel) (P : Measure Ω) : ℝ :=
  pStar m (M.priceLaw P)

open Classical in
/-- **Units bought through the Market-Maker contract at `p*_M`**: the units whose value `v`
satisfies the purchase rule `buysMM` (ties to the Market-Maker, p.18). -/
noncomputable def mmUnits (m : RiskModel) (P : Measure Ω) (ω : Ω) : List ℝ :=
  (M.units ω).filter fun v => decide (buysMM m (M.priceLaw P) (M.mmPrice m P) v)

open Classical in
/-- **Units that stay in the auction** when the contract is offered at `p*_M`. -/
noncomputable def restUnits (m : RiskModel) (P : Measure Ω) (ω : Ω) : List ℝ :=
  (M.units ω).filter fun v => !decide (buysMM m (M.priceLaw P) (M.mmPrice m P) v)

/-- **`ℓ`, the number of units sold through the Market-Maker contract** (proof of Theorem 3,
p.18: "the highest valued ℓ ≤ I buyers select the Market-Maker contract"). -/
noncomputable def nMM (m : RiskModel) (P : Measure Ω) (ω : Ω) : ℕ :=
  (M.mmUnits m P ω).length

/-- **Clearing price with the contract**: the remaining `I − ℓ` units are sold in the
`(I − ℓ + 1)`-th price auction among the units that did not buy the contract (proof of
Theorem 3, p.18: "I − ℓ buyers participate in the auction in P2"); `0` if at most `I − ℓ` such
units are demanded.

**Formalization Note** `I − ℓ` is truncated natural subtraction; Theorem 3 proves `ℓ ≤ I`
almost surely. -/
noncomputable def c1 (m : RiskModel) (P : Measure Ω) (ω : Ω) : ℝ :=
  (sortDesc (M.restUnits m P ω)).getD (M.I - M.nMM m P ω) 0

/-- **Efficiency with the contract**: the contract units plus the `I − ℓ` highest remaining
units. -/
noncomputable def eff1 (m : RiskModel) (P : Measure Ω) (ω : Ω) : ℝ :=
  (M.mmUnits m P ω).sum + ((sortDesc (M.restUnits m P ω)).take (M.I - M.nMM m P ω)).sum

/-- **Revenue with the contract**: `ℓ · p*_M` from the contract plus `(I − ℓ) · c₁` from the
auction (§3.4, p.13: "the sum of prices paid to the seller").

**Formalization Note** `(I − ℓ)` is the natural-number difference, cast to `ℝ`. -/
noncomputable def rev1 (m : RiskModel) (P : Measure Ω) (ω : Ω) : ℝ :=
  (M.nMM m P ω : ℝ) * M.mmPrice m P + ((M.I - M.nMM m P ω : ℕ) : ℝ) * M.c1 m P ω

open Classical in
/-- **Sum of the buyers' utilities with the contract**: a unit of value `v` that buys the
contract gets `U_buy(v, p*_M)` (eq. (15), p.37), every other unit gets `U_A(v)`. -/
noncomputable def util1 (m : RiskModel) (P : Measure Ω) (ω : Ω) : ℝ :=
  ((M.units ω).map fun v =>
    if buysMM m (M.priceLaw P) (M.mmPrice m P) v then Ubuy m v (M.mmPrice m P)
    else UA m (M.priceLaw P) v).sum

/-- **Welfare with the contract** (§3.4, p.13). -/
noncomputable def welfare1 (m : RiskModel) (P : Measure Ω) (ω : Ω) : ℝ :=
  M.util1 m P ω + M.rev1 m P ω

end Market

end MarketMakerAds


