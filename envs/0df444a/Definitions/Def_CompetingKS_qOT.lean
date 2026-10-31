-- Prove2me | Definitions.Def_CompetingKS_qOT
-- name    : CompetingKS_qOT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:02.359003+00:00
-- url     : https://prove2.me/theorems/7917c491-fd83-48a8-b886-15766bd22a40
-- title:
--   The retail stage: linear demand, the Cournot and common-retailer problems, $q^*$, $p^*$ and the trade profits (3)
-- statement:
--   Two products or stores compete under the linear inverse demand
--   $$
--   p_i(q_i,q_j)=a-bq_i-\eta bq_j,\qquad i\ne j,
--   $$
--   where $a>c$, $b>0$ and $\eta\in[0,1]$ measures substitutability. Given wholesale prices $w=(w_i,w_j)$, selling $q_i$ units in channel $i$ earns $(p_i(q_i,q_j)-w_i)q_i$.
--
--   In the **one-to-two channel** two competing retailers choose $q_i,q_j\ge0$ simultaneously, and the retail stage is the pure Nash equilibrium of this quantity game. In the **two-to-one channel** one common retailer chooses both quantities $q_i,q_j\ge0$ to maximize the sum of the two profits.
--
--   The module defines these two retail problems and the closed forms $q^*_i(w)$ of Lemma 1. With $x=a-w_i$ and $y=a-w_j$, the one-to-two quantity is $0$ if $2x\le\eta y$, it is $x/(2b)$ if $2y\le\eta x$, and otherwise
--   $$
--   q^*_i(w)=\frac{2x-\eta y}{b(4-\eta^2)};
--   $$
--   the two-to-one quantity is $0$ if $x\le\eta y$, it is $x/(2b)$ if $y\le\eta x$, and otherwise
--   $$
--   q^*_i(w)=\frac{x-\eta y}{2b(1-\eta^2)}.
--   $$
--   The retail price is the demand price at these quantities, $p^*_i(w)=a-bq^*_i(w)-\eta bq^*_j(w)$, and the profits from trade $i$ are
--   $$
--   R_i(w_i,w_j)=q^*_i(w)(w_i-c),\qquad r_i(w_i,w_j)=q^*_i(w)(p^*_i(w)-w_i).
--   $$
--
--   This is the second stage of the model: every profit in the bargaining problems is computed through it, and Lemma 1 proves that these closed forms solve the retail problems.
--
--   **Formalization Note** Quantities in the retail problems are `ℝ≥0`, and the general equilibrium notion is the published `CompetingChains.Cournot.IsPureNash`. The case conditions have cleared denominators, so they stay meaningful at $w_j=a$ and at $\eta=0$, where the printed $2/\eta$ would be read as $0$ by Lean. Prices are defined from the demand, so the price formulas of Lemma 1 are results. The two-to-one channel is only used for $\eta<1$.
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, §4, pp.13–14, inverse demand, Lemma 1, (3)

import Mathlib
import Definitions.Def_CompetingChains_Cournot_TwoPlayerGame

open scoped NNReal

namespace CompetingKS

/-- The linear inverse demand of Feng, Li, Shanthikumar, *Negotiations in Competing Supply Chains:
The Kalai-Smorodinsky Bargaining Solution*, accepted manuscript (Management Science, July 3, 2021),
SSRN 3447674, §4, p.13: the price of the product in channel `i`, given the quantity `qi` in channel
`i` and the quantity `qj` in the other channel, is `pᵢ(qᵢ, qⱼ) = a - b qᵢ - η b qⱼ`. -/
def price (a b η qi qj : ℝ) : ℝ := a - b * qi - η * b * qj

/-- The profit `(pᵢ(qᵢ, qⱼ) - wᵢ) qᵢ` from selling `qᵢ` units of channel `i` bought at wholesale
price `wᵢ`, the other channel selling `qⱼ` (Feng, Li, Shanthikumar, SSRN 3447674, p.13). -/
def retailPayoff (a b η w qi qj : ℝ) : ℝ := (price a b η qi qj - w) * qi

/-- The retail stage of the one-to-two channel (Feng, Li, Shanthikumar, SSRN 3447674, p.13): two
competing retailers choose nonnegative quantities, each maximizing its own profit, so the outcome
is a pure Nash equilibrium of the quantity game.

**Formalization Note** The general notion is the published `CompetingChains.Cournot.IsPureNash`;
strategies are nonnegative reals `ℝ≥0`. -/
def IsRetailEqOT (a b η wi wj : ℝ) (qi qj : ℝ≥0) : Prop :=
  CompetingChains.Cournot.IsPureNash
    (fun x y : ℝ≥0 => retailPayoff a b η wi x y) (fun x y : ℝ≥0 => retailPayoff a b η wj y x) qi qj

/-- The retail stage of the two-to-one channel (Feng, Li, Shanthikumar, SSRN 3447674, p.13): the
common retailer chooses both nonnegative quantities to maximize the total profit of the two
products. -/
def IsRetailOptTO (a b η wi wj : ℝ) (qi qj : ℝ≥0) : Prop :=
  ∀ x y : ℝ≥0, retailPayoff a b η wi x y + retailPayoff a b η wj y x ≤
    retailPayoff a b η wi qi qj + retailPayoff a b η wj qj qi

/-- The retail quantity `q*ᵢ(w)` of the one-to-two channel, Lemma 1(i) of Feng, Li, Shanthikumar,
SSRN 3447674, p.13.

**Formalization Note** The three cases of Lemma 1 are written with cleared denominators:
`(a-wᵢ)/(a-wⱼ) ≤ η/2` is `2(a-wᵢ) ≤ η(a-wⱼ)` and `(a-wᵢ)/(a-wⱼ) ≥ 2/η` is
`η(a-wᵢ) ≥ 2(a-wⱼ)`. These agree with the printed ratios when `wⱼ < a` and `η > 0`, and stay
meaningful at `wⱼ = a` and at `η = 0`, where Lean's `x / 0 = 0` would make the printed form wrong.
`lemma_1` proves that these are the equilibrium quantities. -/
noncomputable def qOT (a b η wi wj : ℝ) : ℝ :=
  if 2 * (a - wi) ≤ η * (a - wj) then 0
  else if 2 * (a - wj) ≤ η * (a - wi) then (a - wi) / (2 * b)
  else (2 * (a - wi) - η * (a - wj)) / (b * (4 - η ^ 2))

/-- The retail quantity `q*ᵢ(w)` of the two-to-one channel, Lemma 1(ii) of Feng, Li, Shanthikumar,
SSRN 3447674, p.14. Cases with cleared denominators, as in `qOT`.

**Formalization Note** The two-to-one channel is only used for `η < 1`: at `η = 1` the common
retailer is indifferent between splits at `wᵢ = wⱼ` and the printed cases (a), (c) disagree there,
so `q*` is not a function. -/
noncomputable def qTO (a b η wi wj : ℝ) : ℝ :=
  if a - wi ≤ η * (a - wj) then 0
  else if a - wj ≤ η * (a - wi) then (a - wi) / (2 * b)
  else ((a - wi) - η * (a - wj)) / (2 * b * (1 - η ^ 2))

/-- The retail price `p*ᵢ(w)` of the one-to-two channel: the demand price at the equilibrium
quantities. Lemma 1's price formulas are consequences (`lemma_1`), not definitions. -/
noncomputable def priceOT (a b η wi wj : ℝ) : ℝ :=
  price a b η (qOT a b η wi wj) (qOT a b η wj wi)

/-- The retail price `p*ᵢ(w)` of the two-to-one channel: the demand price at the optimal
quantities. -/
noncomputable def priceTO (a b η wi wj : ℝ) : ℝ :=
  price a b η (qTO a b η wi wj) (qTO a b η wj wi)

/-- The supplier's profit `Rᵢ(wᵢ, wⱼ) = q*ᵢ(w)(wᵢ - c)` from trade `i` in the one-to-two channel,
display (3) of Feng, Li, Shanthikumar, SSRN 3447674, p.14. -/
noncomputable def ROT (a b c η wi wj : ℝ) : ℝ := qOT a b η wi wj * (wi - c)

/-- The retailer's profit `rᵢ(wᵢ, wⱼ) = q*ᵢ(w)(p*ᵢ(w) - wᵢ)` from trade `i` in the one-to-two
channel, display (3). -/
noncomputable def rOT (a b η wi wj : ℝ) : ℝ := qOT a b η wi wj * (priceOT a b η wi wj - wi)

/-- The supplier's profit `Rᵢ(wᵢ, wⱼ)` from trade `i` in the two-to-one channel, display (3). -/
noncomputable def RTO (a b c η wi wj : ℝ) : ℝ := qTO a b η wi wj * (wi - c)

/-- The retailer's profit `rᵢ(wᵢ, wⱼ)` from trade `i` in the two-to-one channel, display (3). -/
noncomputable def rTO (a b η wi wj : ℝ) : ℝ := qTO a b η wi wj * (priceTO a b η wi wj - wi)

end CompetingKS


