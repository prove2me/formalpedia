-- Prove2me | Definitions.Def_SpilloverDuopoly_Switchers_Supplement_ThreePeriod
-- name    : SpilloverDuopoly_Switchers_Supplement_ThreePeriod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:37:46.905847+00:00
-- url     : https://prove2.me/theorems/49a35318-a5cd-4520-8146-559c0df79380
-- title:
--   Appendix D.2, pp. 51–53 — the three-period four-firm game: history segments, π_i^k, π_i^{kl}, profit (30) and Π₁ of (31)
-- statement:
--   The payoff interface for the three-period four-firm game. A first-period purchase is $k\in\{1,2,3,4\}$; the second choice is $l\in\{0,1,2,3,4\}$, with $l=0$ denoting the outside option. For each preceding second-period offer profile $o$, terminal demand and offers may change with the distribution selected into $(k,l)$. All quantities are measured per unit of initial share $\lambda_k$.
--
--   Let $\pi_i^k$ and $\pi_i^{kl}$ be margins times period-2 and selected terminal demand. The original total profit is
--   $$\lambda_i(p)(p_i-c)+\delta\sum_k\lambda_k(p)\pi_i^k+\delta^2\sum_k\lambda_k(p)\sum_{l=0}^4\pi_i^{kl},\qquad \Pi_i=\pi_i^i+\delta\sum_{l=0}^4\pi_i^{il}.$$
--   A continuation equilibrium requires terminal Nash play after every period-2 offer profile and period-2 Nash play accounting for these contingent responses. A symmetric first-period equilibrium forbids every unilateral real-price deviation.
--
--   **Formalization Note** SourceThreePeriod instantiates these interfaces by integrals of optimal, information-respecting consumer choices. Neither switching-profit cancellation nor (31) is imposed as an equilibrium condition. The unused abstract period-2 substitution and on-path-only symmetry predicates have been removed.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), pp. 51–54 (PDF 53–56), Appendix D.2, eqs. (30)–(31)

import Mathlib
import Definitions.Def_ImbalPricing_IsPureNash
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_PricingGames

namespace SpilloverDuopoly.Switchers.Supplement

open Finset

/-- The payoff interface for the three-period four-firm game of Appendix D.2 (pp. 51–54 (PDF 53–56)); firms are `Fin 4`
(the paper's firm `1` is `0`). A first-period segment is `k`; a second-period history is `(k, l)`
with `l : Option (Fin 4)`, where `none` is the paper's `l = 0` (outside option in period 2).

* `demand2 k`: period-2 demand of segment `k` per unit of `λ_k`; `demand2 k o l` is the mass that
  chooses `l` in period 2 (consumers are forward-looking: this is the demand given the anticipated
  period-3 play);
* `demand3 k o l`: period-3 demand from history `(k, l)` after period-2 offers `o`,
  measured per unit of the initial share `λ_k`. Its consumer composition may change with `o`. -/
structure ThreePeriod extends FirstPeriod (Fin 4) where
  demand2 : Fin 4 → SegmentDemand (Fin 4)
  demand3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → SegmentDemand (Fin 4)

namespace ThreePeriod

/-- The firms whose product segment `(k, l)` has not tried. -/
def untried3 (k : Fin 4) (l : Option (Fin 4)) : Finset (Fin 4) :=
  (univ.erase k).filter (fun j => l ≠ some j)

/-- Firm `j`'s third-period profit from history `(k, l)` after period-2 offers `o2`,
per unit of initial share `λ_k`. The selected distribution depends on `o2`. -/
def termProfit (G : ThreePeriod) (k : Fin 4) (o2 : Fin 4 → Offer)
    (l : Option (Fin 4)) (o : Fin 4 → Offer)
    (j : Fin 4) : ℝ :=
  margin G.c (o j) * G.demand3 k o2 l o (some j)

/-- `o` is an equilibrium of the third-period pricing game of segment `(k, l)`. -/
def IsTermEq (G : ThreePeriod) (k : Fin 4) (o2 : Fin 4 → Offer)
    (l : Option (Fin 4)) (o : Fin 4 → Offer) : Prop :=
  ImbalPricing.IsPureNash (fun _ => Set.univ) (fun j o' => G.termProfit k o2 l o' j) o

/-- `π_i^{kl}`: firm `i`'s third-period profit from segment `(k, l)` per unit of `λ_k`, given the
period-2 offers `o2` and period-3 offers `o3`. -/
def piKL (G : ThreePeriod) (o2 : Fin 4 → Fin 4 → Offer)
    (o3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → Fin 4 → Offer) (i k : Fin 4) (l : Option (Fin 4)) : ℝ :=
  G.termProfit k (o2 k) l (o3 k (o2 k) l) i

/-- `π_i^k`: firm `i`'s second-period profit from segment `k`, per unit of `λ_k`. -/
def piK (G : ThreePeriod) (o2 : Fin 4 → Fin 4 → Offer) (i k : Fin 4) : ℝ :=
  margin G.c (o2 k i) * G.demand2 k (o2 k) (some i)

/-- Firm `i`'s payoff in the period-2 game of segment `k` at period-2 offers `o`, with period-3
play `o3`: period-2 profit plus the discounted period-3 profits from all segments `(k, l)`. -/
def secondPayoff (G : ThreePeriod) (o3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → Fin 4 → Offer) (k : Fin 4)
    (o : Fin 4 → Offer) (i : Fin 4) : ℝ :=
  margin G.c (o i) * G.demand2 k o (some i) +
    G.delta * ∑ l, G.termProfit k o l (o3 k o l) i

/-- Continuation equilibrium: every period-3 segment game after every period-2 offer profile
is in equilibrium, and every period-2
segment game is in equilibrium given the period-3 play. -/
def IsContEq (G : ThreePeriod) (o2 : Fin 4 → Fin 4 → Offer)
    (o3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → Fin 4 → Offer) : Prop :=
  (∀ k o l, G.IsTermEq k o l (o3 k o l)) ∧
    ∀ k, ImbalPricing.IsPureNash (fun _ => Set.univ) (fun i o => G.secondPayoff o3 k o i) (o2 k)

/-- `Π_i` of equation (31): firm `i`'s profits after the first period from the consumers who
tried product `i` first, valued at period 2: `π_i^i + δ ∑_{l=0}^{4} π_i^{il}`. -/
def Pi (G : ThreePeriod) (o2 : Fin 4 → Fin 4 → Offer)
    (o3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → Fin 4 → Offer) (i : Fin 4) : ℝ :=
  G.piK o2 i i + G.delta * ∑ l, G.piKL o2 o3 i i l

/-- Firm `i`'s overall three-period profit (30) at first-period prices `p`:
`λ_i (p_i - c) + δ ∑_k λ_k π_i^k + δ² ∑_k λ_k ∑_{l=0}^{4} π_i^{kl}`. -/
noncomputable def profit (G : ThreePeriod) (o2 : Fin 4 → Fin 4 → Offer)
    (o3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → Fin 4 → Offer) (p : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  G.share p i * (p i - G.c) + G.delta * ∑ k, G.share p k * G.piK o2 i k +
    G.delta ^ 2 * ∑ k, G.share p k * ∑ l, G.piKL o2 o3 i k l

/-- A symmetric first-period equilibrium at the common price `p`, given the continuation play. -/
def IsSymFirstEq (G : ThreePeriod) (o2 : Fin 4 → Fin 4 → Offer)
    (o3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → Fin 4 → Offer) (p : ℝ) : Prop :=
  ImbalPricing.IsPureNash (fun _ => Set.univ) (fun i q => G.profit o2 o3 q i) (fun _ => p)

end ThreePeriod

end SpilloverDuopoly.Switchers.Supplement


