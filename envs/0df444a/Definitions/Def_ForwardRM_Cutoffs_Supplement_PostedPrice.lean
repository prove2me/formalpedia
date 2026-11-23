-- Prove2me | Definitions.Def_ForwardRM_Cutoffs_Supplement_PostedPrice
-- name    : ForwardRM_Cutoffs_Supplement_PostedPrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:22:24.88697+00:00
-- url     : https://prove2.me/theorems/95524725-0b99-41e0-9016-8221074fabf8
-- title:
--   §5 and Lemma 7's proof — posted prices with a final second-price auction, buyer strategies, payoffs (A.9), seller revenue and equilibrium
-- statement:
--   The game is played in the discretized problem with $n$ periods of length $h=T/n$ and $K$ units.
--
--   A **posted-price policy** gives a price $p_i(H)$ for each period $i$ and each **public history** $H$, the list of how many units were sold in periods $1,\dots,i-1$. Prices are in time-$0$ units. The history also determines the announced inventory $\kappa=K-\sum H$. Prices may not depend on arrivals, values or reports.
--
--   The **mechanism** runs as follows. In period $i$ the Poisson cohort of that period arrives first. Then:
--
--   1. If no unit is left, nothing happens.
--   2. If $i=n$ and one unit is left, the seller runs a **second-price auction with reserve** $\rho=e^{-rT}m^{-1}(0)$, where $m^{-1}(0)$ is the root of $m$ on $[\underline v,\bar v]$. If a bid reaches $\rho$, the highest bidder wins and pays $\max\{\rho,\text{second-highest bid}\}$. Ties at the top are broken uniformly at random.
--   3. Otherwise the seller posts $p_i(H)$ and $d$ present buyers demand. If $d\le\kappa$, every demander pays and leaves with a unit, and play continues with $\kappa-d$ units and history $H$ followed by $d$. If $d>\kappa$, a uniformly random set of $\kappa$ demanders is served, so each demander is served with probability $\kappa/d$, and the units run out.
--
--   A **buyer strategy** is symmetric and pure. A buyer of value $v$ who entered in period $j$ and is still unserved decides, from $(v,j,H)$, whether to demand at the posted price and what to bid in the final auction. A bid below $\rho$ is the same as not bidding.
--
--   A buyer served in period $i$ gets $e^{-r\,ih}v$ minus his payment. His expected utility $u(v,j,\cdot)$ is (A.9). The expectation runs over the Poisson cohorts of the other buyers, which are those of the model and do not depend on his own entry, over their i.i.d. values, and over the rationing and tie-breaking lotteries. The **seller's revenue** is the expected sum of payments.
--
--   A strategy $\sigma$ is an **equilibrium** when three conditions hold:
--
--   1. $\sigma$ is measurable in the value.
--   2. Bids are bounded on $[\underline v,\bar v]$.
--   3. For every value $v\in[\underline v,\bar v]$, every entry period $j\in\{1,\dots,n\}$ and every alternative strategy $\tau$, the buyer of type $(v,j)$ playing $\tau$ while all others play $\sigma$ gets no more than he gets by playing $\sigma$.
--
--   This is the class of mechanisms and the solution concept of Theorem 3.
--
--   **Formalization Note** Expectations over a cohort are written as $E[g^+]-E[g^-]$, each a lower Lebesgue integral, so they equal the true expectation for the measurable and bounded payoffs that an equilibrium profile produces. For fixed $n,K$, only finitely many public sale histories are reachable, hence their prices are bounded. Equilibrium bids are uniformly bounded and values lie in a bounded interval almost surely; each fixed tagged deviation has finitely many reachable bids. Consequently both lower integrals are finite in the uses relevant to the theorem. On unrestricted inputs, the total helper can still send an infinite part to zero through `ENNReal.toReal`; the helper alone does not assert integrability. Only payments reach the seller, so revenue is the sum of payments and not of virtual values. An alternative strategy may be any function of the public history, which covers every purchase plan and every bid adapted to the buyer's information.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 19, §5 (posted prices); p. 38, proof of Lemma 7 (mechanism, reserve e^{−rT}m^{−1}(0), random rationing); p. 39, eq. (A.9); p. 7, eq. (2.2)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Supplement_ContinuousModel

namespace ForwardRM.Cutoffs.Supplement

open MeasureTheory ProbabilityTheory

/-- A posted-price policy (§5, p. 19; proof of Lemma 7, p. 38): the price, in time-`0` units, that
the seller posts in period `i` after the public history `H`. The public history is the list of the
numbers of units sold in periods `1, …, i − 1` (oldest first); it also determines the inventory
`K − ΣH` announced by the seller. The price depends on nothing else: not on arrivals, values or
reports of the buyers. -/
structure PostedPricePolicy where
  price : ℕ → List ℕ → ℝ

/-- A (symmetric, pure) buyer strategy. A buyer of value `v` who entered in period `j` and is still
unserved in period `i` acts on the public history `H` of periods `1, …, i − 1`:
* `demand v j H`: whether he asks to buy at the posted price of period `i`;
* `bid v j H`: his bid (time-`0` units) in the final second-price auction. A bid below the reserve
  never wins and does not affect the price, so it is the same as not bidding. -/
structure BuyerStrategy where
  demand : ℝ → ℕ → List ℕ → Bool
  bid : ℝ → ℕ → List ℕ → ℝ

/-- Where the one buyer whose payoff is being evaluated (the *tagged* buyer) stands: not yet
entered, present and unserved, or no longer in the market (served). -/
inductive TagStatus
  | waiting
  | present
  | gone
  deriving DecidableEq

/-- `E[g]` over the entrants of one period: their number has law `N` and their values are i.i.d.
with law `μ`. Written as `E[g⁺] − E[g⁻]`, each part a lower Lebesgue integral. For a probability
law `μ` and measurable, essentially bounded `g`, both parts are finite and this is the usual
expectation. In `IsEquilibrium`, finite reachable price histories and bounded equilibrium bids
give these bounds for the game payoffs, including each fixed tagged deviation. For unrestricted
inputs, `ENNReal.toReal` still sends infinity to zero; this total function alone supplies no
integrability or measurability assertion. -/
noncomputable def cohortExpect (N : PMF ℕ) (μ : Measure ℝ) (g : Multiset ℝ → ℝ) : ℝ :=
  (∑' k : ℕ, N k * ∫⁻ x : Fin k → ℝ, ENNReal.ofReal (g (cohort x)) ∂(Measure.pi fun _ => μ)).toReal
  - (∑' k : ℕ, N k * ∫⁻ x : Fin k → ℝ, ENNReal.ofReal (-g (cohort x)) ∂(Measure.pi fun _ => μ)).toReal

open Classical in
/-- The seller's revenue from a second-price auction with reserve `ρ` and bids `B`: if some bid
reaches `ρ`, the winner pays the larger of `ρ` and the second-highest bid; otherwise nothing is
sold. -/
noncomputable def auctionRevenue (ρ : ℝ) (B : Multiset ℝ) : ℝ :=
  if ∃ b ∈ B, ρ ≤ b then max ρ ((sortDesc B).getD 1 ρ) else 0

open Classical in
/-- The expected utility of a bidder with discounted value `w` (time-`0` units) who bids `b` in a
second-price auction with reserve `ρ` against the other bids `O`, ties at the top broken uniformly
at random: he wins iff `b ≥ ρ` and no other bid exceeds `b`, with probability `1/(1 + #ties)`, and
then pays the larger of `ρ` and the highest other bid. -/
noncomputable def auctionUtility (ρ w b : ℝ) (O : Multiset ℝ) : ℝ :=
  if ρ ≤ b ∧ ∀ o ∈ O, o ≤ b then
    (w - max ρ ((sortDesc O).headD ρ)) / ((Multiset.card (O.filter (· = b)) : ℝ) + 1)
  else 0

namespace ContinuousModel

variable (C : ContinuousModel)

/-- `m⁻¹(0)`: the root of the marginal revenue on `[v̲, v̄]` (unique, since `m` is continuous and
strictly increasing there with `m(v̲) < 0 < m(v̄)`). -/
noncomputable def mRoot : ℝ :=
  sInf {v | v ∈ Set.Icc C.vlo C.vhi ∧ 0 ≤ C.m v}

/-- The reserve `e^{−rT} m⁻¹(0)` of the final second-price auction (proof of Lemma 7, p. 38),
in time-`0` units. -/
noncomputable def reserve : ℝ :=
  Real.exp (-(C.r * C.T)) * C.mRoot

variable (n : ℕ) (hn : 1 ≤ n) (p : PostedPricePolicy) (σ τ : BuyerStrategy) (v : ℝ) (j : ℕ)

/-- The posted-price mechanism with a final auction (proof of Lemma 7, p. 38) in the discretized
problem with `n` periods, played by buyers who follow `σ`, plus one tagged buyer of value `v`
entering in period `j` who follows `τ`.

`stage rem κ H S st` is the pair (expected payments to the seller, expected utility of the tagged
buyer) from the start of period `i = n − rem` on, before the period-`i` entrants arrive, when `rem`
periods are left after it, `κ` units remain, the public history is `H`, the unserved buyers other
than the tagged one are `S` (value, entry period) and the tagged buyer's status is `st`.

In period `i`, after the Poisson cohort of period `i` (law `arrivals i`, i.i.d. values) arrives
(and the tagged buyer, if `i = j`):
* with no unit left nothing happens;
* if `i = n` and one unit is left, the seller runs a second-price auction with reserve
  `e^{−rT} m⁻¹(0)` among all present buyers; the tagged buyer's value is `e^{−rT} v`;
* otherwise she posts the price `p.price i H`; if `d` buyers demand and `d ≤ κ`, each pays the
  price and leaves with a unit, and play continues with `κ − d` units and history `H ++ [d]`; if
  `d > κ`, the `κ` units go to a uniformly random set of `κ` demanders (each, the tagged one
  included, is served with probability `κ/d`), and the units are exhausted. A buyer served in
  period `i` gets `e^{−r i h} v − price`. -/
noncomputable def stage : ℕ → ℕ → List ℕ → Multiset (ℝ × ℕ) → TagStatus → ℝ × ℝ
  | rem, κ, H, S, st =>
    let D := C.discretize n hn
    let i := n - rem
    let st' : TagStatus := if st = TagStatus.waiting ∧ j = i then TagStatus.present else st
    let act : Multiset (ℝ × ℕ) → ℝ × ℝ := fun S' =>
      if κ = 0 then (0, 0)
      else if i = n ∧ κ = 1 then
        let O := S'.map (fun b => σ.bid b.1 b.2 H)
        if st' = TagStatus.present then
          (auctionRevenue C.reserve (τ.bid v j H ::ₘ O),
            auctionUtility C.reserve (Real.exp (-(C.r * C.T)) * v) (τ.bid v j H) O)
        else (auctionRevenue C.reserve O, 0)
      else
        let q := p.price i H
        let Dm := S'.filter (fun b => σ.demand b.1 b.2 H = true)
        let t : Bool := st' = TagStatus.present ∧ τ.demand v j H = true
        let d : ℕ := Multiset.card Dm + (if t then 1 else 0)
        let w := Real.exp (-(C.r * ((i : ℝ) * C.step n))) * v
        if κ < d then
          (q * κ, if t then ((κ : ℝ) / d) * (w - q) else 0)
        else
          let now : ℝ × ℝ := (q * d, if t then w - q else 0)
          match rem with
          | 0 => now
          | rem' + 1 =>
            now + stage rem' (κ - d) (H ++ [d]) (S' - Dm) (if t then TagStatus.gone else st')
    (cohortExpect (D.arrivals i) D.law
        (fun c => (act (S + c.map (fun x => (x, i)))).1),
      cohortExpect (D.arrivals i) D.law
        (fun c => (act (S + c.map (fun x => (x, i)))).2))

/-- The seller's expected payments (time-`0` units, (2.2) p. 7) from the posted-price mechanism with
`K` units and a final auction when all buyers follow `σ`. -/
noncomputable def sellerRevenue (K : ℕ) : ℝ :=
  (C.stage n hn p σ σ 0 0 (n - 1) K [] 0 TagStatus.gone).1

/-- The expected utility `u(v, j, ·)` ((A.9), p. 39) of a buyer of value `v` entering in period `j`
who follows `τ` while every other buyer follows `σ`; he joins an otherwise unchanged Poisson
market. -/
noncomputable def buyerUtility (K : ℕ) : ℝ :=
  (C.stage n hn p σ τ v j (n - 1) K [] 0 TagStatus.waiting).2

/-- `σ` is an equilibrium of the posted-price mechanism `p` with `K` units: the strategy is
measurable in the value with bids bounded on `[v̲, v̄]` (so that every expected payment is an
honest integral), and no buyer type — any value `v ∈ [v̲, v̄]` and entry period
`j ∈ {1, …, n}` — gains by switching to any other strategy `τ` (any purchase plan and any bids
adapted to the public history), given that all other buyers follow `σ`. -/
def IsEquilibrium (K : ℕ) : Prop :=
  (∀ j H, Measurable fun v => σ.demand v j H) ∧
  (∀ j H, Measurable fun v => σ.bid v j H) ∧
  (∃ B : ℝ, ∀ v ∈ Set.Icc C.vlo C.vhi, ∀ j H, |σ.bid v j H| ≤ B) ∧
  ∀ v ∈ Set.Icc C.vlo C.vhi, ∀ j, 1 ≤ j → j ≤ n → ∀ τ : BuyerStrategy,
    C.buyerUtility n hn p σ τ v j K ≤ C.buyerUtility n hn p σ σ v j K

end ContinuousModel

end ForwardRM.Cutoffs.Supplement


