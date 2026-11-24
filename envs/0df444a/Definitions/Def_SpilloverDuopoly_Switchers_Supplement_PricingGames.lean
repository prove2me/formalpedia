-- Prove2me | Definitions.Def_SpilloverDuopoly_Switchers_Supplement_PricingGames
-- name    : SpilloverDuopoly_Switchers_Supplement_PricingGames
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:36:34.484954+00:00
-- url     : https://prove2.me/theorems/711ba511-febc-4748-9e5e-80bbf0c989b4
-- title:
--   Appendix D, pp. 50–52 — segment offers, untried products as perfect substitutes, and the N-firm first-period share rule
-- statement:
--   This file collects the objects shared by the $N$-firm extensions of Appendix D.
--
--   **Offers and margins.** In the second and later periods a firm makes an offer to each consumer segment (consumers with a given purchase history): either a price $q\in\mathbb R$ or no sale. The margin of an offer at marginal cost $c$ is $q-c$ (and $0$ for no sale).
--
--   **Segment demand.** A segment demand $d$ assigns to every offer profile $o$ the mass $d(o)(j)$ of the segment buying firm $j$'s product and the mass choosing the outside option.
--
--   **Untried products are perfect substitutes.** For a set $U$ of firms whose products the segment has not tried, $d$ satisfies:
--
--   1. $d\ge 0$;
--   2. a firm that makes no offer sells nothing;
--   3. a firm in $U$ whose price is strictly above that of another firm in $U$ sells nothing;
--   4. a firm in $U$ that posts a price strictly below every other price in $U$ (and not above its own) sells at least the total mass that all of $U$ sold before.
--
--   These are the properties the paper uses when it says that "all of the untried products are valued equally by a consumer … each of them strictly prefers the cheapest untried product should they choose to switch."
--
--   **First period.** All products are ex-ante identical: a consumer who buys at price $p$ gets surplus $V-p$, and $u_0$ is the value of not buying. At a price vector $p$ the best acceptable offers are the cheapest firms, provided $V-p_j\ge u_0$. Tied best offers split the market by a tie rule: the firms in a tied set $S$ receive shares $\mathrm{tie}(S,j)\ge 0$ that sum to one; all other firms get zero. The common-price shares are $\lambda_j=\mathrm{tie}(\{1,\dots,N\},j)$, so any vector of market shares $\lambda_j\in[0,1]$ with $\sum_j\lambda_j=1$, zero entries allowed, is admissible. The standing assumptions are $c\ge 0$ and $\delta\in[0,1]$.
--
--   **Formalization Note** Equilibria elsewhere use the published `ImbalPricing.IsPureNash` with unrestricted strategy sets.
--
--   **Boundary specialization.** `zeroDiscountFirstPeriod(mu)` sets $c=\delta=0$, $V=\mu$, $u_0=0$ and equal shares among tied firms. `zeroDiscountProfit` is first-period revenue: later profits have zero present-value weight. This is used to refute the printed Theorem D.3.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), pp. 6, 49–52 (PDF 8, 51–54), §2 and Appendix D.1–D.2

import Mathlib

namespace SpilloverDuopoly.Switchers.Supplement

open Finset

/-- An offer of a firm to one consumer segment in one period: `some q` posts the price `q ∈ ℝ`,
`none` means the firm does not sell to the segment (Lemma D.1's "not sell", Chen–Stanton–Thomas,
accepted manuscript, p. 52 (PDF 54)). -/
abbrev Offer := Option ℝ

/-- Per-unit margin of an offer at marginal cost `c`: `q - c` for the price `q`, and `0` for no
sale (the demand of a firm that does not sell is zero, so the value is immaterial). -/
def margin (c : ℝ) : Offer → ℝ
  | some q => q - c
  | none => 0

/-- Demand of a consumer segment in one period: at the offer profile `o`, `d o (some j)` is the mass
of the segment buying firm `j`'s product and `d o none` the mass choosing the outside option. -/
abbrev SegmentDemand (ι : Type*) := (ι → Offer) → Option ι → ℝ

/-- The products of the firms in `U` (the products the segment has not tried) are perfect
substitutes for the segment (Appendix D.1, p. 50 (PDF 52): "all of the untried products are valued
equally by a consumer … each of them strictly prefers the cheapest untried product should they
choose to switch"; proof of Lemma D.2, p. 52 (PDF 54)):

1. demand is nonnegative;
2. a firm that does not sell has no demand;
3. an untried firm whose price is strictly above another untried firm's price sells nothing;
4. an untried firm that undercuts every other untried price (and does not raise its own) captures
   at least the whole demand that all untried products had before. -/
structure UntriedSubstitutes {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Finset ι)
    (d : SegmentDemand ι) : Prop where
  nonneg : ∀ o x, 0 ≤ d o x
  no_sale : ∀ o j, o j = none → d o (some j) = 0
  cheapest_only : ∀ (o : ι → Offer) (j j' : ι) (q q' : ℝ), j ∈ U → j' ∈ U →
    o j = some q → o j' = some q' → q' < q → d o (some j) = 0
  undercut : ∀ (o : ι → Offer) (j : ι) (q : ℝ), j ∈ U →
    (∀ j' ∈ U, j' ≠ j → ∀ q', o j' = some q' → q < q') →
    (∀ q', o j = some q' → q ≤ q') →
    ∑ j' ∈ U, d o (some j') ≤ d (Function.update o j (some q)) (some j)

/-- The first-period price game among the firms `ι` (Theorem 1's first period, extended to `N`
firms in Appendix D): common marginal cost `c`, discount factor `δ`, consumers' gross present value
`V` of a first-period purchase of any (ex-ante identical) product, present value `u0` of not buying,
and a tie-share rule: `tie S j` is firm `j`'s first-period market share when the firms in `S` tie
as the best acceptable offers. -/
structure FirstPeriod (ι : Type*) where
  c : ℝ
  delta : ℝ
  V : ℝ
  u0 : ℝ
  tie : Finset ι → ι → ℝ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Standing assumptions: `c ≥ 0`, `δ ∈ [0,1]` (§2, p. 6 (PDF 8)), and an admissible tie rule: tie
shares are nonnegative and the shares of every nonempty tied set sum to one (zero shares allowed). -/
def FirstPeriod.Standing (G : FirstPeriod ι) : Prop :=
  0 ≤ G.c ∧ 0 ≤ G.delta ∧ G.delta ≤ 1 ∧ (∀ S j, 0 ≤ G.tie S j) ∧
    ∀ S : Finset ι, S.Nonempty → ∑ j ∈ S, G.tie S j = 1

/-- The best acceptable first-period offers at the price vector `p`: the firms with the lowest
price, provided that price leaves surplus `V - p j ≥ u0`. -/
noncomputable def FirstPeriod.best (G : FirstPeriod ι) (p : ι → ℝ) : Finset ι :=
  univ.filter (fun j => G.u0 ≤ G.V - p j ∧ ∀ j', p j ≤ p j')

/-- Firm `j`'s first-period market share at prices `p`: consumers buy the cheapest acceptable
product; tied best offers split the market by the tie rule; otherwise the share is zero. -/
noncomputable def FirstPeriod.share (G : FirstPeriod ι) (p : ι → ℝ) (j : ι) : ℝ :=
  if j ∈ G.best p then G.tie (G.best p) j else 0

/-- The market shares `λ_j = tie univ j` when all firms charge the same acceptable price. -/
def FirstPeriod.lam (G : FirstPeriod ι) (j : ι) : ℝ := G.tie univ j

/-- The `T = N = 2`, `c = δ = 0` boundary of Theorem D.3. Before any trial all consumers
value either product at its mean `mu`; the outside option has value zero. At zero discount
the continuation has zero present value, independently of its equilibrium prices and learning.
Equal tie shares are one of the source's admissible symmetric allocations. -/
noncomputable def zeroDiscountFirstPeriod (mu : ℝ) : FirstPeriod (Fin 2) where
  c := 0
  delta := 0
  V := mu
  u0 := 0
  tie := fun S _ => 1 / (S.card : ℝ)

/-- Total discounted profit at `c = δ = 0`: only the initial margin contributes. -/
noncomputable def zeroDiscountProfit (G : FirstPeriod (Fin 2)) (p : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  G.share p i * p i

end SpilloverDuopoly.Switchers.Supplement


