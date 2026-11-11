-- Prove2me | Definitions.Def_StratifyMarkets_DoubleAuction_Bilateral
-- name    : StratifyMarkets_DoubleAuction_Bilateral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:52:29.961217+00:00
-- url     : https://prove2.me/theorems/95ffc672-6143-4139-80dc-8732f289d6d0
-- title:
--   Bilateral trade instances, first-best gains from trade, and seller-, buyer- and random-offerer profits (§2.1, Definition 2.1)
-- statement:
--   A **bilateral trade instance** consists of a buyer whose value $v$ has law $\mu_B$ (cumulative distribution function $F$) and a seller whose cost $c$ has law $\mu_S$ (CDF $G$). Both laws are continuous (they have no atoms) probability measures supported on $[0,1]$, and $v$ and $c$ are independent, so the joint law of $(c,v)$ is the product $\mu_S\otimes\mu_B$.
--
--   Write $\bar F(s)=\Pr[v\ge s]$ for the probability that the buyer's value is (at least) $s$, and $G(b)=\Pr[c\le b]$. The **first-best gains from trade** are
--   $$\mathrm{FB}=\mathbb E_{v,c}\big[(v-c)_+\big],$$
--   where $X_+=\max\{X,0\}$; this is the published definition `SecondBestBT.firstBest` evaluated at $(\mu_S,\mu_B)$.
--
--   In the **seller-pricing mechanism** the seller with cost $c$ posts a take-it-or-leave-it price; her conditional expected profit at a profit-maximizing price is
--   $$\mathrm{SellerProfit}(c)=\max_{s\in[0,1]}(s-c)\,\bar F(s),\qquad \mathrm{SellerProfit}=\int_0^1\mathrm{SellerProfit}(c)\,dG(c).$$
--   In the **buyer-pricing mechanism**, symmetrically,
--   $$\mathrm{BuyerProfit}(v)=\max_{b\in[0,1]}(v-b)\,G(b),\qquad \mathrm{BuyerProfit}=\int_0^1\mathrm{BuyerProfit}(v)\,dF(v).$$
--   The **random-offerer mechanism** (Definition 2.1) picks the proposer uniformly at random, and the proposer's expected profit is $\mathrm{ROProfit}=\tfrac12\mathrm{BuyerProfit}+\tfrac12\mathrm{SellerProfit}$.
--
--   These are the bilateral objects of Section 2.1 used by Theorem 2.2, Lemmas 3.3, 3.5, 3.6 and Theorem 3.1.
--
--   **Formalization Note.** `BTInstance` bundles `μB μS : Measure ℝ` with `IsProbabilityMeasure`, `NullSingletonClass` (no atoms) and `μ (Icc 0 1) = 1`. `Fbar s = (μB (Ici s)).toReal`, `G b = (μS (Iic b)).toReal`. The profits are `⨆ s : Icc 0 1, …`, a supremum over a nonempty set of a bounded function, attained because $\bar F$ and $G$ are continuous; this equals the paper's value $(s_c-c)\bar F(s_c)$ at any maximizer. `FB = SecondBestBT.firstBest μS μB = ∫ x, max (x.2 − x.1) 0 ∂(μS.prod μB)`, with `x = (c, v)`.
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), pp. 7–8, §2.1 and Definition 2.1

import Mathlib
import Definitions.Def_SecondBestBT_firstBest

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- A bilateral trade instance (Deng–Lin–Schoepflin–Wang, *Stratifying Markets for Efficient
Trade*, §2.1, p. 7): the buyer's value `v` has law `μB` (CDF `F`), the seller's cost `c` has law
`μS` (CDF `G`), and `v`, `c` are independent (the joint law is the product `μS.prod μB`, see
`BTInstance.law`). Both laws are continuous (no atoms) probability measures supported on `[0, 1]`,
the paper's standing assumption of §2.1. -/
structure BTInstance where
  /-- law of the buyer's value `v` (CDF `F`) -/
  μB : Measure ℝ
  /-- law of the seller's cost `c` (CDF `G`) -/
  μS : Measure ℝ
  isProb_B : IsProbabilityMeasure μB
  isProb_S : IsProbabilityMeasure μS
  noAtoms_B : NullSingletonClass μB
  noAtoms_S : NullSingletonClass μS
  support_B : μB (Set.Icc 0 1) = 1
  support_S : μS (Set.Icc 0 1) = 1

namespace BTInstance

/-- The joint law of `(c, v)`: the product of the seller's and the buyer's laws (independence).
A point `x : ℝ × ℝ` is read as `x.1 = c` (cost) and `x.2 = v` (value). -/
noncomputable def law (I : BTInstance) : Measure (ℝ × ℝ) := I.μS.prod I.μB

/-- The bilateral first-best gains from trade `FB = E_{v,c}[(v − c)_+]` (§2.1, p. 7), the published
definition `SecondBestBT.firstBest` (seller law first). -/
noncomputable def FB (I : BTInstance) : ℝ := SecondBestBT.firstBest I.μS I.μB

/-- `F̄(s) = Pr[v ≥ s]`, the probability that the buyer's value is (at least) `s` (§2.1, p. 7). -/
noncomputable def Fbar (I : BTInstance) (s : ℝ) : ℝ := (I.μB (Set.Ici s)).toReal

/-- `G(b) = Pr[c ≤ b]`, the seller's CDF. -/
noncomputable def G (I : BTInstance) (b : ℝ) : ℝ := (I.μS (Set.Iic b)).toReal

/-- `SellerProfit(c) = max_{s ∈ [0,1]} (s − c) · F̄(s)` (Definition 2.1 and p. 7): the seller's
conditional expected profit when she posts a profit-maximizing price `s_c`. The supremum is over the
nonempty compact `[0, 1]` of a bounded function, and is attained because `F̄` is continuous. -/
noncomputable def sellerProfitAt (I : BTInstance) (c : ℝ) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ) 1, ((s : ℝ) - c) * I.Fbar s

/-- `SellerProfit = ∫_0^1 SellerProfit(c) dG(c)` (p. 8). -/
noncomputable def sellerProfit (I : BTInstance) : ℝ := ∫ c, I.sellerProfitAt c ∂I.μS

/-- `BuyerProfit(v) = max_{b ∈ [0,1]} (v − b) · G(b)` (p. 8). -/
noncomputable def buyerProfitAt (I : BTInstance) (v : ℝ) : ℝ :=
  ⨆ b : Set.Icc (0 : ℝ) 1, (v - (b : ℝ)) * I.G b

/-- `BuyerProfit = ∫_0^1 BuyerProfit(v) dF(v)` (p. 8). -/
noncomputable def buyerProfit (I : BTInstance) : ℝ := ∫ v, I.buyerProfitAt v ∂I.μB

/-- `ROProfit = BuyerProfit / 2 + SellerProfit / 2` (p. 8): the expected profit of the proposer
of the random-offerer mechanism (Definition 2.1). -/
noncomputable def roProfit (I : BTInstance) : ℝ := I.buyerProfit / 2 + I.sellerProfit / 2

end BTInstance

end StratifyMarkets.DoubleAuction


