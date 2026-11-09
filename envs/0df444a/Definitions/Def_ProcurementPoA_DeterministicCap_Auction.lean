-- Prove2me | Definitions.Def_ProcurementPoA_DeterministicCap_Auction
-- name    : ProcurementPoA_DeterministicCap_Auction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:50.271656+00:00
-- url     : https://prove2.me/theorems/d6190714-0a7b-4b19-a413-f2c2dd7b4538
-- title:
--   Deterministic capped procurement auction and mixed BNE
-- statement:
--   Let independent private costs have laws $\mu_i$ on measurable domains $D_i\subseteq[L,U]$. A measurable tie rule takes the real bid vector and returns a probability law on lowest-bidding suppliers. It observes no private costs and may give any supplier priority.
--
--   For a cap $T$, a lowest bid is accepted exactly when it is at most $T$. The selected supplier receives her bid; other suppliers receive zero. If all bids exceed $T$, the buyer uses an outside option costing $U$. At own cost $c$ and pure bid $b$, interim utility is
--
--   $$u_i(c,b)=(b-c)\Pr(i\text{ selected}\mid b)\,\mathbf1_{b\le T}.$$
--
--   The probability integrates the independent opponents' mixed bid laws and the tie rule. A selected mixed Bayes–Nash equilibrium is a typewise best response with no used bid below own cost. Every real deviation is tested, including a bid below cost; bids are never restricted to $[L,U]$ or to the cap.
--
--   The social cost is the expectation of the accepted supplier's actual cost, or $U$ on rejection, averaging randomized ties explicitly. The benchmark is $\mathrm{SC}_{\mathrm{OPT}}=\mathbb E[\min_i c_i]$. These definitions provide the common auction model for both target statements.
--
--   **Formalization Note** Nonnegative expectations use extended nonnegative reals and Lebesgue integrals of nonnegative functions. On the stated positive bounded intervals these equal the usual finite expectations, so nonintegrable Bochner defaults cannot occur. The finite minimum has a nonempty index type. The rule is defined for every real $T$, even outside the phantom class $T\le U$.
-- source:
--   Simone Palazzotto, Andrés Cristi, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, §2, printed p. 4 (PDF p. 6); Definition 5.1 and normalization, printed p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_ProbabilityModel

namespace ProcurementPoA.DeterministicCap

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Costs belong to the specified positive interval in the theorem applications. -/
def InCostInterval {n : ℕ} (D : IndependentTypes n) (L U : ℝ) : Prop :=
  ∀ i, D.types i ⊆ Set.Icc L U

/-- Nonempty finite minimum, with no empty-minimum convention. -/
noncomputable def lowest {n : ℕ} (x : Suppliers n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty x

/-- An arbitrary measurable randomized tie rule, observing only the bid vector.
It always selects a lowest bidder, including off-equilibrium profiles. -/
structure TieRule (n : ℕ) where
  select : Kernel (Suppliers n → ℝ) (Suppliers n)
  markov : IsMarkovKernel select
  lowest_only : ∀ b, ∀ᵐ i ∂(select b), ∀ j, b i ≤ b j

instance {n : ℕ} (τ : TieRule n) : IsMarkovKernel τ.select := τ.markov

/-- Probability of winning at a pure bid, integrating the independent opponents'
marginal bid laws. The sampled own coordinate is overwritten and ignored. -/
noncomputable def interimWin {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (i : Suppliers n) (b : ℝ) : ENNReal :=
  ∫⁻ bs, τ.select (Function.update bs i b) {i} ∂(Measure.pi (marginalBidLaw D σ))

/-- The cap accepts equality. A rejected bid has zero utility, at any real bid. -/
noncomputable def interimUtility {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (T : ℝ) (i : Suppliers n) (c b : ℝ) : ℝ :=
  if b ≤ T then (b - c) * (interimWin D τ σ i b).toReal else 0

/-- No supplier uses a bid below her own cost. -/
def NoUnderbidding {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n) : Prop :=
  ∀ i, ∀ c ∈ D.types i, ∀ᵐ b ∂(σ.bid i c), c ≤ b

/-- The source's selected mixed BNE: actual interim best responses, with no
underbidding. Deviations include every real bid, including below-cost bids. -/
def IsBNE {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (T : ℝ) : Prop :=
  NoUnderbidding D σ ∧ IsTypewiseBestResponse D σ (interimUtility D τ σ T)

/-- Tie-averaged actual outcome cost, not payment: accepted supplier's cost,
or the outside option U. Bids equal to T are accepted. -/
noncomputable def outcomeCost {n : ℕ} (τ : TieRule n) (U T : ℝ)
    (x : Suppliers n → ℝ × ℝ) : ENNReal :=
  if lowest (fun i => (x i).2) ≤ T then
    ∑ i, ENNReal.ofReal (x i).1 * τ.select (fun j => (x j).2) {i}
  else ENNReal.ofReal U

/-- Actual expected social cost, including mixed actions and randomized ties. -/
noncomputable def socialCost {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (U T : ℝ) : ENNReal :=
  ∫⁻ x, outcomeCost τ U T x ∂(playLaw D σ)

/-- Expected minimum private cost, rather than an expected pointwise ratio. -/
noncomputable def optimalSocialCost {n : ℕ} (D : IndependentTypes n) : ENNReal :=
  ∫⁻ c, ENNReal.ofReal (lowest c) ∂(typeLaw D)

end ProcurementPoA.DeterministicCap


