-- Prove2me | Definitions.Def_BudgetedAuctionLearning_Robustness_RepeatedRun
-- name    : BudgetedAuctionLearning_Robustness_RepeatedRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:38.342878+00:00
-- url     : https://prove2.me/theorems/30784d62-e22f-47df-b991-95ed6b447529
-- title:
--   §§3, 5.1 — adaptive randomized optimizer, trajectory, budget constraint and expected total value
-- statement:
--   An optimizer strategy consists of an internal seed $s$ with law $\nu$ and, for each round, a jointly measurable bid $b_O^{(t)}=\pi_t(s,(v^{(1)},\dots,v^{(t-1)}),v_O^{(t)})\ge0$. It may use the seed, all earlier value pairs and her own current value, but not the learner's current value or future draws. The learner's multiplier is a function of the same data, so the optimizer knows it.
--
--   Value pairs are i.i.d. with law $D$ and independent of the seed. Along the induced trajectory the learner bids $\lambda^{(t)}v_L^{(t)}$ and the controller (3) runs on the actual payments. The optimizer's budget constraint requires total payment at most $T\rho_O$ with probability one. Her objective is the expected accumulated value
--
--   $$E\Big[\sum_{t=1}^Tv_O^{(t)}\mathbf 1\{b_O^{(t)}>b_L^{(t)}\}\Big],$$
--
--   not value minus payment. This is the adversary class of the main theorem.
--
--   **Formalization Note.** The seed space is an arbitrary measurable space, which includes every randomized strategy. Rounds are $0$-indexed. The expectation is a lower Lebesgue integral of a measurable nonnegative function.
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), §3, printed p. 7 (PDF p. 8); §5.1, printed p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_AuctionModel
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- An adaptive randomized optimizer. In round `t` (0-based) her bid is a jointly measurable function
of an internal seed in `S`, the values of all earlier rounds (both coordinates), and her own current
value. It sees neither the learner's current value nor future draws. The multiplier is a function of
this data, so it need not be a separate input. Bids are not capped by values. -/
structure OptimizerPolicy (S : Type) [MeasurableSpace S] where
  bid : (t : ℕ) → S × (Fin t → ValuePair) × I → ℝ≥0
  measurable_bid : ∀ t, Measurable (bid t)

/-- The optimizer's actual bid in round `t` on the sample path `(s, v)`. -/
def OptimizerPolicy.bidAt {S : Type} [MeasurableSpace S] (π : OptimizerPolicy S) (s : S)
    (v : ℕ → ValuePair) (t : ℕ) : ℝ≥0 :=
  π.bid t (s, (fun i : Fin t => v i), (v t).2)

/-- The learner's multiplier along the sample path `(s, v)`: the controller (3) run on the
optimizer's actual bids and the learner's realized values. -/
noncomputable def runPacing (fmt : AuctionFormat) (ρL η lam₁ : ℝ) {S : Type} [MeasurableSpace S]
    (π : OptimizerPolicy S) (s : S) (v : ℕ → ValuePair) : ℕ → ℝ :=
  pacingController fmt ρL η lam₁ (π.bidAt s v) (fun t => (v t).1)

/-- The learner's actual bid `λ^(t) v_L^(t)`. -/
noncomputable def runLearnerBid (fmt : AuctionFormat) (ρL η lam₁ : ℝ) {S : Type} [MeasurableSpace S]
    (π : OptimizerPolicy S) (s : S) (v : ℕ → ValuePair) (t : ℕ) : ℝ :=
  runPacing fmt ρL η lam₁ π s v t * ((v t).1 : ℝ)

/-- The optimizer's accumulated value over the first `T` rounds: `∑ v_O 1{O wins}` at actual bids. -/
noncomputable def runValue (fmt : AuctionFormat) (ρL η lam₁ : ℝ) {S : Type} [MeasurableSpace S]
    (π : OptimizerPolicy S) (T : ℕ) (s : S) (v : ℕ → ValuePair) : ℝ :=
  ∑ t ∈ Finset.range T, ((v t).2 : ℝ) *
    if runLearnerBid fmt ρL η lam₁ π s v t < (π.bidAt s v t : ℝ) then 1 else 0

/-- The optimizer's total payment over the first `T` rounds, at actual bids. -/
noncomputable def runOptimizerPayment (fmt : AuctionFormat) (ρL η lam₁ : ℝ) {S : Type}
    [MeasurableSpace S] (π : OptimizerPolicy S) (T : ℕ) (s : S) (v : ℕ → ValuePair) : ℝ :=
  ∑ t ∈ Finset.range T, auctionPayO fmt (π.bidAt s v t) (runLearnerBid fmt ρL η lam₁ π s v t)

/-- The law of the value sequence: i.i.d. across rounds with law `D`. -/
noncomputable def pathLaw (D : Measure ValuePair) : Measure (ℕ → ValuePair) :=
  Measure.infinitePi fun _ => D

/-- The optimizer's budget constraint: total payment at most `T ρ_O` with probability `1`, under the
seed law `ν` (independent of the values) and the i.i.d. value law. -/
def OptimizerBudgetFeasible (fmt : AuctionFormat) (D : Measure ValuePair) (ρL ρO η lam₁ : ℝ) {S : Type}
    [MeasurableSpace S] (ν : Measure S) (π : OptimizerPolicy S) (T : ℕ) : Prop :=
  ∀ᵐ ω ∂(ν.prod (pathLaw D)), runOptimizerPayment fmt ρL η lam₁ π T ω.1 ω.2 ≤ (T : ℝ) * ρO

/-- The optimizer's expected total value over the induced trajectory law. -/
noncomputable def expectedOptimizerValue (fmt : AuctionFormat) (D : Measure ValuePair) (ρL η lam₁ : ℝ)
    {S : Type} [MeasurableSpace S] (ν : Measure S) (π : OptimizerPolicy S) (T : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (runValue fmt ρL η lam₁ π T ω.1 ω.2) ∂(ν.prod (pathLaw D))

end BudgetedAuctionLearning.Robustness


