-- Prove2me | Definitions.Def_CtxSearchTSR_Supplement_Algorithm3
-- name    : CtxSearchTSR_Supplement_Algorithm3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:21:41.613349+00:00
-- url     : https://prove2.me/theorems/3cb1cfb4-271c-417c-8b5f-fc70cd374bf6
-- title:
--   Algorithm 3 (Bayesian Contextual Bilateral Trade): price rules with (17), posterior, run and expected total loss
-- statement:
--   **Lemma 3.1** of the paper asserts that for every pair $(S,B)$ of square-integrable reals there is a common price $p$ with
--
--   $$L(p)\le 2^{11}D(p),\qquad (17)$$
--
--   and that the price can be chosen as a function of the joint distribution. A **price rule** $\rho$ maps a joint law $\mu$ of $(S,B)$ to a price; it **satisfies (17)** if $L_\mu(\rho(\mu))\le 2^{11}D_\mu(\rho(\mu))$ for every probability measure $\mu$ on $\mathbb R^2$ with square-integrable coordinates.
--
--   **Algorithm 3** with a price rule $\rho$ starts from the prior $\pi_1=\pi$ of $(s,b)$. In round $t$ it receives $x_t$, posts $p_t=\rho\big(\text{law of }(x_t^\top s,x_t^\top b)\text{ under }\pi_t\big)$, observes $Y_t=\mathbf 1\{x_t^\top s\le p_t\le x_t^\top b\}$, and sets $\pi_{t+1}$ to $\pi$ conditioned on the pairs consistent with all observed trade bits. The loss is $\ell_t=(x_t^\top(b-s))_+(1-Y_t)$.
--
--   Contexts come from a strategy that sees an auxiliary randomization $\xi\sim\kappa$ (independent of $(s,b)$) and the observed history of contexts, prices and trade bits. The expected total loss over $T$ rounds is $\mathbb E\big[\sum_{t=1}^T\ell_t\big]$ over $\xi$ and $(s,b)\sim\pi$.
--
--   **Formalization Note** Algorithm 3 is specified in the paper only through Lemma 3.1 ("apply Lemma 3.1 under $\pi_t$"), so the algorithm is parametrized by any price rule with property (17); that the property is satisfiable is Lemma 3.1 itself. Conditioning the prior on the consistent set is the exact Bayes posterior, since each bit is a deterministic function of the pair given the price and contexts carry no information about the pair. Rounds are 0-based; the expectation is a lower Lebesgue integral of the nonnegative total loss.
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), Lemma 3.1 p.12, Algorithm 3 p.13, §1.4 p.7

import Mathlib
import Definitions.Def_CtxSearchTSR_Supplement_BilateralTrade

open MeasureTheory Matrix ProbabilityTheory
open scoped ENNReal

namespace CtxSearchTSR.Supplement

/-!
# Algorithm 3 (Bayesian Contextual Bilateral Trade), its run, and its expected total loss

Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, *Contextual Search and Bilateral Trade with a
Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…),
Lemma 3.1 (p.12) and Algorithm 3 (p.13):

"Initialize the posterior π₁ = π. For t = 1, 2, …: 1. Receive xₜ and let πₜ be the current
posterior of (s, b). 2. Apply Lemma 3.1 under πₜ to S = xₜᵀs and B = xₜᵀb and post the resulting
price pₜ. 3. Observe Yₜ and condition the joint posterior on this bit and the posted offer."

Lemma 3.1: "For every pair (S, B) of square-integrable real random variables, there is a common
price p such that L(p) ≤ 2¹¹D(p). (17) The price can be chosen as a function of the joint
distribution."

**Formalization Note.**
* Algorithm 3 is parametrized by a price rule `ρ`, a function of the joint law of (S, B).
  `PriceRule17 ρ` is exactly the property Lemma 3.1 provides: for every probability measure on
  ℝ × ℝ whose two coordinates are square-integrable, the price `ρ μ` satisfies (17).
* The history, context strategies (with auxiliary randomization ξ), posterior-by-conditioning and
  0-based rounds are as for Algorithm 1 (`Def_CtxSearchTSR_Supplement_Algorithm1`). The posterior is
  the prior conditioned on the pairs consistent with every recorded trade bit; this is the exact
  Bayes posterior because each bit is a deterministic function of the pair given the posted price
  and contexts carry no information about the pair (§1.4). Algorithm 3 uses no randomness of its
  own.
* The expectation is a lower Lebesgue integral of the nonnegative total loss over w = (s, b) ∼ π
  (inner) and ξ ∼ κ (outer).
-/

/-- Property (17) of a price rule, for every joint law with finite second moments. -/
def PriceRule17 (ρ : Measure (ℝ × ℝ) → ℝ) : Prop :=
  ∀ μ : Measure (ℝ × ℝ), IsProbabilityMeasure μ →
    MemLp (fun q : ℝ × ℝ => q.1) 2 μ → MemLp (fun q : ℝ × ℝ => q.2) 2 μ →
    lossL μ (ρ μ) ≤ 2 ^ 11 * infoD μ (ρ μ)

/-- One round's observed record: context, posted price, trade bit. -/
structure TradeRecord (d : ℕ) where
  /-- The context xₜ. -/
  x : Fin d → ℝ
  /-- The posted price pₜ. -/
  p : ℝ
  /-- The trade bit Yₜ. -/
  Y : Bool

/-- An adaptive, possibly randomized, context strategy for Bayesian bilateral trade. -/
abbrev BayesTradeStrategy (d : ℕ) (Ξ : Type*) : Type _ := Ξ → List (TradeRecord d) → (Fin d → ℝ)

/-- The pairs (s, b) consistent with every recorded trade bit. -/
def consistentTradeSet {d : ℕ} (h : List (TradeRecord d)) : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {w | ∀ r ∈ h, tradeBit (r.x ⬝ᵥ w.1) (r.x ⬝ᵥ w.2) r.p = r.Y}

/-- The posterior of (s, b) after the history `h`. -/
noncomputable def tradePosterior {d : ℕ} (π : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (h : List (TradeRecord d)) : Measure ((Fin d → ℝ) × (Fin d → ℝ)) :=
  π[|consistentTradeSet h]

/-- The joint law of (S, B) = (xᵀs, xᵀb) under `ν`. -/
noncomputable def projLaw {d : ℕ} (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (x : Fin d → ℝ) :
    Measure (ℝ × ℝ) :=
  ν.map (fun w => (x ⬝ᵥ w.1, x ⬝ᵥ w.2))

/-- The record of a round of Algorithm 3 after history `h`. -/
noncomputable def alg3Record {d : ℕ} {Ξ : Type*} (π : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (ρ : Measure (ℝ × ℝ) → ℝ) (X : BayesTradeStrategy d Ξ) (ξ : Ξ)
    (w : (Fin d → ℝ) × (Fin d → ℝ)) (h : List (TradeRecord d)) : TradeRecord d :=
  let x := X ξ h
  let p := ρ (projLaw (tradePosterior π h) x)
  ⟨x, p, tradeBit (x ⬝ᵥ w.1) (x ⬝ᵥ w.2) p⟩

/-- The history of Algorithm 3 before round `t` (0-based). -/
noncomputable def alg3History {d : ℕ} {Ξ : Type*} (π : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (ρ : Measure (ℝ × ℝ) → ℝ) (X : BayesTradeStrategy d Ξ) (ξ : Ξ)
    (w : (Fin d → ℝ) × (Fin d → ℝ)) : ℕ → List (TradeRecord d)
  | 0 => []
  | t + 1 => alg3History π ρ X ξ w t ++ [alg3Record π ρ X ξ w (alg3History π ρ X ξ w t)]

/-- The loss ℓₜ = (xₜᵀ(b − s))₊(1 − Yₜ) of round `t` (0-based) of Algorithm 3. -/
noncomputable def alg3RoundLoss {d : ℕ} {Ξ : Type*} (π : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (ρ : Measure (ℝ × ℝ) → ℝ) (X : BayesTradeStrategy d Ξ) (ξ : Ξ)
    (w : (Fin d → ℝ) × (Fin d → ℝ)) (t : ℕ) : ℝ :=
  let r := alg3Record π ρ X ξ w (alg3History π ρ X ξ w t)
  tradeLoss (r.x ⬝ᵥ w.1) (r.x ⬝ᵥ w.2) r.p

/-- The expected total loss Σ_{t=1}^T 𝔼[ℓₜ] of Algorithm 3 over `T` rounds, over ξ ∼ κ and
(s, b) ∼ π. -/
noncomputable def alg3ExpectedTotalLoss {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (π : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (ρ : Measure (ℝ × ℝ) → ℝ) (κ : Measure Ξ)
    (X : BayesTradeStrategy d Ξ) (T : ℕ) : ℝ≥0∞ :=
  ∫⁻ ξ, ∫⁻ w, ∑ t : Fin T, ENNReal.ofReal (alg3RoundLoss π ρ X ξ w t.val) ∂π ∂κ

end CtxSearchTSR.Supplement


