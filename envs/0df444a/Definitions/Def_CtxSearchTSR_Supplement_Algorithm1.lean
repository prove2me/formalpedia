-- Prove2me | Definitions.Def_CtxSearchTSR_Supplement_Algorithm1
-- name    : CtxSearchTSR_Supplement_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:20:35.62191+00:00
-- url     : https://prove2.me/theorems/f7b446c9-6300-44de-b0fb-58b6d70f696b
-- title:
--   Algorithm 1 (Bayesian Contextual Search): posterior, price $\mu_t+\frac{\sigma_t}{2}\varepsilon_t$, run and expected total loss
-- statement:
--   A target $z\in\mathbb R^d$ is drawn from a known prior $\pi$. In round $t$ the learner receives a context $x_t$, and **Algorithm 1** (Bayesian Contextual Search)
--
--   1. computes the posterior mean $\boldsymbol\mu_t$ and covariance $\Sigma_t$ of $z$ given the observed history, and $\mu_t=x_t^\top\boldsymbol\mu_t$, $\sigma_t=(x_t^\top\Sigma_t x_t)^{1/2}$;
--   2. draws a fresh uniform sign $\varepsilon_t\in\{-1,1\}$ and posts $P_t=\mu_t+\frac{\sigma_t}{2}\varepsilon_t$;
--   3. observes $Y_t=\operatorname{sign}(x_t^\top z-P_t)$, with $\operatorname{sign}(0)=1$, and updates the posterior.
--
--   The loss of round $t$ is $\ell_t=|x_t^\top z-P_t|$.
--
--   The **observed history** before round $t$ is the list of earlier contexts, prices, feedback bits and signs. A **context strategy** chooses the next context as a function of an auxiliary randomization $\xi$ (drawn from an arbitrary probability measure $\kappa$, independent of $z$ and of the learner's signs) and of the observed history. It never sees $z$ or the current sign. The **posterior** after a history is the prior conditioned on the set of targets consistent with every recorded feedback bit,
--
--   $$\pi_{t}=\pi\big(\,\cdot \bigm| \{z' : \operatorname{sign}(x_s^\top z'-P_s)=Y_s \text{ for all } s<t\}\big).$$
--
--   The **expected total loss** over $T$ rounds is $\mathbb E\big[\sum_{t=1}^T\ell_t\big]$, the expectation over $\xi\sim\kappa$, the $2^T$ equally likely sign vectors, and $z\sim\pi$.
--
--   **Formalization Note** The conditioned prior is the exact Bayes posterior: the probability of a history given $z$ is the indicator of the consistent set times factors that do not involve $z$. Before round 1 the posterior is the prior. A history of prior probability zero gives the zero measure, and such histories carry weight zero. Rounds are 0-based. Losses are nonnegative, so the expectation is a lower Lebesgue integral (in $[0,\infty]$) of the total loss; sign vectors past the horizon are extended by the published `extendSigns` and never read.
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §1.4 p.7, §2.1 p.7, Algorithm 1 p.8, Theorem 2.1 p.8

import Mathlib
import Definitions.Def_CtxSearchTSR_ExpectedTotalLoss
import Definitions.Def_CtxSearchTSR_Supplement_Moments

open MeasureTheory Matrix ProbabilityTheory
open scoped ENNReal

namespace CtxSearchTSR.Supplement

/-!
# Algorithm 1 (Bayesian Contextual Search), its run, and its expected total loss

Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, *Contextual Search and Bilateral Trade with a
Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…),
§1.4 (p.7), §2.1 (p.7) and Algorithm 1 (p.8):

1. compute the posterior moments µₜ, Σₜ of z and µₜ = xₜᵀµₜ, σₜ = (xₜᵀΣₜxₜ)^{1/2};
2. draw a fresh independent uniform sign εₜ ∈ {−1, 1} and post Pₜ = µₜ + (σₜ/2) εₜ;
3. observe Yₜ = sign(xₜᵀz − Pₜ) (sign(0) = 1) and compute the posterior distribution on z.

"The expectation is over the prior and the randomization of the learner and the contexts"
(Theorem 2.1, p.8).

**Formalization Note.**
* The observed history F_{t−1} (§1.4) is the list of the previous rounds' records (context, posted
  price, feedback, learner sign), oldest first.
* A context strategy `X ξ h` maps an auxiliary context randomization `ξ` (drawn from an arbitrary
  probability measure, independent of z and of the learner's signs) and the observed history `h`
  to the next context. It never sees z or the current sign, so the context is conditionally
  independent of z given the history (§1.4). A deterministic adaptive strategy is the case of a
  one-point `ξ`.
* The posterior of z given a history is the prior conditioned (`ProbabilityTheory.cond`) on the set
  of targets consistent with all recorded feedback. This is the exact Bayes posterior: the
  likelihood of a history is the indicator of that set times factors that do not involve z. Before
  round 1 the history is empty and the posterior is the prior (`cond_univ`). On a history of prior
  probability zero the posterior is the zero measure; such histories carry weight zero.
* Rounds are 0-based (the paper's round t is index t − 1). Signs are `Bool` mapped to ±1 by
  `signOf`; the sign sequence is extended past the horizon by `extendSigns` (never read).
* Losses are nonnegative; the expectation is a lower Lebesgue integral of `ENNReal.ofReal` of the
  total loss, over z ∼ prior (innermost), the 2^T equally likely sign vectors, and ξ (outermost).
-/

/-- One round's observed record: context, posted price, feedback ±1, learner sign. -/
structure SearchRecord (d : ℕ) where
  /-- The context xₜ. -/
  x : Fin d → ℝ
  /-- The posted price Pₜ. -/
  P : ℝ
  /-- The feedback Yₜ = sign(xₜᵀz − Pₜ) ∈ {−1, 1}. -/
  Y : ℝ
  /-- The learner's sign εₜ. -/
  e : Bool

/-- An adaptive, possibly randomized, context strategy: the next context as a function of the
auxiliary context randomization `ξ : Ξ` and the observed history (oldest record first). -/
abbrev BayesSearchStrategy (d : ℕ) (Ξ : Type*) : Type _ := Ξ → List (SearchRecord d) → (Fin d → ℝ)

/-- The targets consistent with every recorded feedback bit. -/
def consistentSet {d : ℕ} (h : List (SearchRecord d)) : Set (Fin d → ℝ) :=
  {z | ∀ r ∈ h, feedback z r.x r.P = r.Y}

/-- The posterior of z after the history `h`: the prior conditioned on the consistent set. -/
noncomputable def posterior {d : ℕ} (π : Measure (Fin d → ℝ)) (h : List (SearchRecord d)) :
    Measure (Fin d → ℝ) :=
  π[|consistentSet h]

/-- Algorithm 1's price at posterior `ν`, context `x`, sign `e`:
P = xᵀµ(ν) + ((xᵀ Cov(ν) x)^{1/2} / 2) · e. -/
noncomputable def alg1Price {d : ℕ} (ν : Measure (Fin d → ℝ)) (x : Fin d → ℝ) (e : Bool) : ℝ :=
  x ⬝ᵥ meanVec ν + Real.sqrt (x ⬝ᵥ (covMat ν *ᵥ x)) / 2 * signOf e

/-- The record of round `t` of Algorithm 1 after history `h`, for target `z`, context strategy `X`
with randomization `ξ`, and signs `ε`. -/
noncomputable def alg1Record {d : ℕ} {Ξ : Type*} (π : Measure (Fin d → ℝ))
    (X : BayesSearchStrategy d Ξ) (ξ : Ξ) (ε : ℕ → Bool) (z : Fin d → ℝ) (t : ℕ)
    (h : List (SearchRecord d)) : SearchRecord d :=
  let x := X ξ h
  let P := alg1Price (posterior π h) x (ε t)
  ⟨x, P, feedback z x P, ε t⟩

/-- The history of Algorithm 1 before round `t` (0-based). -/
noncomputable def alg1History {d : ℕ} {Ξ : Type*} (π : Measure (Fin d → ℝ))
    (X : BayesSearchStrategy d Ξ) (ξ : Ξ) (ε : ℕ → Bool) (z : Fin d → ℝ) :
    ℕ → List (SearchRecord d)
  | 0 => []
  | t + 1 => alg1History π X ξ ε z t ++ [alg1Record π X ξ ε z t (alg1History π X ξ ε z t)]

/-- The loss ℓₜ = |xₜᵀz − Pₜ| of round `t` (0-based) of Algorithm 1. -/
noncomputable def alg1RoundLoss {d : ℕ} {Ξ : Type*} (π : Measure (Fin d → ℝ))
    (X : BayesSearchStrategy d Ξ) (ξ : Ξ) (ε : ℕ → Bool) (z : Fin d → ℝ) (t : ℕ) : ℝ :=
  let r := alg1Record π X ξ ε z t (alg1History π X ξ ε z t)
  searchLoss z r.x r.P

/-- The expected total loss Σ_{t=1}^T 𝔼[ℓₜ] of Algorithm 1 over `T` rounds: the expectation is
over the context randomization ξ ∼ κ, the learner's i.i.d. uniform signs, and z ∼ π. -/
noncomputable def alg1ExpectedTotalLoss {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (π : Measure (Fin d → ℝ)) (κ : Measure Ξ) (X : BayesSearchStrategy d Ξ) (T : ℕ) : ℝ≥0∞ :=
  ∫⁻ ξ, ((2 : ℝ≥0∞) ^ T)⁻¹ * ∑ ε : Fin T → Bool,
    ∫⁻ z, ∑ t : Fin T, ENNReal.ofReal (alg1RoundLoss π X ξ (extendSigns ε) z t.val) ∂π ∂κ

end CtxSearchTSR.Supplement


