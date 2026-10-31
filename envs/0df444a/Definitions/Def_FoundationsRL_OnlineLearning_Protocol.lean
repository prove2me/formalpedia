-- Prove2me | Definitions.Def_FoundationsRL_OnlineLearning_Protocol
-- name    : FoundationsRL_OnlineLearning_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:39.238996+00:00
-- url     : https://prove2.me/theorems/ccdcf33e-d00b-4dd8-a202-525e59f5e862
-- title:
--   Online learning protocol: cumulative loss, the benchmark, regret (1.18) and randomized regret (1.19)
-- statement:
--   The objects of the online learning protocol. On round $t$ the learner forms a predictor $\hat f^t:\mathcal X\to\mathcal Y'$ from the past examples, then observes $(x^t,y^t)\in\mathcal X\times\mathcal Y$ and suffers $\ell(\hat f^t(x^t),y^t)$ for a loss $\ell:\mathcal Y'\times\mathcal Y\to R$.
--
--   1. **Cumulative loss.** $\sum_{t=1}^T\ell(\hat f^t(x^t),y^t)$; a fixed function $f$ is the constant sequence.
--   2. **Benchmark.** $\min_{f\in\mathcal F}\sum_{t=1}^T\ell(f(x^t),y^t)$.
--   3. **Regret to $\mathcal F$.**
--   $$
--   \mathbf{Reg}=\sum_{t=1}^T\ell(\hat f^t(x^t),y^t)-\min_{f\in\mathcal F}\sum_{t=1}^T\ell(f(x^t),y^t).
--   $$
--   4. **Regret of a randomized predictor on a finite class.**
--   $$
--   \mathbf{Reg}=\sum_{t=1}^T\mathbb E_{\hat f^t\sim q^t}\big[\ell(\hat f^t(x^t),y^t)\big]-\min_{f\in\mathcal F}\sum_{t=1}^T\ell(f(x^t),y^t).
--   $$
--
--   These are the performance measures of Section 1.6; every regret bound of this mission is stated with them.
--
--   **Formalization Note** Rounds are 0-based, so `Finset.range T` is the notes' $1,\dots,T$. The value type of the cumulative loss is left open, so that one definition serves real losses and the log loss, whose values lie in $(-\infty,+\infty]$. The minimum is `⨅ f : F`; over a finite nonempty class it is attained. Over an infinite class Lean's real infimum is $0$ when the set is not bounded below, so each statement using it over such a class says why it is bounded below. In (1.19) the expectation is the finite sum $\sum_{f\in\mathcal F}q^t(f)\,\ell(f(x^t),y^t)$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.6, (1.17)–(1.19), pp. 12–13, Remark 4, p. 13

import Mathlib

namespace FoundationsRL.OnlineLearning

/-- **Cumulative loss of a sequence of predictors.** Foster & Rakhlin, Foundations of Reinforcement
Learning and Interactive Decision Making, arXiv:2312.16730v1, §1.6, p. 13:
`∑_{t=1}^T ℓ(f̂^t(x^t), y^t)`.

**Formalization Note.** Rounds are 0-based: the notes' round `t` is the index `t - 1` here, so
`Finset.range T` is the notes' `1, …, T`. A fixed function `f` is the constant sequence
`fun _ => f`. The value type `R` is left open so that the same definition serves real-valued losses
and the log loss, whose values lie in `EReal`. -/
def cumLoss {X Y Y' R : Type*} [AddCommMonoid R] (ℓ : Y' → Y → R) (fhat : ℕ → X → Y')
    (x : ℕ → X) (y : ℕ → Y) (T : ℕ) : R :=
  ∑ t ∈ Finset.range T, ℓ (fhat t (x t)) (y t)

/-- **The benchmark `min_{f ∈ F} ∑_{t=1}^T ℓ(f(x^t), y^t)`** of (1.18), p. 13, arXiv:2312.16730v1.

**Formalization Note.** The minimum is `⨅ f : F`. Over a finite nonempty class it is attained. For a
real-valued loss over an infinite class, Lean's real infimum is `0` on a set not bounded below or an
empty class, so every statement using it over an infinite class says why it is bounded below. -/
def bestCumLoss {X Y Y' R : Type*} [AddCommMonoid R] [InfSet R] (ℓ : Y' → Y → R)
    (F : Set (X → Y')) (x : ℕ → X) (y : ℕ → Y) (T : ℕ) : R :=
  ⨅ f : F, cumLoss ℓ (fun _ => (f : X → Y')) x y T

/-- **Regret to `F`**, (1.18), p. 13, arXiv:2312.16730v1:
`Reg = ∑_{t=1}^T ℓ(f̂^t(x^t), y^t) - min_{f ∈ F} ∑_{t=1}^T ℓ(f(x^t), y^t)`. -/
noncomputable def regret {X Y Y' : Type*} (ℓ : Y' → Y → ℝ) (F : Set (X → Y')) (fhat : ℕ → X → Y')
    (x : ℕ → X) (y : ℕ → Y) (T : ℕ) : ℝ :=
  cumLoss ℓ fhat x y T - bestCumLoss ℓ F x y T

/-- **Regret of a randomized predictor on a finite class**, (1.19), Remark 4, p. 13,
arXiv:2312.16730v1: `Reg = ∑_{t=1}^T E_{f̂^t ∼ q^t}[ℓ(f̂^t(x^t), y^t)] - min_{f ∈ F} ∑_{t=1}^T ℓ(f(x^t), y^t)`.

**Formalization Note.** `q t` is the distribution `q^t` on the finite class `F`, and the expectation
is the finite sum `∑ f ∈ F, q t f * ℓ (f (x t)) (y t)`. No probability space is needed, since `q^t`
is a deterministic function of the past. -/
noncomputable def regretRandomized {X Y Y' : Type*} (ℓ : Y' → Y → ℝ) (F : Finset (X → Y'))
    (q : ℕ → (X → Y') → ℝ) (x : ℕ → X) (y : ℕ → Y) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ f ∈ F, q t f * ℓ (f (x t)) (y t) -
    bestCumLoss ℓ (F : Set (X → Y')) x y T

end FoundationsRL.OnlineLearning


