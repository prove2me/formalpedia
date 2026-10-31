-- Prove2me | Definitions.Def_FoundationsRL_OnlineLearning_Mixable
-- name    : FoundationsRL_OnlineLearning_Mixable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:49.05306+00:00
-- url     : https://prove2.me/theorems/1a669675-5057-4181-80be-3eaa54068bc4
-- title:
--   Mixability of a loss (1.34)
-- statement:
--   A loss $\ell$ is **mixable** with parameter $\eta$ over the class $\mathcal F$ if there is a constant $c>0$ such that for any $x$ and any distribution $q\in\Delta(\mathcal F)$ there is a prediction $\hat f(x)\in\mathcal Y'$ with, for all $y\in\mathcal Y$,
--   $$
--   \ell(\hat f(x),y)\le-\frac c\eta\log\Big(\sum_{f\in\mathcal F}q(f)\exp\{-\eta\,\ell(f(x),y)\}\Big).
--   $$
--
--   Mixability is the notes' tool for fast rates beyond the log loss: it replays the log-loss potential argument with an inequality in place of (1.27).
--
--   **Formalization Note** `IsMixableWith` fixes the constants $\eta$ and $c$; `IsMixable` asserts that some $c>0$ works. $\mathcal Y'$ and $\mathcal Y$ are subsets of ambient types.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Remark 6, (1.34), p. 18

import Mathlib

namespace FoundationsRL.OnlineLearning

/-- **Mixability with constants `η` and `c`**, (1.34), Remark 6, p. 18, arXiv:2312.16730v1: for any
`x` and any distribution `q ∈ Δ(F)` there is a prediction `a = f̂(x) ∈ Y'` such that for all `b ∈ Y`,
`ℓ(a, b) ≤ -(c/η) log ∑_{f ∈ F} q(f) exp{-η ℓ(f(x), b)}`.

**Formalization Note.** `Yp` and `Yo` are the notes' `Y'` and `Y`, as subsets of the types `A` and
`B`. A distribution on `F` is a nonnegative `q` with `∑ f ∈ F, q f = 1`. -/
def IsMixableWith {X A B : Type*} (Yp : Set A) (Yo : Set B) (ℓ : A → B → ℝ) (F : Finset (X → A))
    (η c : ℝ) : Prop :=
  ∀ (x : X) (q : (X → A) → ℝ), (∀ f ∈ F, 0 ≤ q f) → ∑ f ∈ F, q f = 1 →
    ∃ a ∈ Yp, ∀ b ∈ Yo, ℓ a b ≤ -(c / η) * Real.log (∑ f ∈ F, q f * Real.exp (-η * ℓ (f x) b))

/-- **Mixability with parameter `η`**, Remark 6, p. 18, arXiv:2312.16730v1: there is a constant
`c > 0` such that (1.34) holds. -/
def IsMixable {X A B : Type*} (Yp : Set A) (Yo : Set B) (ℓ : A → B → ℝ) (F : Finset (X → A))
    (η : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ IsMixableWith Yp Yo ℓ F η c

end FoundationsRL.OnlineLearning


