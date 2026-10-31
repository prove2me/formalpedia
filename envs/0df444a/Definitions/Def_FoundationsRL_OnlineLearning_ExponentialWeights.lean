-- Prove2me | Definitions.Def_FoundationsRL_OnlineLearning_ExponentialWeights
-- name    : FoundationsRL_OnlineLearning_ExponentialWeights
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:18:37.218213+00:00
-- url     : https://prove2.me/theorems/7a2878af-41bc-49b1-bd7f-00969c2c1025
-- title:
--   Exponential Weights: weights, distribution (1.23), averaged prediction (1.24), potential (1.26)
-- statement:
--   Let $\mathcal F$ be a finite class, $\eta$ a learning rate, and $(x^t,y^t)$ the data sequence.
--
--   1. **Weight.** $\exp\{-\eta\sum_{i=1}^{t-1}\ell(f(x^i),y^i)\}$.
--   2. **Exponential Weights distribution.**
--   $$
--   q^t(f)\propto\exp\Big\{-\eta\sum_{i=1}^{t-1}\ell(f(x^i),y^i)\Big\}.
--   $$
--   3. **Averaged prediction.** $\hat f^t=\mathbb E_{f\sim q^t}[f]$, for functions into a real vector space.
--   4. **Potential.**
--   $$
--   \Phi^t_\eta=-\log\sum_{f\in\mathcal F}\exp\Big\{-\eta\sum_{i=1}^t\ell(f(x^i),y^i)\Big\}.
--   $$
--
--   The randomized variant samples $\hat f^t\sim q^t$; the averaged one plays $\mathbb E_{f\sim q^t}[f]$. The potential is what the regret analysis telescopes.
--
--   **Formalization Note** The Lean weight at index $t$ sums the first $t$ rounds, so it belongs to the notes' round $t+1$; the potential's index counts the rounds summed, as in the notes. The notes take $\eta>0$; at $\eta=0$ the definition is still meaningful and uniform, which is what $\eta=\sqrt{8\log|\mathcal F|/T}$ gives when $|\mathcal F|=1$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (1.23)–(1.24), p. 15, (1.26), p. 16

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_Protocol

namespace FoundationsRL.OnlineLearning

/-- **Exponential weight** `exp{-η ∑_{i=1}^{t-1} ℓ(f(x^i), y^i)}`, the unnormalized right side of
(1.23), p. 15, arXiv:2312.16730v1.

**Formalization Note.** Rounds are 0-based: `ewWeight ℓ η x y t f` sums the first `t` rounds, so it
belongs to the round with 0-based index `t`, which is the notes' round `t + 1`. -/
noncomputable def ewWeight {X Y Y' : Type*} (ℓ : Y' → Y → ℝ) (η : ℝ) (x : ℕ → X) (y : ℕ → Y)
    (t : ℕ) (f : X → Y') : ℝ :=
  Real.exp (-η * cumLoss ℓ (fun _ => f) x y t)

/-- **The Exponential Weights distribution** on a finite class, (1.23), p. 15, arXiv:2312.16730v1:
`q^t(f) ∝ exp{-η ∑_{i=1}^{t-1} ℓ(f(x^i), y^i)}`.

**Formalization Note.** The weights are positive, so for nonempty `F` the denominator is positive and
`ewDist` is a probability vector on `F`. The notes take `η > 0`; the definition also makes sense at
`η = 0`, where it is uniform, which is what `η = √(8 log|F|/T)` gives for `|F| = 1`. -/
noncomputable def ewDist {X Y Y' : Type*} (ℓ : Y' → Y → ℝ) (F : Finset (X → Y')) (η : ℝ)
    (x : ℕ → X) (y : ℕ → Y) (t : ℕ) (f : X → Y') : ℝ :=
  ewWeight ℓ η x y t f / ∑ g ∈ F, ewWeight ℓ η x y t g

/-- **Averaged prediction** `f̂^t = E_{f ∼ q^t}[f]`, (1.24), p. 15, arXiv:2312.16730v1, for a
finite class of functions into a real vector space and weights `q` on the class. -/
noncomputable def ewAveraged {X V : Type*} [AddCommMonoid V] [Module ℝ V] (F : Finset (X → V))
    (q : (X → V) → ℝ) : X → V :=
  ∑ f ∈ F, q f • f

/-- **The potential** `Φ^t_η = -log ∑_{f ∈ F} exp{-η ∑_{i=1}^t ℓ(f(x^i), y^i)}`, (1.26), p. 16,
arXiv:2312.16730v1. The index `t` counts the rounds summed, exactly as in the notes. -/
noncomputable def potential {X Y Y' : Type*} (ℓ : Y' → Y → ℝ) (F : Finset (X → Y')) (η : ℝ)
    (x : ℕ → X) (y : ℕ → Y) (t : ℕ) : ℝ :=
  -Real.log (∑ f ∈ F, ewWeight ℓ η x y t f)

end FoundationsRL.OnlineLearning


