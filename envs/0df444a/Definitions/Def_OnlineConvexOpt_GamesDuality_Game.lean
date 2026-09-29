-- Prove2me | Definitions.Def_OnlineConvexOpt_GamesDuality_Game
-- name    : OnlineConvexOpt_GamesDuality_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:20:06.664899+00:00
-- url     : https://prove2.me/theorems/e0b50c58-33b8-4400-981a-99295e331f06
-- title:
--   Zero-sum game values and Algorithm 28 (Simple LP)
-- statement:
--   This bundle collects the definitions for Chapter 8 ("Games, Duality, and Regret") of Hazan's
--   *Introduction to Online Convex Optimization*, 2nd ed. (arXiv:1909.05207v3): the zero-sum game
--   of Section 8.2, and the row-player's regret-minimization algorithm of Section 8.4.
--
--   **The game.** A two-player zero-sum game in normal form (Definition 8.2) is a real matrix
--   $A \in \mathbb{R}^{n \times m}$: the row player picks a mixed strategy $x$ in the simplex
--   $\Delta_n$, the column player a mixed strategy $y \in \Delta_m$, and the row player's expected
--   loss (the column player's expected reward) is $\mathrm{rowValue}(A, x, y) = x^{\mathsf T} A y$.
--
--   The row player's guaranteed loss is $\lambda_R = \min_{x \in \Delta_n} \max_{y \in \Delta_m}
--   x^{\mathsf T} A y$ (`lambdaR`), and the column player's guaranteed reward is
--   $\lambda_C = \max_{y \in \Delta_m} \min_{x \in \Delta_n} x^{\mathsf T} A y$ (`lambdaC`), p. 143.
--   Both are rendered with Mathlib's `iInf`/`iSup` over the membership condition
--   `x ∈ stdSimplex ℝ (Fin n)`, matching the convention `Introduction to Online Convex Optimization
--   III`'s `RegretT` already fixed for this series (an infimum/supremum over a possibly-unbounded
--   or, here, always-bounded compact set, rather than a `sInf`/`sSup` of an explicit image set).
--
--   **Algorithm 28 ("Simple LP").** `IsSimpleLPRun η A x y` packages one run of the algorithm on
--   p. 147: the row player's mixed strategy starts uniform, `x 0 i = 1 / n`; at every round `t`
--   the column player best-responds, playing some `y t ∈ Δ_m` that maximizes
--   `rowValue A (x t) ·` over `Δ_m` (Eq. (8.2)); and the next row strategy is the multiplicative-
--   weights / exponentiated-gradient update on the linear loss `A · (y t)`,
--   $$x_{t+1}(i) = \frac{x_t(i)\, e^{-\eta (A y_t)_i}}{\sum_j x_t(j)\, e^{-\eta (A y_t)_j}}.$$
--   `average x T` is the algorithm's returned vector after `T` rounds, the mean of
--   `x 0, …, x (T - 1)` (the book's rounds `1, …, T`, index-shifted as throughout this series).
--
--   **Formalization Note.** The best-response condition is stated as membership plus a
--   maximality inequality rather than picking out a specific maximizer, since the maximizer of a
--   linear functional over a simplex need not be unique. `η` is left a free real parameter of the
--   run rather than hard-coded to its optimal value; the theorems that use this run fix it to the
--   "appropriate choice" the book names, `η = √(2 log n / T)`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, pp. 142-143, 147 (Definition 8.2, Section 8.2, Algorithm 28)

import Mathlib

namespace OnlineConvexOpt.GamesDuality

open Finset

/-- The row player's expected loss (equivalently, the column player's expected reward) when
the row player plays mixed strategy `x` and the column player plays mixed strategy `y` against
payoff matrix `A`, Hazan p. 142: `x⊤Ay`. -/
def rowValue {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) : ℝ :=
  x ⬝ᵥ A.mulVec y

/-- The row player's guaranteed loss `λ_R`, Hazan p. 143: `λ_R = min_{x ∈ Δn} max_{y ∈ Δm}
x⊤Ay`. -/
noncomputable def lambdaR {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ⨅ x ∈ stdSimplex ℝ (Fin n), ⨆ y ∈ stdSimplex ℝ (Fin m), rowValue A x y

/-- The column player's guaranteed reward `λ_C`, Hazan p. 143: `λ_C = max_{y ∈ Δm}
min_{x ∈ Δn} x⊤Ay`. -/
noncomputable def lambdaC {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ⨆ y ∈ stdSimplex ℝ (Fin m), ⨅ x ∈ stdSimplex ℝ (Fin n), rowValue A x y

/-- `(x, y)` is a run of Algorithm 28 ("Simple LP", p. 147) on payoff matrix `A` with learning
rate `η`: the row player starts at the uniform mixed strategy over `[n]`; at every round `t`
the column player best-responds, playing `y t` to maximize her value `x_t⊤A y` against the row
player's current strategy (Eq. (8.2)); and the row player's next strategy is the exponentiated-
gradient / multiplicative-weights update on the linear loss `A y_t` (Algorithm 28, step 5). -/
structure IsSimpleLPRun {n m : ℕ} (η : ℝ) (A : Matrix (Fin n) (Fin m) ℝ)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ) : Prop where
  init : ∀ i, x 0 i = 1 / (n : ℝ)
  best_response : ∀ t, y t ∈ stdSimplex ℝ (Fin m) ∧
    ∀ y' ∈ stdSimplex ℝ (Fin m), rowValue A (x t) y' ≤ rowValue A (x t) (y t)
  update : ∀ t i, x (t + 1) i =
    x t i * Real.exp (-η * A.mulVec (y t) i) /
      ∑ j, x t j * Real.exp (-η * A.mulVec (y t) j)

/-- Algorithm 28's output after `T` rounds: the average of the row player's mixed strategies
`x_0, …, x_{T-1}` (the book's rounds `1, …, T` shifted down by one), `x̄ = (1/T) ∑_{t=1}^T x_t`.
-/
noncomputable def average {n : ℕ} (x : ℕ → Fin n → ℝ) (T : ℕ) : Fin n → ℝ :=
  fun i => (∑ t ∈ Finset.range T, x t i) / (T : ℝ)

end OnlineConvexOpt.GamesDuality


