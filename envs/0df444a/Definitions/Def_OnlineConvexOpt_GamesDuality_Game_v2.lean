-- Prove2me | Definitions.Def_OnlineConvexOpt_GamesDuality_Game_v2
-- name    : OnlineConvexOpt_GamesDuality_Game_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:52.200851+00:00
-- url     : https://prove2.me/theorems/197ea7f8-01c4-4473-97d6-4865db18f638
-- title:
--   Zero-sum game values $\lambda_R$, $\lambda_C$ (genuine extrema over the simplices), Algorithm 28 run and average
-- statement:
--   The row player's expected loss $x^\top Ay$, the game values $\lambda_R=\min_{x\in\Delta_n}\max_{y\in\Delta_m}x^\top Ay$ and $\lambda_C=\max_{y\in\Delta_m}\min_{x\in\Delta_n}x^\top Ay$, the run predicate of Algorithm 28 (Simple LP) and its averaged output. Corrected version of `OnlineConvexOpt_GamesDuality_Game`: $\lambda_R,\lambda_C$ are rendered as real infima/suprema of images of the simplices (genuine extrema for $n,m\ge1$ by compactness and continuity) instead of nested `⨅ x ∈ Δn`/`⨆ y ∈ Δm` binders, which on $\mathbb R$ collapsed both values to the junk value $0$ for every matrix. `rowValue`, `IsSimpleLPRun` and `average` are unchanged.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, pp. 142–143 (mixed strategies, λ_R, λ_C), p. 147, Algorithm 28 (PDF pp. 164–165, 169)

import Mathlib

namespace OnlineConvexOpt.GamesDuality

open Finset

/-- The row player's expected loss (equivalently, the column player's expected reward) when
the row player plays mixed strategy `x` and the column player plays mixed strategy `y` against
payoff matrix `A`, Hazan p. 142: `x⊤Ay`. -/
def rowValue {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) : ℝ :=
  x ⬝ᵥ A.mulVec y

/-- The row player's guaranteed loss `λ_R`, Hazan p. 143: `λ_R = min_{x ∈ Δn} max_{y ∈ Δm}
x⊤Ay`, rendered as the real infimum over the image of the simplex `Δn` of the function
`x ↦ sSup (rowValue A x '' Δm)`. Both extrema are genuine (attained) when `n, m ≥ 1`: the
simplices are nonempty and compact and `rowValue` is continuous. (The retired version used the
binders `⨅ x ∈ stdSimplex …, ⨆ y ∈ stdSimplex …`, which on `ℝ` evaluate to the junk values
`sInf ∅ = 0` / `sSup ∅ = 0` at every point outside the simplex and so collapsed `λ_R` to `0`
for every matrix.) -/
noncomputable def lambdaR {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  sInf ((fun x => sSup ((fun y => rowValue A x y) '' stdSimplex ℝ (Fin m))) '' stdSimplex ℝ (Fin n))

/-- The column player's guaranteed reward `λ_C`, Hazan p. 143: `λ_C = max_{y ∈ Δm}
min_{x ∈ Δn} x⊤Ay`, rendered as the real supremum over the image of `Δm` of
`y ↦ sInf (rowValue A · y '' Δn)` (genuine extrema for `n, m ≥ 1`, see `lambdaR`). -/
noncomputable def lambdaC {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  sSup ((fun y => sInf ((fun x => rowValue A x y) '' stdSimplex ℝ (Fin n))) '' stdSimplex ℝ (Fin m))

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


