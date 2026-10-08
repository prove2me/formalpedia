-- Prove2me | Definitions.Def_WassKF_Bisect_algorithm1
-- name    : WassKF_Bisect_algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:11:49.948108+00:00
-- url     : https://prove2.me/theorems/ad820dd4-a94d-417b-a5d8-07bab33ffab3
-- title:
--   Algorithm 1, p. 6 — the bisection iteration: bracket [γ_min, γ_max], midpoints, output L and the exit test h(γ) > 0, Δ < ε
-- statement:
--   Algorithm 1 takes $\Sigma \succ 0$, $D = \nabla f(S) \succeq 0$, $\rho > 0$, a tolerance $\varepsilon > 0$, the largest eigenvalue $\lambda_1$ of $D$ and an eigenvector $v_1$ of $\lambda_1$. It starts from the bracket
--   $$
--   LB_0 = \gamma_{\min} = \lambda_1\Big(1 + \sqrt{v_1^\top\Sigma v_1}/\rho\Big),\qquad UB_0 = \gamma_{\max} = \lambda_1\Big(1 + \sqrt{\mathrm{Tr}[\Sigma]}/\rho\Big).
--   $$
--   In pass $k = 0, 1, 2, \dots$ of its repeat loop it sets $\gamma_k = (UB_k + LB_k)/2$ and $L = L(\gamma_k)$, then updates the bracket by
--   $$
--   (LB_{k+1}, UB_{k+1}) = \begin{cases} (\gamma_k, UB_k) & \text{if } h(\gamma_k) < 0,\\ (LB_k, \gamma_k) & \text{otherwise,}\end{cases}
--   $$
--   and stops after pass $k$, returning $L(\gamma_k)$, if $h(\gamma_k) > 0$ and $\Delta(\gamma_k) < \varepsilon$.
--
--   This file defines $\gamma_{\min}$ (`gammaMin`), $\gamma_{\max}$ (`gammaMax`), the bracket sequence (`bisectState`), the trial multiplier $\gamma_k$ (`bisectGamma`), the matrix $L(\gamma_k)$ (`bisectOutput`) and the exit test (`bisectStops`).
--
--   **Formalization Note** The loop is modelled as the sequence of passes rather than as a function returning the output, because the loop need not terminate; statements about Algorithm 1 quantify over the passes at which the exit test holds. $\lambda_1$ and $v_1$ are explicit inputs, so a statement about the algorithm quantifies over every admissible choice.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 6, Algorithm 1; p. 13, (A.7)

import Mathlib
import Definitions.Def_WassKF_Bisect_hFun
import Definitions.Def_WassKF_Bisect_Lgamma
import Definitions.Def_WassKF_Bisect_Delta

open Matrix

namespace WassKF.Bisect

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `γ_min = λ₁(1 + √(v₁ᵀΣv₁)/ρ)`, (A.7) p. 13: the initial lower bound `LB` of Algorithm 1. -/
noncomputable def gammaMin (Sigma : Matrix ι ι ℝ) (ρ lam1 : ℝ) (v₁ : ι → ℝ) : ℝ :=
  lam1 * (1 + Real.sqrt (v₁ ⬝ᵥ (Sigma *ᵥ v₁)) / ρ)

/-- `γ_max = λ₁(1 + √Tr[Σ]/ρ)`, (A.7) p. 13: the initial upper bound `UB` of Algorithm 1. -/
noncomputable def gammaMax (Sigma : Matrix ι ι ℝ) (ρ lam1 : ℝ) : ℝ :=
  lam1 * (1 + Real.sqrt Sigma.trace / ρ)

/-- The bracket `(LB_k, UB_k)` held by Algorithm 1 (p. 6) at the start of its `k`-th pass through
the `repeat` loop (`k = 0, 1, 2, …`). It starts at `(γ_min, γ_max)`; a pass sets
`γ = (UB + LB)/2` and then `LB ← γ` if `h(γ) < 0`, else `UB ← γ`. The inputs `λ₁` (the largest
eigenvalue of `D`) and `v₁` (an eigenvector of `λ₁`) are passed explicitly. -/
noncomputable def bisectState (Sigma D : Matrix ι ι ℝ) (ρ lam1 : ℝ) (v₁ : ι → ℝ) : ℕ → ℝ × ℝ
  | 0 => (gammaMin Sigma ρ lam1 v₁, gammaMax Sigma ρ lam1)
  | k + 1 =>
    let s := bisectState Sigma D ρ lam1 v₁ k
    let γ := (s.2 + s.1) / 2
    if hFun Sigma D ρ γ < 0 then (γ, s.2) else (s.1, γ)

/-- The trial multiplier `γ = (UB + LB)/2` of the `k`-th pass of Algorithm 1's `repeat` loop. -/
noncomputable def bisectGamma (Sigma D : Matrix ι ι ℝ) (ρ lam1 : ℝ) (v₁ : ι → ℝ) (k : ℕ) : ℝ :=
  ((bisectState Sigma D ρ lam1 v₁ k).2 + (bisectState Sigma D ρ lam1 v₁ k).1) / 2

/-- The matrix `L = γ²(γI_d − D)⁻¹Σ(γI_d − D)⁻¹` set in the `k`-th pass of Algorithm 1; it is the
algorithm's output if the loop exits after this pass. -/
noncomputable def bisectOutput (Sigma D : Matrix ι ι ℝ) (ρ lam1 : ℝ) (v₁ : ι → ℝ) (k : ℕ) :
    Matrix ι ι ℝ :=
  Lgamma Sigma D (bisectGamma Sigma D ρ lam1 v₁ k)

/-- The exit test `until h(γ) > 0 and Δ < ε` of Algorithm 1, evaluated at the `k`-th pass. -/
def bisectStops (Sigma D : Matrix ι ι ℝ) (ρ ε lam1 : ℝ) (v₁ : ι → ℝ) (k : ℕ) : Prop :=
  0 < hFun Sigma D ρ (bisectGamma Sigma D ρ lam1 v₁ k) ∧
    Delta Sigma D ρ (bisectGamma Sigma D ρ lam1 v₁ k) < ε

end WassKF.Bisect


