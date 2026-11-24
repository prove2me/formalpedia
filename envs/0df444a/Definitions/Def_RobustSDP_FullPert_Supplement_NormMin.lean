-- Prove2me | Definitions.Def_RobustSDP_FullPert_Supplement_NormMin
-- name    : RobustSDP_FullPert_Supplement_NormMin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:44:14.946136+00:00
-- url     : https://prove2.me/theorems/76babfbb-79f8-452d-a113-4c2358764d92
-- title:
--   §5.6, pp. 44–45 — robust maximum-norm minimization: problems (27), (28), (29), their solutions and the minimum-norm nominal solution
-- statement:
--   This entry fixes the objects of the robust maximum-norm minimization problem of §5.6 of El Ghaoui, Oustry and Lebret. Let $H_0, H_1, \dots, H_m \in \mathbb{R}^{p\times q}$ and $H(x) = H_0 + \sum_{i=1}^m x_i H_i$ for $x \in \mathbb{R}^m$. All matrix norms are spectral norms (largest singular value); $\|x\|$ is the Euclidean norm of $x$. For a block row $\Delta = [\Delta_0\ \dots\ \Delta_m]$ of $p\times q$ blocks, $\mathbf{H}(x,\Delta) = H_0 + \Delta_0 + \sum_i x_i (H_i + \Delta_i)$.
--
--   1. **Worst-case objective of (28).** For $\rho \ge 0$,
--   $$\phi_\rho(x) = \max_{\|\Delta\| \le \rho} \|\mathbf{H}(x,\Delta)\|,$$
--   where $\|\Delta\|$ is the spectral norm of the whole block row.
--
--   2. **Objective of (29).** $\psi_\rho(x) = \|H(x)\| + \rho\sqrt{\|x\|^2 + 1}$.
--
--   3. **Solutions of (28).** $x$ solves (28) if $\phi_\rho(x) \le \phi_\rho(x')$ for every $x' \in \mathbb{R}^m$.
--
--   4. **Solutions of the nominal problem (27).** $x$ solves (27) if $\|H(x)\| \le \|H(x')\|$ for every $x'$.
--
--   5. **Minimum-norm nominal solution.** A solution $x$ of (27) with $\|x\| \le \|x'\|$ for every solution $x'$ of (27).
--
--   These are the objects of Theorem 5.4: the robust problem (28) is a regularization of (27), and its solutions are compared with the minimum-norm solution of (27).
--
--   **Formalization Note** The published module `RobustSDP.Unstructured.Model` supplies `affineMap` and `perturbedH`; the block row is one $p \times q(m+1)$ matrix whose columns are indexed by pairs. $\phi_\rho(x)$ is written as a real supremum (`sSup`). For $\rho \ge 0$ the set contains $\|H(x)\|$ (take $\Delta = 0$). It is bounded above and the supremum is attained, so the real supremum is the maximum of (28).
--
--
--   The module also defines `NormSolutionLipschitz`, the local exact-solution stability predicate used in the refutation, and `normCounterexampleData e`, the two coefficients $[-1,e]$ and $[1,0]$ of $H_e(x)=[x-1,e]$. This predicate is not assumed: its failure at $e=0$, $\rho=\sqrt2$ is a conclusion of the revised Theorem 5.4.
--
--   For a negative radius the Lean supremum is over the empty set and equals zero; no theorem uses that extension.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 44, Eq. (27) and the display of H(x, Δ); p. 45, Eq. (28) and Eq. (29)

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert.Supplement

open RobustSDP.Unstructured

/-- The worst-case objective of the min-max problem (28), p. 45 (El Ghaoui–Oustry–Lebret 1998):
`max_{‖Δ‖ ≤ ρ} ‖H(x, Δ)‖`, where `H(x, Δ) = H₀ + Δ₀ + ∑ᵢ xᵢ(Hᵢ + Δᵢ)` (`perturbedH`) and
`Δ = [Δ₀ … Δ_m]` is a block row of `p × q` blocks with spectral norm at most `ρ`. Written as a
real supremum; the set is nonempty (`Δ = 0` when `ρ ≥ 0`) and bounded above, and the
maximum is attained. -/
noncomputable def robustNormObj {m p q : ℕ} (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ)
    (ρ : ℝ) (x : Fin m → ℝ) : ℝ :=
  sSup {s : ℝ | ∃ Δ : Matrix (Fin p) (Fin (m + 1) × Fin q) ℝ, ‖Δ‖ ≤ ρ ∧
    s = ‖perturbedH Hs Δ x‖}

/-- The objective of the convex problem (29), p. 45: `‖H(x)‖ + ρ√(‖x‖² + 1)`, with `‖H(x)‖` the
spectral norm and `‖x‖` the Euclidean norm. -/
noncomputable def normObj29 {m p q : ℕ} (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ) (ρ : ℝ)
    (x : Fin m → ℝ) : ℝ :=
  ‖affineMap Hs x‖ + ρ * Real.sqrt (∑ i, x i ^ 2 + 1)

/-- The Euclidean norm `‖x‖ = √(∑ᵢ xᵢ²)` of a decision vector. -/
noncomputable def euclidNorm {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- `x` is a solution of the min-max problem (28), p. 45: it minimizes the worst-case objective
over all of `ℝ^m`. -/
def IsRobustNormSolution {m p q : ℕ} (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ) (ρ : ℝ)
    (x : Fin m → ℝ) : Prop :=
  ∀ x' : Fin m → ℝ, robustNormObj Hs ρ x ≤ robustNormObj Hs ρ x'

/-- `x` is a solution of the nominal problem (27), p. 44: it minimizes `‖H(x)‖` over `ℝ^m`. -/
def IsNominalNormSolution {m p q : ℕ} (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ)
    (x : Fin m → ℝ) : Prop :=
  ∀ x' : Fin m → ℝ, ‖affineMap Hs x‖ ≤ ‖affineMap Hs x'‖

/-- `x` is a minimum (Euclidean) norm solution of the nominal problem (27): a solution of (27)
whose Euclidean norm is at most that of every solution of (27). -/
def IsMinNormNominalSolution {m p q : ℕ} (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ)
    (x : Fin m → ℝ) : Prop :=
  IsNominalNormSolution Hs x ∧
    ∀ x' : Fin m → ℝ, IsNominalNormSolution Hs x' → euclidNorm x ≤ euclidNorm x'

/-- Local Lipschitz stability of the exact solution map at fixed positive rho, as claimed
in Theorem 5.4. Kept as a predicate so its failure can be stated explicitly. -/
def NormSolutionLipschitz {m p q : ℕ}
    (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ) (ρ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (Hs' : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ) (η : ℝ), η < ε →
      (∀ i, ‖Hs' i - Hs i‖ ≤ η) → ∀ x x' : Fin m → ℝ,
        IsRobustNormSolution Hs ρ x → IsRobustNormSolution Hs' ρ x' →
          euclidNorm (x' - x) ≤ C * η

/-- Counterexample data for the Lipschitz clause of Theorem 5.4:
`H_e(x) = [x - 1, e]`, a 1-by-2 row, with one decision variable. -/
def normCounterexampleData (e : ℝ) : Fin 2 → Matrix (Fin 1) (Fin 2) ℝ :=
  ![!![-1, e], !![1, 0]]

end RobustSDP.FullPert.Supplement


