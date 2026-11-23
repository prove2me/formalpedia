-- Prove2me | Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_ResidualMinimizer
-- name    : GlobalInexactNewton_Backtracking_Supplement_ResidualMinimizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:46:13.991877+00:00
-- url     : https://prove2.me/theorems/f64d61e6-854f-4ecd-8a37-1301423b0c26
-- title:
--   Residual minimization on nested subspaces and the segment of Lemma 8.1
-- statement:
--   For a linear map $A$, a right-hand side $b$, an initial approximation $u_0$, and a real subspace $K$, a residual-minimizing correction $z$ belongs to $K$ and satisfies
--
--   $$\|b-A(u_0+z)\|\le\|b-A(u_0+w)\|\quad\text{for every }w\in K.$$
--
--   A residual-minimizing method supplies nested subspaces $K_i$ and such corrections $z_i$. Index zero denotes the initial approximation: $K_0=\{0\}$ and $z_0=0$. For two corrections, put $\rho_i=\|b-A(u_0+z_i)\|$, $\rho_j=\|b-A(u_0+z_j)\|$ and define $\tau(\rho)=\sqrt{(\rho^2-\rho_j^2)/(\rho_i^2-\rho_j^2)}$ and $z(\rho)=\tau(\rho)z_i+(1-\tau(\rho))z_j$.
--
--   This interface allows any nested real subspaces and any minimizing corrections. It assumes neither invertibility of $A$ nor solvability of $Au=b$. **Formalization Note** The segment formula is used only with $\rho_i>\rho_j$ and $\rho_j\le\rho\le\rho_i$. Infinite histories may be continued by repeating their final space and minimizer; only a finite prefix is retained by the equality curve.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 415, Residual minimizing iterative method; DOI 10.1137/0804022

import Mathlib

namespace GlobalInexactNewton.Backtracking.Supplement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Correction attaining the minimum residual over a real linear subspace. -/
def IsResidualMinimizer (A : E →L[ℝ] E) (b u₀ : E) (K : Submodule ℝ E) (z : E) : Prop :=
  z ∈ K ∧ ∀ w ∈ K, ‖b - A (u₀ + z)‖ ≤ ‖b - A (u₀ + w)‖

/-- General nested-subspace residual minimization, starting from correction zero. -/
def IsResidualMethod (A : E →L[ℝ] E) (b u₀ : E)
    (K : ℕ → Submodule ℝ E) (z : ℕ → E) : Prop :=
  K 0 = ⊥ ∧ z 0 = 0 ∧ Monotone K ∧ ∀ i, IsResidualMinimizer A b u₀ (K i) (z i)

/-- The square-root parametrization of Lemma 8.1, using the two actual residual norms. -/
noncomputable def residualSegment (A : E →L[ℝ] E) (b u₀ zi zj : E) (ρ : ℝ) : E :=
  let τ := Real.sqrt ((ρ ^ 2 - ‖b - A (u₀ + zj)‖ ^ 2) /
    (‖b - A (u₀ + zi)‖ ^ 2 - ‖b - A (u₀ + zj)‖ ^ 2))
  τ • zi + (1 - τ) • zj

end GlobalInexactNewton.Backtracking.Supplement


