-- Prove2me | Definitions.Def_NashPoly_Generic_ComplexKKT
-- name    : NashPoly_Generic_ComplexKKT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:58.516994+00:00
-- url     : https://prove2.me/theorems/149b734f-7419-4c53-b8e7-99258f1edb14
-- title:
--   (A.1), p. 28; p. 8 — complex solutions of the KKT system (A.1) and nonsingular constraining tuples
-- statement:
--   This file defines two complex-algebraic objects used in the genericity results.
--
--   **The complex KKT system** (A.1). For a NEPP with only equality constraints, the KKT system for all players is
--   $$\sum_{j=1}^{m_i}\lambda_{i,j}\nabla_{x_i}g_{i,j}(x_i)=\nabla_{x_i}f_i(x)\quad(i\in[N]),\qquad g_{i,j}(x_i)=0\quad(i\in[N],\ j\in[m_i]).$$
--   Its complex solution set is the set of pairs $(x,\lambda)\in\mathbb C^n\times\prod_i\mathbb C^{m_i}$ satisfying these equations, the real polynomials $f_i,g_{i,j}$ being evaluated at complex points. Sign conditions on $\lambda$ are ignored.
--
--   **Nonsingularity** (p. 8). A tuple $g=(g_1,\dots,g_m)$ of real polynomials in $z\in\mathbb R^{n'}$ is *nonsingular* if the matrix $G(\xi)$ of (3.1) has full column rank for every complex point $\xi\in\mathbb C^{n'}$:
--   $$\operatorname{rank} G(\xi)=m\qquad\text{for all }\xi\in\mathbb C^{n'} .$$
--
--   The first object is the subject of Theorem A.1; the second is the standing assumption of §3 and the first step of the proof of Theorem A.1.
--
--   **Formalization Note** The multipliers are indexed by pairs $(i,j)$, $j\in[m_i]$. Evaluation at complex points uses the algebra map $\mathbb R\to\mathbb C$. Full column rank is linear independence of the columns of $G(\xi)$ over $\mathbb C$.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 28, (A.1); p. 8, nonsingularity of g_i

import Mathlib
import Definitions.Def_NashPoly_Generic_MultiplierExpr

namespace NashPoly.Generic

open MvPolynomial

variable {N : ℕ} {n m : Fin N → ℕ}

/-- The complex solutions `(x, λ) ∈ ℂ^n × ∏_i ℂ^{m_i}` of the KKT system (A.1), p. 28, of the
equality-constrained NEP with objectives `f` and constraints `g`:
`Σ_j λ_{i,j} ∇_{x_i} g_{i,j}(x_i) = ∇_{x_i} f_i(x)` (`i ∈ [N]`) and `g_{i,j}(x_i) = 0` (all `i, j`).
The real polynomials are evaluated at complex points. -/
def A1Sol (f : Fin N → MvPolynomial (Var n) ℝ)
    (g : (i : Fin N) → Fin (m i) → MvPolynomial (Fin (n i)) ℝ) :
    Set ((Var n → ℂ) × ((Σ i, Fin (m i)) → ℂ)) :=
  {p | ∀ i,
    (∀ k : Fin (n i), ∑ j, p.2 ⟨i, j⟩ * aeval (fun k' => p.1 ⟨i, k'⟩) (pderiv k (g i j)) =
      aeval p.1 (pderiv ⟨i, k⟩ (f i))) ∧
    ∀ j, aeval (fun k' => p.1 ⟨i, k'⟩) (g i j) = 0}

/-- A constraining tuple `g = (g_1, …, g_m)` in `ℝ[z]`, `z ∈ ℝ^{n'}`, is nonsingular (p. 8) if
`G(ξ)` of (3.1) has full column rank (linearly independent columns) for every `ξ ∈ ℂ^{n'}`. -/
def Nonsingular {n' m' : ℕ} (g : Fin m' → MvPolynomial (Fin n') ℝ) : Prop :=
  ∀ ξ : Fin n' → ℂ, LinearIndependent ℂ (fun j : Fin m' => fun r => aeval ξ (Gmat g r j))

end NashPoly.Generic


