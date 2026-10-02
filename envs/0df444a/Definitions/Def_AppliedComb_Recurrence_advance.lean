-- Prove2me | Definitions.Def_AppliedComb_Recurrence_advance
-- name    : AppliedComb_Recurrence_advance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:14:09.963605+00:00
-- url     : https://prove2.me/theorems/4f91f051-d43a-4179-9dcb-0c05e91b18eb
-- title:
--   Sections 9.3 and 9.5 — the advancement operator A, operator polynomials p(A), and the solution space W
-- statement:
--   Let $V$ be the real vector space of all functions $f : \mathbb{Z} \to \mathbb{R}$, with pointwise addition $(f+g)(n) = f(n) + g(n)$ and scalar multiplication $(\alpha f)(n) = \alpha\, f(n)$.
--
--   The **advancement operator** $A : V \to V$ is defined by $A f(n) = f(n+1)$. It is a linear operator, and its $p$-th power (composition) satisfies $A^p f(n) = f(n+p)$ for every nonnegative integer $p$.
--
--   Given a nonnegative integer $k$ and real constants $c_0, c_1, \dots, c_k$, the **advancement operator polynomial** is the linear operator
--
--   $$p(A) = c_0 A^k + c_1 A^{k-1} + c_2 A^{k-2} + \cdots + c_k,$$
--
--   so that $p(A) f(n) = c_0 f(n+k) + c_1 f(n+k-1) + \cdots + c_k f(n)$ for all $n \in \mathbb{Z}$. The **solution space** $W$ of the homogeneous equation $p(A) f = 0$ is the set of all $f \in V$ with $p(A) f = 0$, that is, the kernel of $p(A)$; it is a linear subspace of $V$.
--
--   These are the objects of the chapter's Principal Theorem 9.18: solving a linear recurrence with constant coefficients means describing $W$.
--
--   **Formalization Note.** `advance` is $A$ as a `Module.End ℝ (ℤ → ℝ)`. `opPoly k c` is $p(A)$ for a coefficient vector `c : Fin (k + 1) → ℝ`, where `c i` multiplies `advance ^ (k - i)`; since `i ≤ k` the natural-number subtraction is exact, so `c 0` is the leading coefficient $c_0$ and `c (Fin.last k)` the constant term $c_k$. `solutionSpace k c` is `LinearMap.ker (opPoly k c)`, a `Submodule ℝ (ℤ → ℝ)`. Functions are indexed by all of $\mathbb{Z}$, as in Section 9.5, not by $\mathbb{N}$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 188, Section 9.3 and p. 199, Section 9.5

import Mathlib

namespace AppliedComb.Recurrence

/-- Keller–Trotter, Sections 9.3 and 9.5 (pp. 188, 199). The advancement operator `A` on the
real vector space `V` of all functions `f : ℤ → ℝ`, defined by `A f (n) = f (n + 1)`. It is a
linear operator on `V`, so `A ^ p` (composition) satisfies `A ^ p f (n) = f (n + p)`. -/
def advance : Module.End ℝ (ℤ → ℝ) where
  toFun f := fun n => f (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Keller–Trotter, Section 9.5 (p. 199, Eq. (9.5.1)). The advancement operator polynomial
`p(A) = c₀ A^k + c₁ A^(k-1) + c₂ A^(k-2) + ⋯ + c_k` with real coefficients `c₀, …, c_k`,
as a linear operator on `V = (ℤ → ℝ)`. The coefficient `c i` multiplies `A ^ (k - i)`
(here `i ≤ k`, so the natural-number subtraction is exact). -/
noncomputable def opPoly (k : ℕ) (c : Fin (k + 1) → ℝ) : Module.End ℝ (ℤ → ℝ) :=
  ∑ i : Fin (k + 1), c i • advance ^ (k - (i : ℕ))

/-- Keller–Trotter, Section 9.5 (p. 199). The set `W` of all solutions `f : ℤ → ℝ` of the
homogeneous equation `(c₀ A^k + c₁ A^(k-1) + ⋯ + c_k) f = 0`, i.e. the kernel of `p(A)`,
as a subspace of `V`. -/
noncomputable def solutionSpace (k : ℕ) (c : Fin (k + 1) → ℝ) : Submodule ℝ (ℤ → ℝ) :=
  LinearMap.ker (opPoly k c)

end AppliedComb.Recurrence


