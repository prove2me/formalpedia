-- Prove2me | Definitions.Def_NewtonLCP_BitBound
-- name    : NewtonLCP_BitBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:38.155871+00:00
-- url     : https://prove2.me/theorems/a7275ef4-117c-4386-93da-e83ce618fb15
-- title:
--   The bit bound $\Delta$ of Lemma 8.3
-- statement:
--   Let $M\in\mathbb R^{n\times n}$, $q\in\mathbb R^n$. An integer $\Delta\ge1$ is a **bit bound** for $(M,q)$ if
--
--   1. $\|M\|_{\max}+\|q\|_\infty\le\Delta$, and
--   2. for every basic feasible solution $(x,s)$ of the polyhedron $\mathcal F(M,q)$ and every $i\in[n]$, $x_i,s_i\in\{0\}\cup[1/\Delta,\Delta]$.
--
--   Lemma 8.3 states that rational data of encoding length $L$ admit a bit bound $\Delta\le2^{O(L)}$; Lemmas 8.4 and 8.5 use only this property of $\Delta$.
--
--   **Formalization Note** A basic feasible solution is an extreme point of $\mathcal F(M,q)\subseteq\mathbb R^{2n}$. $\|M\|_{\max}+\|q\|_\infty\le\Delta$ is written as $|M_{ij}|+|q_k|\le\Delta$ for all $i,j,k$. The condition $\Delta\ge1$ makes explicit what the paper's $[1/\Delta,\Delta]$ for an integer $\Delta$ presupposes.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Lemma 8.3, p.29

import Mathlib
import Definitions.Def_NewtonLCP_LCP

namespace NewtonLCP

/-!
# The bit bound `∆` of Lemma 8.3

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), Lemma 8.3, p.29.

`IsBitBound M q ∆` is the property Lemma 8.3 asserts of its integer `∆`:
`‖M‖_max + ‖q‖_∞ ≤ ∆`, and every coordinate of every basic feasible solution `(x, s)` of the
polyhedron `F(M, q)` lies in `{0} ∪ [1/∆, ∆]`.

**Formalization Note.** A basic feasible solution of `F(M, q) ⊆ ℝ²ⁿ` is an extreme point of
`F(M, q)` (`Set.extremePoints ℝ`). `‖M‖_max + ‖q‖_∞ ≤ ∆` is written `∀ i j k, |Mᵢⱼ| + |q_k| ≤ ∆`,
which is the same for `n ≥ 1`. The clause `1 ≤ ∆` makes explicit what the paper presupposes when
it writes `1/∆` for an integer `∆`.
-/

variable {ι : Type*} [Fintype ι]

/-- `∆` is a bit bound for `(M, q)` in the sense of Lemma 8.3. -/
def IsBitBound (M : Matrix ι ι ℝ) (q : ι → ℝ) (Δ : ℤ) : Prop :=
  1 ≤ Δ ∧ (∀ i j k, |M i j| + |q k| ≤ Δ) ∧
    ∀ p ∈ (Feas M q).extremePoints ℝ, ∀ i,
      (p.1 i = 0 ∨ (1 / (Δ : ℝ) ≤ p.1 i ∧ p.1 i ≤ Δ)) ∧
      (p.2 i = 0 ∨ (1 / (Δ : ℝ) ≤ p.2 i ∧ p.2 i ≤ Δ))

end NewtonLCP


