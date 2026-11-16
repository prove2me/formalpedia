-- Prove2me | Definitions.Def_SetDefinedGraphs_Supplement_Tropical
-- name    : SetDefinedGraphs_Supplement_Tropical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:42:57.861203+00:00
-- url     : https://prove2.me/theorems/ff00b802-804b-41a5-879f-5c9384c77284
-- title:
--   Min-plus and max-plus matrix-vector products and finite solutions of tropical inequalities
-- statement:
--   Let $\mathbb Z_{\min}=\mathbb Z\cup\{\infty\}$ and $\mathbb Z_{\max}=\mathbb Z\cup\{-\infty\}$. For $A\in\mathbb Z_{\min}^{m\times n}$, $B\in\mathbb Z_{\max}^{m\times n}$ and $x\in\mathbb R^n$,
--   $$(A\otimes_{\min}x)_i=\min_{j\in[n]}\{A_{i,j}+x_j\},\qquad (B\otimes_{\max}x)_i=\max_{j\in[n]}\{B_{i,j}+x_j\}.$$
--   The min-plus system $A\otimes_{\min}x\ge B\otimes_{\min}x$ **has a finite solution** if some $x\in\mathbb R^n$ (every entry finite) satisfies it in every row; likewise for the max-plus system $A\otimes_{\max}y\le B\otimes_{\max}y$.
--
--   These systems are equivalent to mean payoff games, and Theorem 5.1 expresses unbounded chromatic number of $\vec{\mathcal Y}_{P,Z}$ by their feasibility.
--
--   **Formalization Note** $\mathbb Z_{\min}$, $\mathbb R_{\min}$ are `WithTop ℤ`, `WithTop ℝ` and $\mathbb Z_{\max}$, $\mathbb R_{\max}$ are `WithBot ℤ`, `WithBot ℝ`, so $\infty+a=\infty$ and $-\infty+a=-\infty$. The paper's display on p.19 writes $x_i$ inside the maximum; this is a typo for $x_j$, as its Example 3.11 confirms.
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §3.7 p.19 (PDF p.21): max-plus algebra and A ⊗max x; §3.7.1 p.22 (PDF p.24): min-plus algebra; Corollary 3.17: finite solution x ∈ ℝ^n

import Mathlib

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- The **min-plus matrix-vector product** `(A ⊗_min x)_i = min_j (A_{ij} + x_j)` (Adenwalla–Braunfeld–Hons–Sylvester–
Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*, arXiv:2607.23754 (held version, sha256
642c0d70…), §3.7 p.19 and §3.7.1 p.22) of a matrix `A` over `ℤ_min = ℤ ∪ {∞}` and a finite vector `x ∈ ℝ^n`, valued in
`ℝ_min = ℝ ∪ {∞}`.

**Formalization Note** `ℤ_min`, `ℝ_min` are `WithTop ℤ`, `WithTop ℝ` (`∞ + a = ∞`; the minimum over an empty index set
is `∞`). The paper's display `max_j {A_{i,j} + x_i}` (p.19) is a typo for `x_j`, as Example 3.11 confirms. -/
noncomputable def minPlusMulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) (WithTop ℤ)) (x : Fin n → ℝ) (i : Fin m) :
    WithTop ℝ :=
  Finset.univ.inf (fun j => WithTop.map (Int.cast : ℤ → ℝ) (A i j) + ((x j : ℝ) : WithTop ℝ))

/-- The **max-plus matrix-vector product** `(A ⊗_max y)_i = max_j (A_{ij} + y_j)` (arXiv:2607.23754, §3.7 p.19) of a
matrix `A` over `ℤ_max = ℤ ∪ {−∞}` and a finite vector `y ∈ ℝ^n`, valued in `ℝ_max = ℝ ∪ {−∞}`.

**Formalization Note** `ℤ_max`, `ℝ_max` are `WithBot ℤ`, `WithBot ℝ` (`−∞ + a = −∞`). -/
noncomputable def maxPlusMulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) (WithBot ℤ)) (y : Fin n → ℝ) (i : Fin m) :
    WithBot ℝ :=
  Finset.univ.sup (fun j => WithBot.map (Int.cast : ℤ → ℝ) (A i j) + ((y j : ℝ) : WithBot ℝ))

/-- The min-plus system `A ⊗_min x ≥ B ⊗_min x` **has a finite solution** (arXiv:2607.23754, §3.7.1 p.22, Corollary
3.17): some `x ∈ ℝ^n` (every entry finite) satisfies `(A ⊗_min x)_i ≥ (B ⊗_min x)_i` for every row `i`. -/
def MinPlusHasFiniteSolution {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (WithTop ℤ)) : Prop :=
  ∃ x : Fin n → ℝ, ∀ i, minPlusMulVec B x i ≤ minPlusMulVec A x i

/-- The max-plus system `A ⊗_max y ≤ B ⊗_max y` **has a finite solution** (arXiv:2607.23754, §3.7 p.19): some
`y ∈ ℝ^n` (every entry finite) satisfies `(A ⊗_max y)_i ≤ (B ⊗_max y)_i` for every row `i`. -/
def MaxPlusHasFiniteSolution {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (WithBot ℤ)) : Prop :=
  ∃ y : Fin n → ℝ, ∀ i, maxPlusMulVec A y i ≤ maxPlusMulVec B y i

end SetDefinedGraphs.Supplement


