-- Prove2me | Definitions.Def_EntrywiseLogGH_Dichotomy_IsingForm
-- name    : EntrywiseLogGH_Dichotomy_IsingForm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:29:26.835292+00:00
-- url     : https://prove2.me/theorems/6ff02639-15d2-4477-af9e-b9ed2efcf7af
-- title:
--   The Ising tensor form (1.1) and nonconstant diagonals
-- statement:
--   A real $n\times n$ matrix $M$ has the **Ising form (1.1)** if, after one simultaneous permutation of rows and columns,
--   $$M=\lambda\bigotimes_{i=1}^{d}\begin{pmatrix}a_i&b_i\\ b_i&a_i\end{pmatrix},\qquad \lambda>0,\ a_i,b_i>0,\ a_i\neq b_i .$$
--   Indexing the rows of the tensor product by $\{0,1\}^d$, its $(u,v)$ entry is $\prod_i(a_i$ if $u_i=v_i$ else $b_i)$. The empty product $d=0$ is allowed ($n=1$, $M=(\lambda)$). $M$ has **nonconstant diagonal** if $|\{M_{ii}\}|\ge2$. The Ising form is the tractable side of the paper's dichotomy.
--
--   **Formalization Note.** `IsIsingForm n M` asks for `d : ℕ`, `λ > 0`, `a b : Fin d → ℝ` with `0 < a i`, `0 < b i`, `a i ≠ b i`, and a bijection `π : Fin n ≃ (Fin d → Fin 2)` (absorbing the permutation, the Kronecker index order and the order of the factors) with `M x y = λ * ∏ i, (if π x i = π y i then a i else b i)`. `HasNonconstantDiagonal n M := ∃ i j, M i i ≠ M j j`.
-- source:
--   Cai, Tang, Entrywise Logarithmic Matrix Algebra and Dichotomy of Planar Graph Homomorphisms, arXiv:2610.00828 (held copy, sha256 4fd56ea7…a7cd), p. 15, (1.1); p. 19 (nonconstant diagonal); p. 82, Appendix C ('An empty Ising tensor is allowed')

import Mathlib

set_option autoImplicit false

/-!
# The Ising form (1.1) and nonconstant diagonals

Cai, Tang, *Entrywise Logarithmic Matrix Algebra and Dichotomy of Planar Graph Homomorphisms*,
arXiv:2610.00828 (held copy, sha256 4fd56ea7…a7cd), §1 p. 15, (1.1); §2.5 p. 19.

"… after one simultaneous permutation of rows and columns,
M = λ ⨂_{i=1}^{d} (a_i b_i ; b_i a_i),  λ > 0,  a_i, b_i > 0,  a_i ≠ b_i.  (1.1)"

"We say a matrx M ∈ R^{n×n} has nonconstant diagonal, if |{M_ii | 1 ≤ i ≤ n}| ≥ 2."

Conventions. The rows of `⨂_{i<d} (a_i b_i ; b_i a_i)` are indexed by `{0,1}^d = Fin d → Fin 2`;
its `(u, v)` entry is `Π_i (a_i if u_i = v_i else b_i)`. One simultaneous permutation of rows and
columns (together with the identification of `[n]` with `{0,1}^d` and the order of the tensor
factors) is a bijection `π : Fin n ≃ (Fin d → Fin 2)`. `d = 0` is allowed (the empty tensor
product, `n = 1`, `M = (λ)`; Appendix C, p. 82: "An empty Ising tensor is allowed").
-/

namespace EntrywiseLogGH.Dichotomy

/-- `M` has the **Ising form (1.1)** up to one simultaneous permutation of rows and columns:
`M_xy = λ Π_{i<d} (a_i if π(x)_i = π(y)_i else b_i)` with `λ > 0`, `a_i, b_i > 0`, `a_i ≠ b_i`. -/
def IsIsingForm (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ d : ℕ, ∃ lam : ℝ, 0 < lam ∧ ∃ a b : Fin d → ℝ, (∀ i, 0 < a i ∧ 0 < b i ∧ a i ≠ b i) ∧
    ∃ π : Fin n ≃ (Fin d → Fin 2), ∀ x y,
      M x y = lam * ∏ i, (if π x i = π y i then a i else b i)

/-- `M` has **nonconstant diagonal** (p. 19): `|{M_ii}| ≥ 2`. -/
def HasNonconstantDiagonal (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ i j : Fin n, M i i ≠ M j j

end EntrywiseLogGH.Dichotomy


