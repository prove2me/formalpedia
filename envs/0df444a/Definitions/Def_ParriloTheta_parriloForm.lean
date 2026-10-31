-- Prove2me | Definitions.Def_ParriloTheta_parriloForm
-- name    : ParriloTheta_parriloForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:18.779124+00:00
-- url     : https://prove2.me/theorems/f4e0f033-7054-4043-9fba-037a49bbd2c0
-- title:
--   Parrilo form $(\sum_i x_i^2)^r\,(x^{\circ 2})^{T} M x^{\circ 2}$
-- statement:
--   Let $M$ be a real matrix indexed by a finite set $\iota$ (the paper's $[n]$), and let $r\in\mathbb N$. Write $x^{\circ 2}=(x_i^2)_{i\in\iota}$ for the entrywise square of the vector of variables. The **Parrilo form** of order $r$ is the real polynomial
--   $$
--   \Big(\sum_{i\in\iota}x_i^2\Big)^{r}\,(x^{\circ 2})^{T}Mx^{\circ 2}=\Big(\sum_{i}x_i^2\Big)^{r}\sum_{i,j}M_{ij}\,x_i^2x_j^2 .
--   $$
--   For $r=0$ it is the quartic form $(x^{\circ2})^TMx^{\circ2}$, which is nonnegative on $\mathbb R^n$ exactly when $M$ is copositive. Asking that this polynomial be a sum of squares defines Parrilo's cones $\mathcal K^{(r)}_n$.
--
--   **Formalization Note** Polynomials are `MvPolynomial ι ℝ`. On `Fin n` this is the published `SemialgebraicSDP.Copositive.formPr` (checked by `rfl` in a verification file).
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, eq. (1.4), p.2

import Mathlib

open MvPolynomial

namespace ParriloTheta

/-- **The Parrilo form `(∑ᵢ xᵢ²)^r (x∘2)ᵀ M x∘2`.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, eq. (1.4),
p.2: the polynomial `(∑_{i=1}^n x_i^2)^r (x∘2)ᵀ M x∘2`, where `x∘2 = (x_1^2, …, x_n^2)`.

For a real matrix `M` indexed by a finite type `ι` and `r : ℕ` this is the real polynomial
`(∑ᵢ Xᵢ²)^r · ∑ᵢ ∑ⱼ Mᵢⱼ Xᵢ² Xⱼ²` in the variables `Xᵢ`, `i ∈ ι`.

**Formalization Note.** The paper's index set `[n]` is a general finite type `ι`; polynomials are
`MvPolynomial ι ℝ`. -/
noncomputable def parriloForm {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (r : ℕ) :
    MvPolynomial ι ℝ :=
  (∑ i, X i ^ 2) ^ r * ∑ i, ∑ j, C (M i j) * X i ^ 2 * X j ^ 2

end ParriloTheta


