-- Prove2me | Definitions.Def_ParriloTheta_InK
-- name    : ParriloTheta_InK
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:02.100326+00:00
-- url     : https://prove2.me/theorems/c86a6310-4a43-4608-9f7e-52fc89f458bc
-- title:
--   Parrilo's cone $\mathcal K^{(r)}_n$
-- statement:
--   For $r\in\mathbb N$, **Parrilo's cone** $\mathcal K^{(r)}_n$ is the set of symmetric $n\times n$ real matrices $M$ for which
--   $$
--   \Big(\sum_{i=1}^n x_i^2\Big)^{r}\,(x^{\circ 2})^{T}Mx^{\circ 2}\in\Sigma ,
--   $$
--   where $\Sigma$ is the cone of sums of squares of real polynomials and $x^{\circ2}=(x_1^2,\dots,x_n^2)$. These cones increase with $r$, lie inside the copositive cone, and their union covers its interior; they are the inner approximations behind the bounds $\vartheta^{(r)}(G)$.
--
--   **Formalization Note** `InK r M` is `M.IsSymm ∧ IsSumSq (parriloForm M r)`; the index set is a general finite type.
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, eq. (1.4), p.2

import Mathlib
import Definitions.Def_ParriloTheta_parriloForm

namespace ParriloTheta

/-- **Parrilo's cone `K^(r)_n`.**
Laurent & Vargas, arXiv:2109.12876v1, eq. (1.4), p.2:
"K(r)_n = {M ∈ Sⁿ : (∑_{i=1}^n x_i^2)^r (x∘2)ᵀ M x∘2 ∈ Σ} for r ∈ N, where Σ denotes the cone of
sums of squares of polynomials."

`InK r M` says that `M` is symmetric and `(∑ᵢ xᵢ²)^r (x∘2)ᵀ M x∘2` is a sum of squares of
real polynomials.

**Formalization Note.** `Sⁿ` (symmetric matrices) is `M.IsSymm`; `Σ` is Mathlib's `IsSumSq` in
`MvPolynomial ι ℝ` (finite sums of squares, the empty sum included). The index set `[n]` is a
general finite type `ι`. -/
def InK {ι : Type*} [Fintype ι] (r : ℕ) (M : Matrix ι ι ℝ) : Prop :=
  M.IsSymm ∧ IsSumSq (parriloForm M r)

end ParriloTheta


