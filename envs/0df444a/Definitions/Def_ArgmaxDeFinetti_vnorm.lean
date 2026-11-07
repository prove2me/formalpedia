-- Prove2me | Definitions.Def_ArgmaxDeFinetti_vnorm
-- name    : ArgmaxDeFinetti_vnorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:14.505052+00:00
-- url     : https://prove2.me/theorems/f9dbb556-024c-4f59-b33b-aae03c5c6d5d
-- title:
--   Euclidean inner product and norm on $\mathbb C^\iota$
-- statement:
--   For a finite index set $\iota$, the space $\mathbb C^\iota$ carries the inner product
--   $$
--   \langle x,y\rangle=\sum_{i\in\iota}\overline{x_i}\,y_i ,
--   $$
--   conjugate-linear in the first argument, and the Hilbert-space norm $\|x\|=\big(\sum_i |x_i|^2\big)^{1/2}$.
--
--   Every Hilbert space of the paper ($\mathbb C^d$, its tensor powers, $\mathcal X\otimes\mathcal Y$) is such a coordinate space with its standard orthonormal basis, and every condition $\|u\|=1$ in the mission refers to this norm.
--
--   **Formalization Note** The norm is defined explicitly; it is not Mathlib's default norm on function types, which is the sup norm.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18 (inner-product convention and Hilbert-space norm)

import Mathlib

open Matrix

namespace ArgmaxDeFinetti

/-- The Hermitian inner product `⟨x, y⟩ = Σᵢ conj(xᵢ) yᵢ` on `ι → ℂ`, conjugate-linear in the first
argument, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18 ("inner products … conjugate-linear in the first argument").

**Formalization Note** Every vector space of the paper (`ℂ^d`, `(ℂ^d)^{⊗n}`, `X ⊗ Y`) is a
coordinate space `ι → ℂ` with its standard orthonormal basis; `vinner` is its inner product. -/
def vinner {ι : Type} [Fintype ι] (x y : ι → ℂ) : ℂ :=
  ∑ i, star (x i) * y i

/-- The Euclidean (Hilbert-space) norm `‖x‖ = (Σᵢ |xᵢ|²)^{1/2}` on `ι → ℂ`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18
("For a vector v, the notation ∥v∥ denotes its Hilbert-space norm").

**Formalization Note** This is deliberately not Mathlib's default norm on the function type
`ι → ℂ`, which is the sup norm. Every condition `∥u∥ = 1` of the paper is `vnorm u = 1`. -/
noncomputable def vnorm {ι : Type} [Fintype ι] (x : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

end ArgmaxDeFinetti


