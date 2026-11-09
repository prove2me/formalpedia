-- Prove2me | Definitions.Def_DetComplexityPowerSum_Quadratic_BezoutNumber
-- name    : DetComplexityPowerSum_Quadratic_BezoutNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:24:21.696473+00:00
-- url     : https://prove2.me/theorems/127e6b0c-36f0-449d-bf22-c8af6b62f2cb
-- title:
--   §3.4 — block degrees and the multi-homogeneous Bézout number
-- statement:
--   Let the variables be partitioned into disjoint finite blocks $x_j$, $j\in\kappa$, with $|x_j|=n_j$. The **block degree** of a polynomial $P$ in block $j$ is the largest value, over the monomials of $P$, of the sum of the exponents of the variables of $x_j$. It is the degree of $P$ in the variables $x_j$, the other blocks being treated as coefficients, and it is $0$ for $P=0$.
--
--   Given natural numbers $d_{i,j}$, for equations $i$ and blocks $j$, the **Bézout number** is
--   $$B=\text{the coefficient of }\ \prod_{j}y_j^{n_j}\ \text{ in }\ \prod_{i}\Bigl(\sum_{j}d_{i,j}\,y_j\Bigr).$$
--
--   These two notions are the data of the multi-homogeneous Bézout theorem (Theorem 3.11).
--
--   **Formalization Note** Blocks are the fibres of a sigma type `Σ j, α j`, and the product is taken in `MvPolynomial κ ℕ`. The block degree sums exponents within a block; it is neither the largest exponent of a single variable nor the total degree across blocks.
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 8-9, §3.4 and Theorem 3.11

import Mathlib

namespace DetComplexityPowerSum.Quadratic

open MvPolynomial

/-- The degree of `P` in the block `x_j` of variables: the largest value, over the monomials of
`P`, of the sum of the exponents of the variables of block `j`. It is `0` for `P = 0`. -/
noncomputable def blockDegree {κ : Type*} {α : κ → Type*} [∀ j, Fintype (α j)]
    (P : MvPolynomial (Σ j, α j) ℂ) (j : κ) : ℕ :=
  P.support.sup fun s => ∑ i : α j, s ⟨j, i⟩

/-- The Bézout number of Theorem 3.11: the coefficient of `∏ⱼ yⱼ^{nⱼ}`, with `nⱼ = |xⱼ|`, in the
product over the equations `i` of the linear forms `∑ⱼ dᵢⱼ yⱼ`. -/
noncomputable def bezoutNumber {κ E : Type*} (α : κ → Type*) [Fintype κ] [∀ j, Fintype (α j)]
    [Fintype E] (d : E → κ → ℕ) : ℕ :=
  coeff (Finsupp.equivFunOnFinite.symm fun j => Fintype.card (α j))
    (∏ i : E, ∑ j : κ, C (d i j) * X j : MvPolynomial κ ℕ)

end DetComplexityPowerSum.Quadratic


