-- Prove2me | Definitions.Def_AnchoredEP_taylorOp
-- name    : AnchoredEP_taylorOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:58.520524+00:00
-- url     : https://prove2.me/theorems/4517cc66-2f94-4463-97ce-18a803da33fc
-- title:
--   Taylor approximation $\mathbb T^{(p-1)}(z;y)$ of an operator
-- statement:
--   For $F:\mathbb R^d\to\mathbb R^d$ that is $p-1$ times differentiable, the **$(p-1)$th-order Taylor approximation** of $F$ with center $y$ is
--   $$
--   \mathbb T^{(p-1)}(z;y)=F(y)+\sum_{i=1}^{p-1}\frac1{i!}D^iF(y)[z-y]^i ,
--   $$
--   where $D^iF(y)[h]^i$ is the $i$th derivative applied to $i$ copies of $h$.
--
--   It is the surrogate from which the $p$th-order method builds its subproblems.
--
--   **Formalization Note** The Lean sum runs over $i=0,\dots,p-1$; its $i=0$ term is $F(y)$. The arguments are ordered (center, point): `taylorOp F p y z` is $\mathbb T^{(p-1)}(z;y)$.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Section 5, p.11

import Mathlib

namespace AnchoredEP

/-- **The `(p−1)`th-order Taylor approximation of `F`.** Jiang–Yoon, arXiv:2609.30212, Section 5,
p.11: "Define the `(p − 1)`th-order Taylor approximation as
`𝕋^{(p−1)}(z′; z) := F(z) + ∑_{i=1}^{p−1} (1/i!) D^iF(z)[z′ − z]^i`."

`taylorOp F p y z` is `𝕋^{(p−1)}(z; y)`: the Taylor model with **center `y`**, evaluated at `z`.

**Formalization Note.** The sum runs over `i ∈ Finset.range p = {0, …, p−1}`; the `i = 0` term is
`iteratedFDeriv ℝ 0 F y (fun _ => z - y) = F y`, and `iteratedFDeriv ℝ i F y (fun _ => h)` is
`D^iF(y)[h]^i`. -/
noncomputable def taylorOp {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (y z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∑ i ∈ Finset.range p, ((i.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ i F y (fun _ => z - y)

end AnchoredEP


