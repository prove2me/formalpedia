-- Prove2me | Definitions.Def_IntQuotHNP_LLLReduced
-- name    : IntQuotHNP_LLLReduced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:12.406506+00:00
-- url     : https://prove2.me/theorems/38ac1ab5-56ae-422e-a557-8dbf96ca9735
-- title:
--   Definition 2.4 — Gram–Schmidt coefficients and LLL-reduced bases
-- statement:
--   For $b_1,\dots,b_m\in\mathbb R^d$, the Gram–Schmidt vectors are $\tilde b_i=b_i-\sum_{j<i}\mu_{ij}\tilde b_j$ with $\mu_{ij}=\langle b_i,\tilde b_j\rangle/\|\tilde b_j\|_2^2$. The family is **LLL-reduced with parameter $\delta$** if $|\mu_{ij}|\le1/2$ for $j<i$ and
--   $$
--   \|\tilde b_i\|_2^2\ge(\delta-\mu_{i,i-1}^2)\|\tilde b_{i-1}\|_2^2\qquad(2\le i\le m).
--   $$
--
--   **Formalization Note** The vectors $\tilde b_i$ are Mathlib's unnormalised `gramSchmidt`. Unlike the published `LLLFactor.RedBasis.IsReduced`, which is for $n$ vectors in $\mathbb R^n$, no relation between $m$ and $d$ is built in, since the paper's bound needs rank at most the ambient dimension. Linear independence and $\delta\in(1/4,1)$ are hypotheses where needed.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 2.4, p.15 (PDF p.16)

import Mathlib

namespace IntQuotHNP

open InnerProductSpace

/-- **The Gram–Schmidt coefficient `μ_ij`** (Definition 2.4).
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), Definition 2.4, p.15 (PDF p.16): "Define its Gram–Schmidt vectors recursively by
b̃_i = b_i − ∑_{j<i} μ_ij b̃_j, where μ_ij = ⟨b_i, b̃_j⟩/∥b̃_j∥₂² for j < i."

**Formalization Note.** `b̃` is Mathlib's (unnormalised) `InnerProductSpace.gramSchmidt ℝ b`, which
subtracts from `b_i` its projections on the lines spanned by `b̃_j`, `j < i`; this is the paper's
recursion. Indices are 0-based (`Fin m`). -/
noncomputable def gsMu {m d : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin d)) (i j : Fin m) : ℝ :=
  ⟪b i, gramSchmidt ℝ b j⟫_ℝ / ‖gramSchmidt ℝ b j‖ ^ 2

/-- **An LLL-reduced basis with parameter `δ`** (Definition 2.4).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 2.4, p.15 (PDF p.16):
"The basis is LLL-reduced with parameter δ if it satisfies the size-reduction conditions
|μ_ij| ≤ 1/2 for 1 ≤ j < i ≤ m and the Lovász conditions
∥b̃_i∥₂² ≥ (δ − μ²_{i,i−1})∥b̃_{i−1}∥₂² (2 ≤ i ≤ m)."

**Formalization Note.** The `m` vectors live in `ℝ^d` with no relation between `m` and `d` imposed
here (the paper has `m ≤ d`, which follows from linear independence). That `b` is a lattice basis
(linearly independent) and `δ ∈ (1/4, 1)` are hypotheses of the theorems that use this predicate.
The Lovász condition for the paper's pair `(i − 1, i)` is stated for the 0-based pair `(j, i)` with
`j + 1 = i`. -/
def IsLLLReduced {m d : ℕ} (δ : ℝ) (b : Fin m → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ i j : Fin m, j < i → |gsMu b i j| ≤ 1 / 2) ∧
    ∀ i j : Fin m, (j : ℕ) + 1 = i →
      (δ - gsMu b i j ^ 2) * ‖gramSchmidt ℝ b j‖ ^ 2 ≤ ‖gramSchmidt ℝ b i‖ ^ 2

end IntQuotHNP


