-- Prove2me | Definitions.Def_ROLDescent_sumMap
-- name    : ROLDescent_sumMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:04.480829+00:00
-- url     : https://prove2.me/theorems/6fb972b1-b3d8-47ad-ab08-f0f0e5ded1c7
-- title:
--   Summation map $\mathsf S$ of a family of subspaces
-- statement:
--   Let $\mathcal U_1, \dots, \mathcal U_m$ be subspaces of a finite-dimensional Hilbert space $\mathcal H$ with isometric inclusions $J_i : \mathcal U_i \hookrightarrow \mathcal H$. On the orthogonal direct sum the **summation map** and **Gram operator** are
--
--   $$\mathsf S : \bigoplus_i \mathcal U_i \to \mathcal H, \quad \mathsf S\big((u_i)_i\big) = \sum_i J_i u_i, \qquad C = \mathsf S^* \mathsf S .$$
--
--   The direct sum keeps separate copies of the subspaces; their images need not be orthogonal, and the off-diagonal blocks $J_i^* J_j$ of $C$ measure their overlap.
--
--   **Formalization Note** The orthogonal direct sum is the $\ell^2$-product `PiLp 2 (fun i => U i)` over a finite index type.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Definition 2.2, eq. (7), p.10 (PDF 10)

import Mathlib

namespace ROLDescent

/-- **Summation map of subspaces**, `S`. Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Definition 2.2, eq. (7), p.10
(PDF 10): "Let U₁, …, U_m be subspaces of a finite-dimensional Hilbert space H, and let
J_i : U_i ↪ H be their isometric inclusions. On the orthogonal direct sum, define the summation
map and Gram operator by S : ⊕_i U_i → H, S((u_i)_i) = Σ_i J_i u_i, C := S*S."

**Formalization Note** The orthogonal direct sum is `PiLp 2 (fun i => U i)` (the ℓ²-sum of the
subspaces, kept as separate copies) over a finite index type `ι` for `1, …, m`. The Gram operator is
`C = adjoint (sumMap U) ∘L sumMap U`. -/
noncomputable def sumMap {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (U : ι → Submodule ℂ H) : PiLp 2 (fun i => ↥(U i)) →L[ℂ] H :=
  ∑ i, (U i).subtypeL ∘L PiLp.proj 2 (fun i => ↥(U i)) i

end ROLDescent


