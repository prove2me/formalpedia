-- Prove2me | Definitions.Def_FermionDirac_gamma
-- name    : FermionDirac_gamma
-- status  : Definition
-- author  : @LG
-- created : 2026-11-25T01:14:40.374409+00:00
-- url     : https://prove2.me/theorems/190958d9-89a9-4647-8b6b-b11f55d86cc8
-- title:
--   The Dirac gamma matrices in the chiral representation, as $4\times4$ complex matrices
-- statement:
--   The **Dirac gamma matrices in the chiral (Weyl) representation**, written entrywise as $4\times4$ complex matrices. In $2\times2$ blocks,
--   $$\gamma^0=\begin{pmatrix}0&I_2\\ I_2&0\end{pmatrix},\qquad \gamma^i=\begin{pmatrix}0&\sigma_i\\ -\sigma_i&0\end{pmatrix}\quad(i=1,2,3),$$
--   where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices. They satisfy the Clifford relation $\gamma^\mu\gamma^\nu+\gamma^\nu\gamma^\mu=2\eta^{\mu\nu}I_4$ with $\eta=\mathrm{diag}(1,-1,-1,-1)$, so they form a Clifford family of size four — the attainment half of the theorem that the gamma matrices need four dimensions (Dirac, 1928).
--
--   **Formalization Note.** These are exactly the matrices of Physlib's Dirac endomorphisms `Fermion.Dirac.gamma` in the chiral basis (Physlib's `gamma_toMatrix`); the mission realizes them directly as matrices rather than through the spinor-space endomorphism machinery, which is the content of Physlib's `isCliffordFamily_gamma` after applying `endEquivMatrix`. The time summand of the index type is a singleton, so its single matrix is given by a wildcard pattern.
-- source:
--   Physlib, `Physlib/Relativity/Fermions/Dirac/GammaMatrices.lean`, `gamma_toMatrix` (L161–L170), the chiral-basis matrices of `gamma` (L142–L143). https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/Relativity/Fermions/Dirac/GammaMatrices.lean#L161-L170

import Mathlib

namespace Fermion.Dirac

open Matrix

/-- The Dirac gamma endomorphisms `γ^μ`, written as `4 × 4` complex matrices in the chiral (Weyl)
basis: in `2 × 2` blocks, `γ^0 = [[0, 1], [1, 0]]` and `γ^i = [[0, σ^i], [-σ^i, 0]]`. These are the
matrices of Physlib's `gamma` in the chiral basis (`gamma_toMatrix`). -/
def gamma (μ : Fin 1 ⊕ Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  match μ with
  | Sum.inl _ => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | Sum.inr 0 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  | Sum.inr 1 => !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0; 0, Complex.I, 0, 0; -Complex.I, 0, 0, 0]
  | Sum.inr 2 => !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

end Fermion.Dirac


