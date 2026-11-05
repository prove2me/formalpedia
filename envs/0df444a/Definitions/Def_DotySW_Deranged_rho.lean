-- Prove2me | Definitions.Def_DotySW_Deranged_rho
-- name    : DotySW_Deranged_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:10.202203+00:00
-- url     : https://prove2.me/theorems/9ad94a52-158f-449b-a6ce-64c764ae87ee
-- title:
--   The action $\rho$ of $\mathrm{GL}_n$ on mixed tensor space
-- statement:
--   For $g\in\mathrm{GL}_n(\mathbb C)$, $\rho(g)$ is the operator on $V^{r,s}=V^{\otimes r}\otimes V^{*\otimes s}$ that applies $g$ in each of the first $r$ positions and the contragredient $(g^{-1})^{\mathsf T}$ in each of the last $s$ positions. In coordinates,
--
--   $$
--   \rho(g)_{i,j}=\prod_{a<r} g_{i(a),\,j(a)}\;\prod_{b<s}(g^{-1})_{j(r+b),\,i(r+b)}.
--   $$
--
--   This is the natural structure of $V^{r,s}$ as a $\mathrm{GL}_n$-module, the left arrow of the diagram (13).
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.4, unnumbered and Eq. (13), p. 9

import Mathlib
import Definitions.Def_DotySW_Deranged_Op

namespace DotySW.Deranged

/-- **The action `ρ` of `GL_n` on mixed tensor space `V^{r,s} = V^{⊗r} ⊗ V^{*⊗s}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.4, unnumbered and Eq. (13), p. 9.

`g` acts on each of the first `r` positions and by the contragredient `(g⁻¹)ᵀ` on each of the
last `s` positions.

**Formalization Note** Coordinates as in `Idx` and `Op`: the entry at row `i`, column `j` is
`∏ a, g (i a) (j a)` over the first `r` positions times `∏ b, g⁻¹ (j b) (i b)` over the last `s`.
The swapped indices on `g⁻¹` are the transpose. -/
def rho (n r s : ℕ) (g : GL (Fin n) ℂ) : Op n (r + s) :=
  Matrix.of fun i j =>
    (∏ a : Fin r, (g : Matrix (Fin n) (Fin n) ℂ) (i (Fin.castAdd s a)) (j (Fin.castAdd s a))) *
      ∏ b : Fin s, ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
        (j (Fin.natAdd r b)) (i (Fin.natAdd r b))

end DotySW.Deranged


