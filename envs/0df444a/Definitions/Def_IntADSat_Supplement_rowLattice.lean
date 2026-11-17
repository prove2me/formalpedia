-- Prove2me | Definitions.Def_IntADSat_Supplement_rowLattice
-- name    : IntADSat_Supplement_rowLattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:51:33.609452+00:00
-- url     : https://prove2.me/theorems/8329e8e8-96ee-4904-8804-a1da287a1ffb
-- title:
--   Transported vertex lattice $L_H=R\,\mathbb Z^{V(H)}$
-- statement:
--   For an $m\times n$ rational matrix $Q$ (a pointed intertwiner from $G$ to $H$), the lattice
--   $$L=Q^{\mathsf T}\mathbb Z^m=\operatorname{span}_{\mathbb Z}\{\text{rows of }Q\}\subseteq\mathbb Q^n .$$
--   In the proof of Theorem S5.4, $R=Q^{\mathsf T}=Q^{-1}$ is the pointed isometry from $H$ to $G$ and $L_H=R\,\mathbb Z^{V(H)}$ is the vertex lattice of $H$ transported into $V=\mathbb Q^{V(G)}$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), proof of Theorem S5.4, p.42 (PDF 43)

import Mathlib

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The vertex lattice `L_H = R ℤ^{V(H)}` of a comparison graph `H` transported into `V = ℚ^{V(G)}`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), proof of Theorem S5.4, p.42 (PDF 43)), where `R = Qᵀ = Q⁻¹` is the pointed isometry from `H` to `G`
and `Q` the one from `G` to `H`.

**Formalization Note** `R e_j = Qᵀ e_j` is the `j`-th row of the `m × n` matrix `Q`, so `L_H` is the `ℤ`-span
of the rows of `Q`. -/
def rowLattice {m n : ℕ} (Q : Matrix (Fin m) (Fin n) ℚ) : Submodule ℤ (Fin n → ℚ) :=
  Submodule.span ℤ (Set.range fun j : Fin m => Q j)

end IntADSat.Supplement


