-- Prove2me | Definitions.Def_IntADSat_Supplement_vecLattice
-- name    : IntADSat_Supplement_vecLattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:46:50.180296+00:00
-- url     : https://prove2.me/theorems/67a73cc1-f542-4a0e-9ecf-a9420d4bfe4d
-- title:
--   Word lattice in $V=\mathbb Q^{V(G)}$
-- statement:
--   The word lattice $\Lambda=\Lambda_G=\mathbb Z\langle A,D\rangle e\subseteq\mathbb Z^n$ viewed inside the rational space $V=\mathbb Q^{V(G)}$ with its standard inner product, as in Section S5. For an AD-full graph it has full rank in $V$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), §S5, p.40 (PDF 41)

import Mathlib
import Definitions.Def_IntADSat_wordLattice
import Definitions.Def_IntADSat_Supplement_castVec

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The word lattice `Λ = Λ_G` viewed inside the rational space `V = ℚ^{V(G)}`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §S5, p.40 (PDF 41)).

**Formalization Note** The image of the published `IntADSat.wordLattice G ⊆ ℤⁿ` under the coordinatewise
inclusion `ℤⁿ ↪ ℚⁿ`. -/
noncomputable def vecLattice {n : ℕ} (G : SimpleGraph (Fin n)) : Submodule ℤ (Fin n → ℚ) :=
  (IntADSat.wordLattice G).map (castVec n)

end IntADSat.Supplement


