-- Prove2me | Definitions.Def_IntADSat_Supplement_preLattice
-- name    : IntADSat_Supplement_preLattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:50:35.988866+00:00
-- url     : https://prove2.me/theorems/150607d2-3c02-46fa-983b-7a3323f95c12
-- title:
--   Lattice corresponding to a subgroup of $D_\Lambda$
-- statement:
--   For a subgroup $S\le D_\Lambda$, the lattice $L_S$ is its inverse image under the quotient map $\Lambda^\#\to D_\Lambda=\Lambda^\#/\Lambda$; thus $\Lambda\subseteq L_S\subseteq\Lambda^\#$ and $S=L_S/\Lambda$. Lemma S5.1 uses this correspondence between subgroups of $D_\Lambda$ and intermediate lattices.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Lemma S5.1, p.41 (PDF 42)

import Mathlib
import Definitions.Def_IntADSat_Supplement_discGroup

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The lattice `L` with `Λ ⊆ L ⊆ Λ^#` corresponding to a subgroup `S ≤ D_Λ`: the inverse image of `S` under
`Λ^# → D_Λ` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma S5.1, p.41 (PDF 42): `S = L/Λ`).

**Formalization Note** `S` is a `ℤ`-submodule (= subgroup) of `D_Λ`; the preimage in `Λ^#` is mapped into
`V = ℚⁿ`. -/
noncomputable def preLattice {n : ℕ} (G : SimpleGraph (Fin n)) (S : Submodule ℤ (discGroup G)) :
    Submodule ℤ (Fin n → ℚ) :=
  (S.comap (Submodule.mkQ _)).map (dualLattice (vecLattice G)).subtype

end IntADSat.Supplement


