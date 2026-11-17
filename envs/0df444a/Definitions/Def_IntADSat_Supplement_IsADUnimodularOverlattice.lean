-- Prove2me | Definitions.Def_IntADSat_Supplement_IsADUnimodularOverlattice
-- name    : IntADSat_Supplement_IsADUnimodularOverlattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:47:46.712841+00:00
-- url     : https://prove2.me/theorems/446bd0ff-64ca-45ee-b8b4-dadaa7c72dd3
-- title:
--   $A,D$-stable integral unimodular overlattice of $\Lambda_G$
-- statement:
--   A lattice $L\subseteq V=\mathbb Q^{V(G)}$ is an **$A,D$-stable integral unimodular overlattice** of $\Lambda=\Lambda_G$ if
--
--   1. $\Lambda\subseteq L\subseteq\Lambda^\#$;
--   2. $AL\subseteq L$ and $DL\subseteq L$, where $A=A_G$, $D=D_G$;
--   3. $L$ is integral: $\langle x,y\rangle\in\mathbb Z$ for all $x,y\in L$;
--   4. $L$ is unimodular: $L^\#=L$.
--
--   These are the lattices of Lemma S5.1 and Definition S5.3.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Lemma S5.1 and Definition S5.3, p.41 (PDF 42)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_IntADSat_Supplement_vecLattice
import Definitions.Def_IntADSat_Supplement_dualLattice

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat.Supplement

/-- `L` is an **`A, D`-stable integral unimodular overlattice** `Λ ⊆ L ⊆ Λ^#` of `Λ = Λ_G`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma S5.1 and Definition S5.3, p.41 (PDF 42)): `Λ ⊆ L ⊆ Λ^#`, `AL ⊆ L`, `DL ⊆ L`, `⟨L, L⟩ ⊆ ℤ`
(integral) and `L^# = L` (unimodular).

**Formalization Note** Lattices are `ℤ`-submodules of `V = ℚⁿ` with the standard dot product; `A = A_G`,
`D = D_G` are cast to `ℚ` and act by `mulVec`. -/
def IsADUnimodularOverlattice {n : ℕ} (G : SimpleGraph (Fin n)) (L : Submodule ℤ (Fin n → ℚ)) :
    Prop :=
  vecLattice G ≤ L ∧ L ≤ dualLattice (vecLattice G) ∧
    (∀ x ∈ L, ((adjacency G).map (Int.cast : ℤ → ℚ)).mulVec x ∈ L) ∧
    (∀ x ∈ L, ((degreeMatrix G).map (Int.cast : ℤ → ℚ)).mulVec x ∈ L) ∧
    (∀ x ∈ L, ∀ y ∈ L, ∃ z : ℤ, x ⬝ᵥ y = z) ∧ dualLattice L = L

end IntADSat.Supplement


