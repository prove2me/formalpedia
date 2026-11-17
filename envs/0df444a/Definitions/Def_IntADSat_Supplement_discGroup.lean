-- Prove2me | Definitions.Def_IntADSat_Supplement_discGroup
-- name    : IntADSat_Supplement_discGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:49:36.109203+00:00
-- url     : https://prove2.me/theorems/a58d8924-6a32-4a7c-8e71-cd50d657e377
-- title:
--   Discriminant group $D_\Lambda=\Lambda^\#/\Lambda$
-- statement:
--   The **discriminant group** of $\Lambda=\Lambda_G$ is the abelian group
--   $$D_\Lambda=\Lambda^\#/\Lambda,\qquad \beta(x+\Lambda,y+\Lambda)=\langle x,y\rangle+\mathbb Z\in\mathbb Q/\mathbb Z .$$
--   For an AD-full graph it is finite, of order $I_G^2$, and $\beta$ is a nondegenerate symmetric bilinear pairing.
--
--   **Formalization Note** The quotient of the $\mathbb Z$-module $\Lambda^\#$ by $\Lambda$; the pairing is used through representatives.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), §S5, p.40 (PDF 41)

import Mathlib
import Definitions.Def_IntADSat_Supplement_vecLattice
import Definitions.Def_IntADSat_Supplement_dualLattice

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The **discriminant group** `D_Λ = Λ^#/Λ` of `Λ = Λ_G` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §S5, p.40 (PDF 41)).

**Formalization Note** The quotient of the `ℤ`-module `Λ^#` by `Λ` (pulled back to `Λ^#`); an `abbrev`, so
its additive group structure is the quotient one. The pairing `β(x + Λ, y + Λ) = ⟨x, y⟩ + ℤ` is used through
representatives in the statements. -/
abbrev discGroup {n : ℕ} (G : SimpleGraph (Fin n)) : Type :=
  ↥(dualLattice (vecLattice G)) ⧸ (vecLattice G).comap (dualLattice (vecLattice G)).subtype

end IntADSat.Supplement


