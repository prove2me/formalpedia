-- Prove2me | Definitions.Def_IntADSat_Supplement_IsGraphAdmissible
-- name    : IntADSat_Supplement_IsGraphAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:49:00.802203+00:00
-- url     : https://prove2.me/theorems/23b3c1dd-d6ab-4ad1-aa40-48083272267f
-- title:
--   Graph-admissible overlattice (Definition S5.3)
-- statement:
--   **Definition S5.3.** An $A,D$-stable integral unimodular overlattice $\Lambda\subseteq L\subseteq\Lambda^\#$ of $\Lambda=\Lambda_G$ is **graph-admissible** if its unit vectors span $V$, every unit vector $v\in L$ satisfies $|\langle\omega,v\rangle|=1$, and on the seed-oriented unit frame $V_\omega(L)$ every vector is an eigenvector of $D$, $\langle v,Av\rangle=0$ and $\langle u,Av\rangle\in\{0,1\}$ for $u\ne v$. The graph associated with $L$ has vertex set $V_\omega(L)$, with $u,v$ adjacent when $\langle u,Av\rangle=1$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Definition S5.3, p.41 (PDF 42)

import Mathlib
import Definitions.Def_IntADSat_Supplement_IsADUnimodularOverlattice
import Definitions.Def_IntADSat_Supplement_UnitFrameConditions

set_option autoImplicit false

namespace IntADSat.Supplement

/-- **Definition S5.3 (Graph-admissible overlattices)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.41 (PDF 42)): an `A, D`-stable integral
unimodular overlattice `Λ ⊆ L ⊆ Λ^#` of `Λ = Λ_G` satisfying conditions (1)–(3) on its unit vectors.

**Formalization Note** The conjunction of `IsADUnimodularOverlattice` and `UnitFrameConditions`. -/
def IsGraphAdmissible {n : ℕ} (G : SimpleGraph (Fin n)) (L : Submodule ℤ (Fin n → ℚ)) : Prop :=
  IsADUnimodularOverlattice G L ∧ UnitFrameConditions G L

end IntADSat.Supplement


