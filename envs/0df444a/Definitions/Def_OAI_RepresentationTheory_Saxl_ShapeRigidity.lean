-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
-- name    : OAI_RepresentationTheory_Saxl_ShapeRigidity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:14:12.884834+00:00
-- url     : https://prove2.me/theorems/8b45e6cd-b561-4399-af2a-34a1c087a0b2
-- title:
--   Row moment of a Young diagram and the column antisymmetrizer in any representation
-- statement:
--   Two auxiliary objects attached to Young diagrams and tableaux.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both indexed from $0$) closed under moving up or to the left; $|\mu|$ is its number of cells. A tableau of shape $\mu$ on the positions $[n]$ is a bijection $t:[n]\to\mu$; its column group $C_t\le\mathfrak S_n$ consists of the permutations $g$ such that $t(g(q))$ and $t(q)$ lie in the same column for every position $q$.
--
--   1. **Row moment.** For a Young diagram $\mu$,
--   $$
--   \operatorname{rm}(\mu)=\sum_{(i,j)\in\mu} i\ \in\mathbb{Z},
--   $$
--   the sum of the zero-based row indices of all cells; if row $i$ has length $\mu_i$, then $\operatorname{rm}(\mu)=\sum_i i\,\mu_i$.
--
--   2. **Column operator.** For a tableau $t$ of shape $\mu$ on $[n]$ and any representation $\rho$ of $\mathfrak S_n$ on a complex vector space $V$,
--   $$
--   \kappa_t^{\rho}=\sum_{g\in C_t}\operatorname{sgn}(g)\,\rho(g)\in\operatorname{End}_{\mathbb{C}}(V),
--   $$
--   the column antisymmetrizer of $t$ acting through $\rho$.
--
--   The row moment is a numerical shape statistic that helps tell Young diagrams apart in the proof that Specht modules of distinct shapes are not isomorphic. The column operator is the column antisymmetrizer of the group algebra acting in an arbitrary representation; every $\mathfrak S_n$-equivariant map $f$ satisfies $f\circ\kappa_t^{\rho}=\kappa_t^{\sigma}\circ f$, which lets the action on a Specht module be compared with the action on any representation it maps into.
--
--   **Formalization Note** `rowMoment μ` sums `(c.1 : ℤ)` over `μ.cells`, and `columnOperator t ρ` is `∑ g : columnGroup t, signC g • ρ g`, where `signC` is the sign character with values in $\mathbb{C}$ and the finite column group is made a `Fintype` via `Fintype.ofFinite`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/ShapeRigidity.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/ShapeRigidity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uV uW

namespace Saxl

/- Zero-based row-index statistic of a partition. -/
def rowMoment (μ : YoungDiagram) : ℤ := ∑ c ∈ μ.cells, (c.1 : ℤ)

/- The column operator on any genuine representation of the same group. -/
def columnOperator {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) : Module.End ℂ V := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t, signC (g : Equiv.Perm (Fin n)) • ρ g

/- Distinct genuine complex Specht shapes are inequivalent. -/
end Saxl

end

end OAI


