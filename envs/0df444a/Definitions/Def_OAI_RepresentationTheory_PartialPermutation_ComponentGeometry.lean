-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
-- name    : OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:05:08.869993+00:00
-- url     : https://prove2.me/theorems/5791a7a7-c99f-4bea-8762-cde24c25ba41
-- title:
--   Isotypic components of a representation viewed as complex subspaces
-- statement:
--   Let $G$ be a finite group, $V$ a finite-dimensional complex inner product space, and $\rho$ a representation of $G$ on $V$, so that $V$ is a module over the group algebra $\mathbb{C}[G]$ with $g$ acting as $\rho(g)$. For an isotypic component $c$ of this module (the sum of all simple $\mathbb{C}[G]$-submodules isomorphic to a fixed simple submodule $S_c$), the component space $V_c\subseteq V$ is $c$ regarded merely as a complex subspace of $V$, i.e. obtained by restricting scalars from $\mathbb{C}[G]$ to $\mathbb{C}$:
--
--   $$
--   V_c=\sum\big\{\,S\subseteq V\ :\ S\ \text{a simple }\mathbb{C}[G]\text{-submodule with } S\cong S_c\,\big\}\quad\text{(as a complex subspace of } V).
--   $$
--
--   Passing to complex subspaces makes the inner-product geometry of $V$ available for isotypic components: the spaces $V_c$ are $\rho$-invariant and together span $V$, and when $\rho$ is unitary they are mutually orthogonal, so that norms and traces on $V$ split along irreducible types via the orthogonal projections onto the $V_c$.
--
--   **Formalization Note** The component space is `componentSpace ρ c`, defined as `c.val.restrictScalars` to $\mathbb{C}$, where `c` ranges over Mathlib's `isotypicComponents` of the module `ρ.asModule`. The inner product on $V$ is part of the setting but is not used in the definition itself.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ComponentGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ComponentGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
section Geometry
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)

def componentSpace (c : isotypicComponents ℂ[G] ρ.asModule) : Submodule ℂ V :=
  c.val.restrictScalars ℂ

end Geometry
end
end PartialPermutation

end

end OAI


