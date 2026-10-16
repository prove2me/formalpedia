-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
-- name    : OAI_RepresentationTheory_PartialPermutation_Restriction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:11:40.637317+00:00
-- url     : https://prove2.me/theorems/e932b9fd-87db-4f0a-8f90-51b4b17fa1c6
-- title:
--   Restriction of a group-algebra module to a subgroup
-- statement:
--   Let $G$ be a group, $M$ a module over the complex group algebra $\mathbb{C}[G]$, and $H\le G$ a subgroup with inclusion $\iota\colon H\to G$. The inclusion induces the algebra homomorphism $\iota_*\colon\mathbb{C}[H]\to\mathbb{C}[G]$, $\sum_h a_h\,h\mapsto\sum_h a_h\,\iota(h)$ (finitely supported sums). The restricted module structure on $M$ is the pull-back of the $\mathbb{C}[G]$-action along $\iota_*$:
--
--   $$
--   \Big(\sum_{h\in H}a_h\,h\Big)\cdot_H m=\Big(\sum_{h\in H}a_h\,\iota(h)\Big)\cdot m\qquad(m\in M).
--   $$
--
--   This is the group-algebra form of restricting a representation of $G$ to the subgroup $H$. It allows the module-theoretic notions (simple submodules, isotypic components) to be applied to $M$ with respect to a subgroup, for example to compare the isotypic decomposition of a $G$-module with its decomposition under subgroups such as block subgroups of a permutation group.
--
--   **Formalization Note** The structure is `restrictGroupModule H`, defined by `Module.compHom` along `MonoidAlgebra.mapDomainAlgHom` applied to `H.subtype`. It is a definition marked `instance_reducible` rather than a global instance, so that it can be installed locally without competing with other module structures on $M$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Restriction.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Restriction.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation

section GroupRestriction
variable {G M : Type*} [Group G] [AddCommGroup M] [Module ℂ[G] M]

@[instance_reducible] noncomputable def restrictGroupModule (H : Subgroup G) : Module ℂ[H] M :=
  Module.compHom M (MonoidAlgebra.mapDomainAlgHom ℂ ℂ H.subtype).toRingHom

end GroupRestriction
end PartialPermutation

end

end OAI


