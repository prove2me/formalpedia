-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
-- name    : OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:20:17.471328+00:00
-- url     : https://prove2.me/theorems/7a2f6afa-359f-45fb-acd6-d3bb6279d2be
-- title:
--   Block subgroups of permutation groups and boundedness of reciprocal degree sums of symmetric groups
-- statement:
--   Let $X$ be a set, let $\mathrm{Sym}(X)$ be its group of permutations, and for $M\subseteq X$ let the block subgroup
--
--   $$
--   H_M=\{\,g\in\mathrm{Sym}(X)\ :\ g(x)=x\ \text{for all } x\notin M\,\}
--   $$
--
--   be the group of permutations supported in $M$. Write $S_n=\mathrm{Sym}(\{0,1,\dots,n-1\})$.
--
--   1. **Block subgroup and permutations of the block.** Extending a permutation of $M$ by the identity outside $M$ gives a group isomorphism $\mathrm{Sym}(M)\to H_M$.
--   2. **Block subgroup and a standard symmetric group.** If $X$ is finite, composing with an enumeration of $M$ gives a group isomorphism $H_M\cong S_{|M|}$.
--   3. **Bounded reciprocal degree sums.** For $n\ge 1$ and real $u$, let $Z_n(u)=\sum_{c\in\operatorname{Irr}(S_n)}d_c^{-u}$, where $\operatorname{Irr}(S_n)$ is the set of isotypic components of the regular representation of $S_n$ (one for each irreducible representation up to equivalence) and $d_c$ is the dimension of the corresponding irreducible representation. The proposition in question asserts that for every real $u>0$ the set $\{Z_n(u):n\ge 1\}$ is bounded above, i.e.
--
--   $$
--   \forall\,u>0\quad\exists\,C\in\mathbb{R}\quad\forall\,n\ge 1:\qquad \sum_{c\in\operatorname{Irr}(S_n)}d_c^{-u}\le C .
--   $$
--
--   Item 3 is a definition of a proposition, not a claim that it holds. Block subgroups are the subgroups appearing in coset-cap hypotheses for functions on $\mathrm{Sym}(X)$, and items 1 and 2 let their degree sums be computed in standard symmetric groups. The proposition of item 3 is exactly what makes the constant $C(u)=\sup_{n\ge 1}Z_n(u)$ a finite number.
--
--   **Formalization Note** $H_M$ is `blockSubgroup M` from the base definitions; item 1 is `permBlockEquiv M`, built from `Equiv.Perm.subtypeEquivSubtypePerm`, and item 2 is `blockSubgroupSnEquiv M` (for a finite type with decidable equality), which uses the non-canonical enumeration `Fintype.equivFin`. Item 3 is the proposition `SymmetricReciprocalDegreeBoundedStatement`, stated with `BddAbove` and `symmetricInverseDegreeSum n u`, where $d_c^{-u}$ is a real power of a positive integer. Boundedness matters because Mathlib's supremum of a set of reals that is not bounded above is $0$ by convention.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/SymmetricTransfer.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/SymmetricTransfer.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
noncomputable section

def permBlockEquiv {X : Type*} (M : Set X) : Equiv.Perm M ≃* blockSubgroup M where
  toEquiv := Equiv.Perm.subtypeEquivSubtypePerm (fun x => x ∈ M)
  map_mul' f g := by
    apply Subtype.ext
    exact Equiv.Perm.ofSubtype.map_mul f g

def blockSubgroupSnEquiv {X : Type*} [Fintype X] [DecidableEq X] (M : Set X) :
    blockSubgroup M ≃* Equiv.Perm (Fin (Fintype.card M)) :=
  (permBlockEquiv M).symm.trans (Fintype.equivFin M).permCongrHom

def SymmetricReciprocalDegreeBoundedStatement : Prop :=
  ∀ u : ℝ, 0 < u →
    BddAbove {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = symmetricInverseDegreeSum n u}

end
end PartialPermutation

end

end OAI


