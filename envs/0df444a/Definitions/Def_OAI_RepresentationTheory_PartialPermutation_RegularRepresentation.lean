-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
-- name    : OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:58:12.73896+00:00
-- url     : https://prove2.me/theorems/2bd6b6ee-8caf-45e8-a305-f86aa5ac9cf1
-- title:
--   Action formula for the left regular representation and the point mass at the identity
-- statement:
--   Let $G$ be a finite group and let $\ell^2(G)$ be the space of complex-valued functions on $G$ with its standard Euclidean inner product. The left regular representation $\lambda$ of $G$ on $\ell^2(G)$ acts by left translation.
--
--   1. **Action formula.** For all $g,h\in G$ and $f\in\ell^2(G)$,
--
--   $$
--   (\lambda(g)f)(h)=f(g^{-1}h).
--   $$
--
--   2. **Point mass at the identity.** $\delta_1\in\ell^2(G)$ is the function with $\delta_1(1)=1$ and $\delta_1(g)=0$ for $g\neq 1$.
--
--   The vector $\delta_1$ is cyclic for $\lambda$: $\lambda(g)\delta_1$ is the point mass at $g$, so for every $a\colon G\to\mathbb{C}$ one has $\sum_{g}a(g)\lambda(g)\delta_1=a$. This is how a function on $G$ is read off from its Fourier transform at the regular representation, which turns operator identities into character identities.
--
--   **Formalization Note** $\ell^2(G)$ is `EuclideanSpace` over $\mathbb{C}$ indexed by $G$, and $\lambda$ is `regularRep G` from the base definitions; item 1 is the simp lemma `regularRep_apply` (true by definition, and stated without the finiteness assumption), and $\delta_1$ is `deltaOne G`, built with `WithLp.toLp 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/RegularRepresentation.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/RegularRepresentation.lean by skeleton subtraction
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

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
variable (G : Type*) [Group G] [Fintype G]

omit [Fintype G] in
@[simp] lemma regularRep_apply (g h : G) (f : EuclideanSpace ℂ G) :
    regularRep G g f h = f (g⁻¹ * h) := rfl

def deltaOne : EuclideanSpace ℂ G := WithLp.toLp 2 (fun g => if g = 1 then 1 else 0)

end
end PartialPermutation

end

end OAI


