-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
-- name    : OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:01:48.83487+00:00
-- url     : https://prove2.me/theorems/1dd34301-6cd3-4a6d-bd09-4b151e603bb4
-- title:
--   The trivial representation as the irreducible type of degree one
-- statement:
--   Let $G$ be a group and let $\mathbf{1}_G$ be the trivial representation of $G$ on $\mathbb{C}$, in which every $g\in G$ acts as the identity.
--
--   1. **Subrepresentations.** Every complex subspace of $\mathbb{C}$ is invariant, which gives an order isomorphism between the lattice of subrepresentations of $\mathbf{1}_G$ and the lattice of complex subspaces of $\mathbb{C}$.
--   2. **Irreducibility.** $\mathbf{1}_G$ is irreducible.
--   3. **Character.** $\chi_{\mathbf{1}_G}(g)=1$ for every $g\in G$.
--
--   Now let $G$ be finite. Let $\operatorname{Irr}(G)$ be the set of isotypic components of the left regular representation $\lambda$ of $G$ on $\ell^2(G)$ (complex functions on $G$, with $(\lambda(g)f)(h)=f(g^{-1}h)$), regarded as a module over the group algebra $\mathbb{C}[G]$. For $c\in\operatorname{Irr}(G)$ let $S_c\subseteq\ell^2(G)$ be the simple submodule chosen to represent the type of $c$, let $\pi_c$ be the restriction of $\lambda$ to $S_c$, and write $d_c=\dim_{\mathbb{C}}S_c$ for its degree and $\chi_c(g)=\operatorname{tr}\pi_c(g)$ for its character.
--
--   4. **Trivial index.** $c_0\in\operatorname{Irr}(G)$ is the index with $\pi_{c_0}\cong\mathbf{1}_G$; it exists and is unique because every irreducible representation is equivalent to exactly one $\pi_c$, and the equivalence $\pi_{c_0}\cong\mathbf{1}_G$ is recorded.
--   5. **Degree and action.** The trivial type has degree one and acts trivially:
--
--   $$
--   d_{c_0}=1,\qquad \pi_{c_0}(g)=\mathrm{id}_{S_{c_0}}\quad\text{for all } g\in G.
--   $$
--
--   The trivial type is the distinguished index in sums over irreducible representations; for instance, in $\sum_{c}d_c^{-u}$ it contributes exactly $1$.
--
--   **Formalization Note** Items 1 to 5 are `trivialSubmoduleEquiv`, the instance `trivial_rep_irreducible`, `trivial_character`, `trivialIndex G` (chosen from the unique-existence statement `irreducibleRep_complete`) with `trivialIndex_equiv`, and the simp lemmas `irreducibleDegree_trivial` and `irreducibleRep_trivial_apply`. Items 1 to 3 hold for an arbitrary group; $\operatorname{Irr}(G)$ is `IrreducibleIndex G`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/TrivialRepresentation.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/TrivialRepresentation.lean by skeleton subtraction
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

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
open scoped BigOperators MonoidAlgebra Classical

variable {G : Type*} [Group G] [Fintype G]
def trivialSubmoduleEquiv (G : Type*) [Group G] : Subrepresentation (Representation.trivial ℂ G ℂ) ≃o Submodule ℂ ℂ where
  toFun := Subrepresentation.toSubmodule
  invFun S := ⟨S, fun g x hx => by simpa only [Representation.trivial_apply] using hx⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

instance trivial_rep_irreducible (G : Type*) [Group G] : Representation.IsIrreducible (Representation.trivial ℂ G ℂ) :=
  (OrderIso.isSimpleOrder_iff (trivialSubmoduleEquiv G)).mpr inferInstance

omit [Fintype G] in
@[simp] lemma trivial_character (g : G) : (Representation.trivial ℂ G ℂ).character g = 1 := by
  simp [Representation.character, Representation.trivial]

def trivialIndex (G : Type*) [Group G] [Fintype G] : IrreducibleIndex G :=
  (irreducibleRep_complete (Representation.trivial ℂ G ℂ)).choose

lemma trivialIndex_equiv :
    Nonempty (Representation.Equiv (irreducibleRep (trivialIndex G))
      (Representation.trivial ℂ G ℂ)) :=
  (irreducibleRep_complete (Representation.trivial ℂ G ℂ)).choose_spec.1

@[simp] lemma irreducibleDegree_trivial : irreducibleDegree (trivialIndex G) = 1 := by
  obtain ⟨e⟩ := trivialIndex_equiv (G := G)
  simpa [irreducibleDegree] using e.toLinearEquiv.finrank_eq

@[simp] lemma irreducibleRep_trivial_apply (g : G) :
    irreducibleRep (trivialIndex G) g = 1 := by
  obtain ⟨e⟩ := trivialIndex_equiv (G := G)
  apply LinearMap.ext
  intro x
  apply e.toLinearEquiv.injective
  simpa using LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x

end
end PartialPermutation
end

end OAI


