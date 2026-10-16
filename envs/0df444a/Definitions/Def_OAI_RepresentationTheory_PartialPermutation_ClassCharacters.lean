-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ClassCharacters
-- name    : OAI_RepresentationTheory_PartialPermutation_ClassCharacters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:15:20.195335+00:00
-- url     : https://prove2.me/theorems/7a29c22b-d73f-41a3-b3b2-8e6db80729f7
-- title:
--   Class characters and the bound on irreducible representations by conjugacy classes
-- statement:
--   This file turns characters into functions on conjugacy classes and shows that a finite group has at most as many pairwise non-isomorphic irreducible complex representations as conjugacy classes.
--
--   **Setting.** Let $G$ be a group, $V$ a finite-dimensional complex vector space and $\rho:G\to GL(V)$ a representation, with character $\chi_\rho(g)=\operatorname{tr}\rho(g)$. Write $\mathrm{Cl}(G)$ for the set of conjugacy classes of $G$ and $[g]$ for the class of $g$.
--
--   1. **Class invariance.** If $g$ and $h$ are conjugate in $G$, then $\chi_\rho(g)=\chi_\rho(h)$.
--
--   2. **Class character.** The class function $\tilde\chi_\rho:\mathrm{Cl}(G)\to\mathbb{C}$ defined by $\tilde\chi_\rho([g])=\chi_\rho(g)$.
--
--   3. **Linear independence.** Assume now that $G$ is finite. Let $(\rho_i)_{i\in I}$ be a family, indexed by a finite set $I$, of irreducible representations of $G$ on finite-dimensional complex vector spaces $V_i$, such that $\rho_i$ and $\rho_j$ are isomorphic if and only if $i=j$. Then the class characters $\tilde\chi_{\rho_i}$, $i\in I$, are linearly independent in the vector space of functions $\mathrm{Cl}(G)\to\mathbb{C}$.
--
--   4. **Counting bound.** For every such family,
--   $$
--   |I|\;\le\;|\mathrm{Cl}(G)| .
--   $$
--
--   This is the upper half of the classical count of irreducible representations by conjugacy classes. For the symmetric group it is combined with the injection of conjugacy classes into Young diagrams and with the non-isomorphism of Specht modules of different shapes, to conclude that the Specht modules exhaust the irreducible representations.
--
--   **Formalization Note** Items 1 and 2 (`character_eq_of_isConj`, `classCharacter`) hold for an arbitrary group. Items 3 and 4 (`independent_classCharacters`, `irreducible_family_card_le_conjClasses`) assume `[Fintype G]` and `Representation.IsIrreducible` for each member of the family, and express pairwise non-isomorphism as `Nonempty (Representation.Equiv (ρ i) (ρ j)) ↔ i = j`; the number of conjugacy classes is `Nat.card (ConjClasses G)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ClassCharacters.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ClassCharacters.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RankFillings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_FillingExtensions
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Interleavings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RowBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Truncation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TailBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagramCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DeficitCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauWeights
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Tabloids
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ColumnSorting
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_AlternatingTabloids
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Polytabloids
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtModules
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ColumnRearrangement
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauVectors
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CrossTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtShapes
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConjugacyCounts

namespace OAI

section
namespace PartialPermutation
noncomputable section
open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
lemma character_eq_of_isConj {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) {g h : G} (H : IsConj g h) :
    ρ.character g=ρ.character h := by
  obtain ⟨k,rfl⟩ := isConj_iff.mp H
  exact (ρ.char_conj _ _).symm

def classCharacter {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : ConjClasses G → ℂ :=
  Quotient.lift ρ.character (fun _ _ h => character_eq_of_isConj ρ h)

omit [Fintype G] in
lemma classCharacter_mk {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    classCharacter ρ (ConjClasses.mk g)=ρ.character g := rfl

lemma independent_classCharacters {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    [∀ i, Representation.IsIrreducible (ρ i)]
    (hd : ∀ i j, Nonempty (Representation.Equiv (ρ i) (ρ j)) ↔ i=j) :
    LinearIndependent ℂ (fun i => classCharacter (ρ i)) := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have he (g : G) : (∑ i, a i*(ρ i).character g)=0 := by
    have h := congrFun ha (ConjClasses.mk g)
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,classCharacter_mk,Pi.zero_apply] using h
  calc
    a j = ∑ i, a i * ((Nat.card G : ℂ)⁻¹ * ∑ g, (ρ i).character g * (ρ j).character g⁻¹) := by
      simp only [Representation.char_orthonormal,hd]
      simp
    _ = (Nat.card G : ℂ)⁻¹ * ∑ g, (∑ i, a i*(ρ i).character g) * (ρ j).character g⁻¹ := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by simp [he]

lemma irreducible_family_card_le_conjClasses {ι : Type*} [Fintype ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
    [∀ i, Representation.IsIrreducible (ρ i)]
    (hd : ∀ i j, Nonempty (Representation.Equiv (ρ i) (ρ j)) ↔ i=j) :
    Fintype.card ι ≤ Nat.card (ConjClasses G) := by
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  simpa using (independent_classCharacters V ρ hd).fintype_card_le_finrank

end
end PartialPermutation

end

end OAI


