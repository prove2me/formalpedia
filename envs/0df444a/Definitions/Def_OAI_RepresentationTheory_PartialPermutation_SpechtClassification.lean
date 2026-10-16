-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtClassification
-- name    : OAI_RepresentationTheory_PartialPermutation_SpechtClassification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:18:36.526126+00:00
-- url     : https://prove2.me/theorems/4831e735-8468-4b2c-9fd2-af10df4cf8ab
-- title:
--   Specht modules classify the irreducible representations of the symmetric group
-- statement:
--   Fix $n\in\mathbb{N}$, let $[n]=\{0,1,\dots,n-1\}$ and let $S_n$ be the group of all permutations of $[n]$. Write $\mathrm{Shape}(n)$ for the finite set of Young diagrams with exactly $n$ cells (equivalently, partitions of $n$). For a Young diagram $\mu$, let $\mathrm{Sym}(\mu)$ be the group of permutations of the set of cells of $\mu$.
--
--   Two objects from companion modules enter the construction.
--
--   - **Specht representation.** A tabloid of $\mu$ is a function on the cells of the form $x\mapsto\mathrm{row}(p(x))$ with $p\in\mathrm{Sym}(\mu)$. The group $\mathrm{Sym}(\mu)$ acts unitarily on the space $\ell^2(T_\mu)$ of complex functions on the set $T_\mu$ of tabloids by $(g\cdot f)(r)=f(r\circ g)$. With $C_\mu\le\mathrm{Sym}(\mu)$ the subgroup of permutations that keep every cell in its column and $r_0$ the tabloid $x\mapsto\mathrm{row}(x)$, the polytabloid is $e_\mu=\sum_{c\in C_\mu}\operatorname{sgn}(c)\,c\cdot\delta_{r_0}$, and the Specht module $S^\mu\subseteq\ell^2(T_\mu)$ is the linear span of the orbit $\{g\cdot e_\mu : g\in\mathrm{Sym}(\mu)\}$, with the restricted action.
--   - **Index set of irreducibles.** $\mathrm{Irr}(S_n)$ is the finite set of isotypic components $c$ of the left regular representation of $S_n$ on $\ell^2(S_n)$; each $c$ carries a chosen irreducible subrepresentation $\rho_c$, and every irreducible finite-dimensional complex representation of $S_n$ is equivalent to $\rho_c$ for exactly one $c$.
--
--   The module defines the following objects and facts, for $\mu,\nu\in\mathrm{Shape}(n)$.
--
--   1. **Labelling.** A fixed (non-canonical) bijection $\ell_\mu$ from the cells of $\mu$ onto $[n]$.
--   2. **Specht representation of $S_n$.** The representation $R_\mu$ of $S_n$ on $S^\mu$ given by $R_\mu(g)=S^\mu\bigl(\ell_\mu^{-1}\circ g\circ\ell_\mu\bigr)$; it is irreducible.
--   3. **Index of a shape.** The element $\iota_n(\mu)\in\mathrm{Irr}(S_n)$ with $\rho_{\iota_n(\mu)}\cong R_\mu$.
--   4. **Classification.** If $R_\mu\cong R_\nu$ then $\mu=\nu$, so $\iota_n$ is injective. Moreover $|\mathrm{Irr}(S_n)|\le|\mathrm{Shape}(n)|$, so $\iota_n$ is a bijection, packaged as the equivalence
--   $$
--   \iota_n\colon\ \mathrm{Shape}(n)\xrightarrow{\ \sim\ }\mathrm{Irr}(S_n),\qquad \rho_{\iota_n(\mu)}\cong R_\mu .
--   $$
--
--   This is the classical statement that the Specht modules form a complete list of pairwise inequivalent irreducible complex representations of $S_n$. Through $\iota_n$, a sum over the irreducible representations of $S_n$, such as an inverse-degree sum $\sum_{c}(\dim\rho_c)^{-u}$, becomes a sum over Young diagrams with $n$ cells, where combinatorial estimates on the dimensions of Specht modules can be applied.
--
--   **Formalization Note** `Shape n` is the subtype of `YoungDiagram` with `cells.card = n`. `labels μ` is `Fintype.equivFin` followed by `finCongr`, `rep μ` is `spechtRep μ.1` composed with `(labels μ).symm.permCongrHom`, and its irreducibility is an unnamed instance. `index μ` is extracted with `choose` from the existence-and-uniqueness statement `irreducibleRep_complete`; the cardinality inequality is `actual_irreducible_card_le`, and `indexEquiv n` is `Equiv.ofBijective index (index_bijective n)`. `IrreducibleIndex (Equiv.Perm (Fin n))` is the type of isotypic components of the regular module over the complex group algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/SpechtClassification.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/SpechtClassification.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ClassCharacters

namespace OAI

section
namespace PartialPermutation
namespace SpechtActual
noncomputable section
open YoungTabloid DiagramCounting
open scoped Classical

def labels {n : ℕ} (μ : Shape n) : μ.1.cells ≃ Fin n :=
  (Fintype.equivFin μ.1.cells).trans (finCongr (by simpa using μ.2))

def rep {n : ℕ} (μ : Shape n) :=
  (spechtRep μ.1).comp (labels μ).symm.permCongrHom.toMonoidHom

instance {n : ℕ} (μ : Shape n) : Representation.IsIrreducible (rep μ) := by
  unfold rep
  infer_instance

def index {n : ℕ} (μ : Shape n) : IrreducibleIndex (Equiv.Perm (Fin n)) :=
  (irreducibleRep_complete (rep μ)).choose

lemma index_spec {n : ℕ} (μ : Shape n) :
    Nonempty (Representation.Equiv (irreducibleRep (index μ)) (rep μ)) :=
  (irreducibleRep_complete (rep μ)).choose_spec.1

lemma rep_equiv_shape_eq {n : ℕ} (μ ν : Shape n)
    (E : Representation.Equiv (rep μ) (rep ν)) : μ=ν := by
  apply Subtype.ext
  let e : μ.1.cells ≃ ν.1.cells := (labels μ).trans (labels ν).symm
  apply specht_equiv_shape_eq μ.1 ν.1 e E.toLinearEquiv
  intro g x
  have hh := LinearMap.congr_fun (E.isIntertwining' ((labels μ).permCongrHom g)) x
  change E (spechtRep μ.1 ((labels μ).symm.permCongrHom ((labels μ).permCongrHom g)) x)=
    spechtRep ν.1 ((labels ν).symm.permCongrHom ((labels μ).permCongrHom g)) (E x) at hh
  have he : (labels μ).symm.permCongrHom ((labels μ).permCongrHom g)=g :=
    (labels μ).permCongrHom.symm_apply_apply g
  rw [he] at hh
  exact hh

lemma index_injective (n : ℕ) : Function.Injective (@index n) := by
  intro μ ν h
  obtain ⟨e⟩ := index_spec μ
  obtain ⟨f⟩ := index_spec ν
  apply rep_equiv_shape_eq μ ν
  exact e.symm.trans (h ▸ f)

lemma actual_irreducible_card_le (n : ℕ) :
    Fintype.card (IrreducibleIndex (Equiv.Perm (Fin n))) ≤ Fintype.card (Shape n) := by
  exact (irreducible_family_card_le_conjClasses (fun c => irreducibleSpace c)
    (fun c => irreducibleRep c) (componentRep_equiv_iff (regularRep (Equiv.Perm (Fin n))))).trans
    (symmetric_conjClasses_card_le n)

theorem index_bijective (n : ℕ) : Function.Bijective (@index n) := by
  have hc := actual_irreducible_card_le n
  have hi := index_injective n
  have he := le_antisymm hc (Fintype.card_le_of_injective _ hi)
  exact ⟨hi,(Fintype.bijective_iff_injective_and_card _).mpr ⟨hi,he.symm⟩ |>.surjective⟩

def indexEquiv (n : ℕ) : Shape n ≃ IrreducibleIndex (Equiv.Perm (Fin n)) :=
  Equiv.ofBijective index (index_bijective n)

end
end SpechtActual
end PartialPermutation

end

end OAI


