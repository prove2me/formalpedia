-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConjugacyCounts
-- name    : OAI_RepresentationTheory_PartialPermutation_ConjugacyCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:13:18.576987+00:00
-- url     : https://prove2.me/theorems/53f91399-857a-472d-8409-c4a7c6ff6863
-- title:
--   Cycle types inject the conjugacy classes of $S_n$ into Young diagrams with $n$ cells
-- statement:
--   This file compares conjugacy classes of symmetric groups with Young diagrams: the cycle type gives an injection of conjugacy classes into partitions, and sorting the parts gives an injection of partitions into Young diagrams.
--
--   **Setting.** A partition of $n$ is a finite multiset of positive integers with sum $n$. A Young diagram is a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ (row $i$, column $j$) closed under decreasing either coordinate, and $\mathrm{Shape}(n)$ is the set of Young diagrams with exactly $n$ cells. For a finite list $w=(w_0,w_1,\dots,w_{k-1})$ of natural numbers, $D(w)=\{(i,j):i<k,\ j<w_i\}$ is the set of cells with row lengths $w$ (a Young diagram when $w$ is weakly decreasing). For a finite set $\alpha$, the cycle type of a permutation of $\alpha$ is the partition of $|\alpha|$ formed by its cycle lengths, fixed points counting as cycles of length $1$.
--
--   1. **Cell count.** For every list $w$, $|D(w)|=w_0+w_1+\cdots+w_{k-1}$.
--
--   2. **Young diagram of a partition.** For a partition $p$ of $n$, $Y(p)\in\mathrm{Shape}(n)$ is the Young diagram whose row lengths are the parts of $p$ listed in weakly decreasing order. The map $p\mapsto Y(p)$ is injective.
--
--   3. **Cycle type of a conjugacy class.** For a finite set $\alpha$, sending the conjugacy class of $g\in\mathrm{Sym}(\alpha)$ to the cycle type of $g$ is a well-defined injective map from the set of conjugacy classes of $\mathrm{Sym}(\alpha)$ to the set of partitions of $|\alpha|$.
--
--   4. **Counting.** For every $n\in\mathbb{N}$, with $S_n$ the symmetric group on $\{0,1,\dots,n-1\}$,
--   $$
--   \#\{\text{conjugacy classes of } S_n\}\;\le\;|\mathrm{Shape}(n)| .
--   $$
--
--   Combined with the fact that a finite group has at most as many pairwise non-isomorphic irreducible representations as conjugacy classes, this shows that $S_n$ has at most as many irreducible representations as there are Young diagrams with $n$ cells; since Specht modules of distinct shapes are non-isomorphic irreducible representations, Young diagrams with $n$ cells then index all irreducible representations of $S_n$.
--
--   **Formalization Note** $D(w)$ is Mathlib's `YoungDiagram.cellsOfRowLens`, $Y(p)$ is `partitionShape` (built with `YoungDiagram.ofRowLens`), and the cycle-type partition is Mathlib's `Equiv.Perm.partition`, lifted to conjugacy classes as `conjugacyPartition`. $\mathrm{Shape}(n)$ is the subtype `Shape n`, and item 4 (`symmetric_conjClasses_card_le`) compares `Nat.card (ConjClasses (Equiv.Perm (Fin n)))` with `Fintype.card (Shape n)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ConjugacyCounts.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ConjugacyCounts.lean by skeleton subtraction
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

namespace OAI

section

namespace PartialPermutation.DiagramCounting
noncomputable section
open Finset
open scoped Classical

lemma cellsOfRowLens_card (w : List ℕ) : (YoungDiagram.cellsOfRowLens w).card=w.sum := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a w ih =>
    have hd : Disjoint (({0} : Finset ℕ) ×ˢ range a)
        ((YoungDiagram.cellsOfRowLens w).map
          (Function.Embedding.prodMap ⟨Nat.succ,Nat.succ_injective⟩ (Function.Embedding.refl ℕ))) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨z,hz,he⟩ := mem_map.mp hy
      have hx0 : x.1=0 := by simpa using (mem_product.mp hx).1
      have hh := congrArg Prod.fst he
      change z.1+1=x.1 at hh
      omega
    simp only [YoungDiagram.cellsOfRowLens,card_union_of_disjoint hd,card_product,
      card_singleton,card_range,one_mul,card_map,ih,List.sum_cons]

def partitionShape {n : ℕ} (p : n.Partition) : Shape n :=
  ⟨YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·))
    (List.sortedGE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)),by
    rw [YoungDiagram.ofRowLens,cellsOfRowLens_card]
    have hs := congrArg Multiset.sum (Multiset.sort_eq p.parts (· ≥ ·))
    exact hs.trans p.parts_sum⟩

lemma partitionShape_injective {n : ℕ} : Function.Injective (@partitionShape n) := by
  intro p q h
  have hp : (partitionShape p).1.rowLens=p.parts.sort (· ≥ ·) :=
    YoungDiagram.rowLens_ofRowLens_eq_self (hw := List.sortedGE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)) (fun x hx => p.parts_pos ((Multiset.mem_sort _).mp hx))
  have hq : (partitionShape q).1.rowLens=q.parts.sort (· ≥ ·) :=
    YoungDiagram.rowLens_ofRowLens_eq_self (hw := List.sortedGE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)) (fun x hx => q.parts_pos ((Multiset.mem_sort _).mp hx))
  apply Nat.Partition.ext
  have he := congrArg (fun μ : Shape n => μ.1.rowLens) h
  rw [hp,hq] at he
  exact (Multiset.sort_eq p.parts (· ≥ ·)).symm.trans
    ((congrArg (fun l : List ℕ => (l : Multiset ℕ)) he).trans (Multiset.sort_eq q.parts (· ≥ ·)))

def conjugacyPartition {α : Type*} [Fintype α] [DecidableEq α] :
    ConjClasses (Equiv.Perm α) → (Fintype.card α).Partition :=
  Quotient.lift Equiv.Perm.partition (fun _ _ h => Equiv.Perm.partition_eq_of_isConj.mp h)

lemma conjugacyPartition_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (@conjugacyPartition α _ _) := by
  intro a b
  induction a using Quotient.inductionOn with | _ g =>
    induction b using Quotient.inductionOn with | _ h =>
      intro he
      exact Quotient.sound (Equiv.Perm.partition_eq_of_isConj.mpr he)

lemma symmetric_conjClasses_card_le (n : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Fin n))) ≤ Fintype.card (Shape n) := by
  let : Fintype (ConjClasses (Equiv.Perm (Fin n))) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective _
    (partitionShape_injective.comp (@conjugacyPartition_injective (Fin n) _ _))
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using h

end
end PartialPermutation.DiagramCounting

end

end OAI


