-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagramCounts
-- name    : OAI_RepresentationTheory_PartialPermutation_DiagramCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:43:33.815982+00:00
-- url     : https://prove2.me/theorems/6aaba30b-4c08-42d0-bb5a-8c8c218a19a7
-- title:
--   Young diagrams with $n$ cells, the partition count $p(n)$, and coding by row and column lengths
-- statement:
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ (row $i$, column $j$, both indexed from $0$) closed downwards for the componentwise order; $|\mu|$ is its number of cells, $r_i(\mu)$ the length of row $i$ and $c_j(\mu)$ the length of column $j$.
--
--   1. **Rectangle bound.** If $(i,j)\in\mu$, then $\mu$ contains the rectangle $\{0,\dots,i\}\times\{0,\dots,j\}$, so
--   $$
--   (i+1)(j+1)\le|\mu|.
--   $$
--   Consequently every cell $(i,j)$ of $\mu$ satisfies $i<|\mu|$ and $j<|\mu|$, and $r_i(\mu)\le|\mu|$ and $c_j(\mu)\le|\mu|$ for all $i,j\in\mathbb{N}$.
--   2. **Shapes of size $n$.** $\mathrm{Shape}(n)$ is the set of Young diagrams with exactly $n$ cells, i.e. the partitions of $n$ drawn as diagrams.
--   3. **Box code.** By item 1 the cell set of $\mu\in\mathrm{Shape}(n)$ is a subset of the box $\{0,\dots,n-1\}^2$. The map sending $\mu$ to its cell set, from $\mathrm{Shape}(n)$ to the subsets of this box, is injective; this makes $\mathrm{Shape}(n)$ a finite set.
--   4. **Partition count.** $p(n)=|\mathrm{Shape}(n)|$, the number of Young diagrams with $n$ cells, that is, the number of partitions of $n$.
--   5. **Short code.** For $n,m\in\mathbb{N}$, the short code of $\mu\in\mathrm{Shape}(n)$ records its first $m$ row lengths and its first $m$ column lengths:
--   $$
--   \mu\longmapsto\bigl((r_0(\mu),\dots,r_{m-1}(\mu)),\,(c_0(\mu),\dots,c_{m-1}(\mu))\bigr)\in\{0,\dots,n\}^m\times\{0,\dots,n\}^m.
--   $$
--
--   When $n<(m+1)^2$, a diagram with $n$ cells has no cell $(i,j)$ with $i\ge m$ and $j\ge m$, so it lies in the union of its first $m$ rows and first $m$ columns and the short code is injective. With $m=\lfloor\sqrt n\rfloor$ this gives the crude subexponential bound $p(n)\le(n+1)^{2\lfloor\sqrt n\rfloor}$, used to control sums over all shapes of a given size.
--
--   **Formalization Note** `Shape n` is the subtype of `YoungDiagram` with `μ.cells.card = n`, made a `Fintype` through the injectivity of `boxCode`; `partitionCount n` is `Fintype.card (Shape n)`; `shortCode n m` takes values in pairs of functions `Fin m → Fin (n+1)`. The bounds of item 1 are `rectangle_card_le`, `cell_bounded`, `rowLen_le_card` and `colLen_le_card`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/DiagramCounts.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/DiagramCounts.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace DiagramCounting
noncomputable section
open Finset

lemma rectangle_card_le (μ : YoungDiagram) (i j : ℕ) (h : (i,j) ∈ μ) :
    (i+1)*(j+1) ≤ μ.cells.card := by
  have hs : (Finset.range (i+1)) ×ˢ (Finset.range (j+1)) ⊆ μ.cells := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hx,hy⟩
    exact μ.isLowerSet ⟨by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hx,
      by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hy⟩ h
  simpa only [Finset.card_product, Finset.card_range] using Finset.card_le_card hs

lemma cell_bounded (μ : YoungDiagram) (x : μ.cells) :
    x.1.1 < μ.cells.card ∧ x.1.2 < μ.cells.card := by
  have h := rectangle_card_le μ x.1.1 x.1.2 x.2
  constructor <;> nlinarith

lemma rowLen_le_card (μ : YoungDiagram) (i : ℕ) : μ.rowLen i ≤ μ.cells.card := by
  by_contra h
  have hx := (μ.mem_iff_lt_rowLen.mpr (show μ.cells.card < μ.rowLen i by omega))
  have hh := cell_bounded μ ⟨(i,μ.cells.card),hx⟩
  exact (lt_irrefl _) hh.2

lemma colLen_le_card (μ : YoungDiagram) (j : ℕ) : μ.colLen j ≤ μ.cells.card := by
  by_contra h
  have hx := (μ.mem_iff_lt_colLen.mpr (show μ.cells.card < μ.colLen j by omega))
  have hh := cell_bounded μ ⟨(μ.cells.card,j),hx⟩
  exact (lt_irrefl _) hh.1

def Shape (n : ℕ) := {μ : YoungDiagram // μ.cells.card=n}

def boxCode (n : ℕ) (μ : Shape n) :
    ((Finset.range n) ×ˢ (Finset.range n)).powerset := by
  refine ⟨μ.1.cells,Finset.mem_powerset.mpr ?_⟩
  intro x hx
  have hh := cell_bounded μ.1 ⟨x,hx⟩
  rw [μ.2] at hh
  simpa only [Finset.mem_product, Finset.mem_range] using hh

lemma boxCode_injective (n : ℕ) : Function.Injective (boxCode n) := by
  intro μ ν h
  apply Subtype.ext
  apply YoungDiagram.ext
  exact congrArg Subtype.val h

instance (n : ℕ) : Fintype (Shape n) := Fintype.ofInjective (boxCode n) (boxCode_injective n)

def partitionCount (n : ℕ) := Fintype.card (Shape n)

def shortCode (n m : ℕ) (μ : Shape n) :
    (Fin m → Fin (n+1)) × (Fin m → Fin (n+1)) :=
  (fun i => ⟨μ.1.rowLen i, by have h:=rowLen_le_card μ.1 i; rw [μ.2] at h; omega⟩,
   fun j => ⟨μ.1.colLen j, by have h:=colLen_le_card μ.1 j; rw [μ.2] at h; omega⟩)

end
end DiagramCounting
end PartialPermutation
end

end OAI


