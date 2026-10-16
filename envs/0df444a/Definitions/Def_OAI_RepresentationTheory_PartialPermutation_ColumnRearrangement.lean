-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ColumnRearrangement
-- name    : OAI_RepresentationTheory_PartialPermutation_ColumnRearrangement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:02:57.357527+00:00
-- url     : https://prove2.me/theorems/b5c77d4f-bc37-46b0-a15d-a9c9872e8ba0
-- title:
--   Column restriction and column decomposition of a Young diagram
-- statement:
--   This file provides three pieces of bookkeeping for the columns of a Young diagram: restricting a column-preserving permutation to a single column, the column index of a cell as a bounded number, and the decomposition of the diagram into its columns.
--
--   **Setting.** Let $\mu$ be a Young diagram, regarded as a finite set $[\mu]\subset\mathbb{N}\times\mathbb{N}$ of cells $(i,j)$ (row $i$, column $j$, both counted from $0$) that is closed under decreasing either coordinate, and let $\mu_0$ be the length of row $0$, the longest row, which equals the number of nonempty columns. Write $\operatorname{col}(i,j)=j$, let $\mathrm{Col}_j=\{x\in[\mu]:\operatorname{col}(x)=j\}$ be the $j$-th column, and let $C_\mu$ be the column group, consisting of the permutations $c$ of $[\mu]$ with $\operatorname{col}(c(x))=\operatorname{col}(x)$ for all cells $x$.
--
--   1. **Restriction to a column.** For $c\in C_\mu$ and $j\in\mathbb{N}$, the restriction $c|_{\mathrm{Col}_j}$ is a permutation of $\mathrm{Col}_j$, with inverse $c^{-1}|_{\mathrm{Col}_j}$.
--
--   2. **Column index.** Every cell $x$ satisfies $\operatorname{col}(x)<\mu_0$, so its column index is an element of $\{0,1,\dots,\mu_0-1\}$.
--
--   3. **Column decomposition.** The map $x\mapsto(\operatorname{col}(x),x)$ is a bijection
--   $$
--   [\mu]\;\cong\;\bigsqcup_{j=0}^{\mu_0-1}\mathrm{Col}_j ,
--   $$
--   whose inverse forgets the column index.
--
--   These devices allow a sum over all cells to be rewritten as a double sum over columns and cells within a column, and a column-preserving permutation to be treated one column at a time. They serve the column-by-column rearrangement arguments used to compare tabloids of standard tableaux when proving that standard polytabloids are linearly independent.
--
--   **Formalization Note** The three objects are `columnRestrict`, `colIndex` (valued in `Fin (μ.rowLen 0)`) and `columnDecomp`, an equivalence between the cells and a sigma type over the column indices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ColumnRearrangement.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ColumnRearrangement.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

def columnRestrict (μ : YoungDiagram) (c : columnGroup μ) (j : ℕ) : Equiv.Perm (Col μ j) where
  toFun x := ⟨c.1 x.1,(c.2 x.1).trans x.2⟩
  invFun x := ⟨c.1⁻¹ x.1,((c⁻¹).2 x.1).trans x.2⟩
  left_inv x := by apply Subtype.ext; exact c.1.symm_apply_apply _
  right_inv x := by apply Subtype.ext; exact c.1.apply_symm_apply _

def colIndex (μ : YoungDiagram) (x : μ.cells) : Fin (μ.rowLen 0) :=
  ⟨col μ x,(μ.mem_iff_lt_rowLen.mp x.2).trans_le
    (μ.rowLen_anti 0 x.1.1 (Nat.zero_le _))⟩

def columnDecomp (μ : YoungDiagram) : μ.cells ≃ Σ j : Fin (μ.rowLen 0), Col μ j where
  toFun x := ⟨colIndex μ x,⟨x,rfl⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨j,x,hx⟩ := x
    have hj : colIndex μ x=j := Fin.ext hx
    cases hj
    rfl

end
end PartialPermutation.YoungTabloid
end

end OAI


