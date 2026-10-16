-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CrossTableaux
-- name    : OAI_RepresentationTheory_PartialPermutation_CrossTableaux
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:07:48.528088+00:00
-- url     : https://prove2.me/theorems/06f621c6-7cac-4a4f-9285-9b4ec04f0070
-- title:
--   Column-transversal tabloids and the row-moment comparison of Young diagrams
-- statement:
--   This file compares two Young diagrams $\mu$ and $\nu$ through tabloids: if the letters of $\mu$ can be placed in a tabloid of shape $\nu$ so that no row receives two letters from the same column of $\mu$, then the row moment of $\mu$ is at most that of $\nu$, with equality only when $\mu=\nu$.
--
--   **Setting.** A Young diagram $\mu$ is regarded as a finite set $[\mu]\subset\mathbb{N}\times\mathbb{N}$ of cells $(i,j)$ (row $i$, column $j$, both counted from $0$) closed under decreasing either coordinate. Write $\operatorname{row}(i,j)=i$, $\operatorname{col}(i,j)=j$, $\mu_i$ for the length of row $i$ and $\mathrm{Col}_j$ for the set of cells of column $j$. Two Young diagrams are equal when their cell sets are equal. A tabloid of shape $\nu$ is a map $r:[\nu]\to\mathbb{N}$ of the form $r=\operatorname{row}\circ q$ for a permutation $q$ of $[\nu]$; it places each letter $y\in[\nu]$ in row $r(y)$.
--
--   1. **Row moment.** $n(\mu)=\sum_{x\in[\mu]}\operatorname{row}(x)=\sum_{i\ge0}i\,\mu_i$.
--
--   2. **Column-transversal maps.** A map $s:[\mu]\to\mathbb{N}$ is column-transversal for $\mu$ if it is injective on each column: $\operatorname{col}(x)=\operatorname{col}(y)$ and $s(x)=s(y)$ imply $x=y$.
--
--   3. **Column sorting.** For such $s$ there is a column-preserving permutation $p_s$ of $[\mu]$ that sorts every column by the values of $s$: if $x$ has the $k$-th smallest value of $s$ within its column (counting from $k=0$), then $p_s(x)=(k,\operatorname{col}(x))$. It satisfies $\operatorname{row}(p_s(x))\le s(x)$ for every cell $x$.
--
--   4. **Comparison.** Let $\nu$ be a Young diagram, $e:[\mu]\to[\nu]$ a bijection and $r$ a tabloid of shape $\nu$ such that $r\circ e$ is column-transversal for $\mu$. Then $n(\mu)\le n(\nu)$.
--
--   5. **Shapes from rows.** Row $i$ of $\mu$ is in bijection with $\{0,\dots,\mu_i-1\}$ via the column index, and if a bijection $e:[\mu]\to[\nu]$ preserves the row index, $\operatorname{row}(e(x))=\operatorname{row}(x)$ for all $x$, then $\mu=\nu$.
--
--   6. **Equality case.** In the situation of item 4,
--   $$
--   n(\mu)=n(\nu)\ \Longrightarrow\ \mu=\nu .
--   $$
--
--   These facts are what the classification step uses: comparing the single numerical statistic $n(\cdot)$ shows that an isomorphism between Specht modules forces their shapes to coincide.
--
--   **Formalization Note** $n(\mu)$ is `rowMoment μ`, column-transversality is `CrossTransversal`, and $p_s$ is `crossSorting`, assembled from the sorted enumerations `crossSortedColumn` of the columns. Items 4 to 6 are `cross_rowMoment_le`, `rowFiberEquiv` with `shape_eq_of_row_equiv`, and `cross_equal_moment_shape_eq`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/CrossTableaux.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/CrossTableaux.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

def rowMoment (μ : YoungDiagram) : ℕ := ∑ x, row μ x

def CrossTransversal (μ : YoungDiagram) (r : μ.cells → ℕ) : Prop :=
  ∀ x y, col μ x=col μ y → r x=r y → x=y

def crossSortedColumn (μ : YoungDiagram) (r : μ.cells → ℕ)
    (hr : CrossTransversal μ r) (j : ℕ) : Col μ j ≃ Fin (μ.colLen j) :=
  (exists_sortingEquiv (Col μ j) (fun x => r x.1)
    (fun x y h => Subtype.ext (hr x.1 y.1 (x.2.trans y.2.symm) h))
    _ (col_card μ j)).choose

lemma crossSortedColumn_mono (μ : YoungDiagram) (r : μ.cells → ℕ)
    (hr : CrossTransversal μ r) (j : ℕ) :
    StrictMono (fun i => r ((crossSortedColumn μ r hr j).symm i).1) :=
  (exists_sortingEquiv (Col μ j) (fun x => r x.1)
    (fun x y h => Subtype.ext (hr x.1 y.1 (x.2.trans y.2.symm) h))
    _ (col_card μ j)).choose_spec

def crossSorting (μ : YoungDiagram) (r : μ.cells → ℕ) (hr : CrossTransversal μ r) :
    Equiv.Perm μ.cells := fiberPermutation (col μ)
      (fun j => (crossSortedColumn μ r hr j).trans (columnEquiv μ j).symm)

lemma crossSorting_row (μ : YoungDiagram) (r : μ.cells → ℕ)
    (hr : CrossTransversal μ r) (x : μ.cells) : row μ (crossSorting μ r hr x) ≤ r x := by
  let e := crossSortedColumn μ r hr (col μ x)
  have h := strictMono_fin_nat_le _ (crossSortedColumn_mono μ r hr (col μ x)) (e ⟨x,rfl⟩)
  change (e ⟨x,rfl⟩).val ≤ r (e.symm (e ⟨x,rfl⟩)).val at h
  erw [Equiv.symm_apply_apply] at h
  exact h

lemma cross_rowMoment_le (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells) (r : Tabloid ν)
    (hr : CrossTransversal μ (fun x => r.1 (e x))) : rowMoment μ ≤ rowMoment ν := by
  calc
    rowMoment μ = ∑ x, row μ (crossSorting μ _ hr x) :=
      (Equiv.sum_comp (crossSorting μ _ hr) (row μ)).symm
    _ ≤ ∑ x, r.1 (e x) := Finset.sum_le_sum (fun x _ => crossSorting_row μ _ hr x)
    _ = ∑ x, r.1 x := Equiv.sum_comp e r.1
    _ = rowMoment ν := rowSum ν r

def rowFiberEquiv (μ : YoungDiagram) (i : ℕ) : {x : μ.cells // row μ x=i} ≃ Fin (μ.rowLen i) where
  toFun x := ⟨col μ x.1,by
    have h := μ.mem_iff_lt_rowLen.mp x.1.2
    have hi : x.1.1.1=i := x.2
    simpa only [col,hi] using h⟩
  invFun j := ⟨rowCell μ i j,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.2.symm rfl
  right_inv _ := rfl

lemma shape_eq_of_row_equiv (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells)
    (h : ∀ x, row ν (e x)=row μ x) : μ=ν := by
  have hr (i : ℕ) : μ.rowLen i=ν.rowLen i := by
    let er : {x : μ.cells // row μ x=i} ≃ {x : ν.cells // row ν x=i} :=
      e.subtypeEquiv (fun x => by rw [h])
    simpa only [Fintype.card_fin] using (Fintype.card_congr (rowFiberEquiv μ i)).symm.trans
      ((Fintype.card_congr er).trans (Fintype.card_congr (rowFiberEquiv ν i)))
  apply YoungDiagram.ext
  ext x
  exact (μ.mem_iff_lt_rowLen).trans ((hr x.1) ▸ ν.mem_iff_lt_rowLen.symm)

lemma cross_equal_moment_shape_eq (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells)
    (r : Tabloid ν) (hr : CrossTransversal μ (fun x => r.1 (e x)))
    (hm : rowMoment μ=rowMoment ν) : μ=ν := by
  let p := crossSorting μ _ hr
  have hs : (∑ x, row μ (p x))=∑ x, r.1 (e x) := by
    rw [Equiv.sum_comp p,Equiv.sum_comp e,rowSum]
    exact hm
  have he : ∀ x, row μ (p x)=r.1 (e x) :=
    fun x => (Finset.sum_eq_sum_iff_of_le (fun x _ => crossSorting_row μ _ hr x)).mp hs x (mem_univ x)
  obtain ⟨q,hq⟩ := r.2
  apply shape_eq_of_row_equiv μ ν ((p.symm.trans e).trans q)
  intro x
  simpa [hq] using (he (p.symm x)).symm

end
end PartialPermutation.YoungTabloid
end

end OAI


