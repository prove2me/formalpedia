-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ColumnSorting
-- name    : OAI_RepresentationTheory_PartialPermutation_ColumnSorting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:53:38.819731+00:00
-- url     : https://prove2.me/theorems/0c162414-00a7-41ed-b695-264c304532b5
-- title:
--   Sorting columns: every column-transversal tabloid comes from a unique element of the column group
-- statement:
--   Let $\mu$ be a Young diagram, a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ closed downwards for the componentwise order, with $\mathrm{row}(i,j)=i$, $\mathrm{col}(i,j)=j$, columns $\mathrm{Col}_j=\{x\in\mu : \mathrm{col}(x)=j\}$ of sizes $c_j$, and column group $C_\mu=\{g\in\mathrm{Sym}(\mu) : \mathrm{col}\circ g=\mathrm{col}\}$. A tabloid is a function $t:\mu\to\mathbb{N}$ of the form $t=\mathrm{row}\circ p$ with $p\in\mathrm{Sym}(\mu)$ (the cells serve as letters and letter $x$ is placed in row $t(x)$).
--
--   1. **Sorting bijections.** If $\alpha$ is a finite set with $m$ elements and $h:\alpha\to\mathbb{N}$ is injective, there is a bijection $e:\alpha\to\{0,\dots,m-1\}$ such that $k\mapsto h(e^{-1}(k))$ is strictly increasing. Moreover every strictly increasing $g:\{0,\dots,m-1\}\to\mathbb{N}$ satisfies $k\le g(k)$ for all $k$.
--   2. **Transversal tabloids.** A tabloid $t$ is transversal if no two distinct letters of the same column lie in the same row:
--   $$
--   \mathrm{col}(x)=\mathrm{col}(y)\ \text{ and }\ t(x)=t(y)\ \Longrightarrow\ x=y\qquad(x,y\in\mu).
--   $$
--   Then $t$ is injective on each column $\mathrm{Col}_j$.
--   3. **Sorted columns.** For a transversal $t$ and $j\in\mathbb{N}$, $\mathrm{sort}_{t,j}:\mathrm{Col}_j\to\{0,\dots,c_j-1\}$ is the bijection of item 1 that ranks the letters of column $j$ by increasing value of $t$ (it is unique, since $t$ is injective on the column).
--   4. **Fibrewise permutations.** For a map $r:\alpha\to\iota$ and permutations $p_i$ of the fibres $r^{-1}(i)$, the permutation $\sigma_{r,p}(a)=p_{r(a)}(a)$ of $\alpha$ acts on each fibre by $p_i$ and satisfies $r\circ\sigma_{r,p}=r$.
--   5. **Column sorting.** For a transversal $t$, $\gamma_t\in\mathrm{Sym}(\mu)$ is the fibrewise permutation for $\mathrm{col}$ that sends the letter of column $j$ with the $k$-th smallest value of $t$ (counting from $k=0$) to the cell $(k,j)$. It belongs to $C_\mu$ and satisfies $\mathrm{row}(\gamma_t x)\le t(x)$ for all $x\in\mu$.
--   6. **Consequences.** Every transversal tabloid $t$ is of the form
--   $$
--   t=\mathrm{row}\circ c\qquad\text{for some }c\in C_\mu,
--   $$
--   and the map $C_\mu\to\{\text{tabloids}\}$, $c\mapsto\mathrm{row}\circ c$, is injective.
--
--   Thus every transversal tabloid arises from exactly one element of the column group; in terms of the relabelling action $(g\cdot t)(x)=t(g^{-1}x)$ and the canonical tabloid $t_0=\mathrm{row}$, it equals $c^{-1}\cdot t_0$. This is the combinatorial input for the uniqueness of column-alternating functions on tabloids: a function $F$ with $F(c\cdot t)=\mathrm{sgn}(c)F(t)$ for all $c\in C_\mu$ vanishes on non-transversal tabloids and is determined by its value at $t_0$.
--
--   **Formalization Note** Item 1 is `exists_sortingEquiv` and `strictMono_fin_nat_le`; item 2 is `Transversal` and `transversal_col_injective`; item 3 is `sortedColumn`, chosen with `Exists.choose`, and `sortedColumn_mono`; item 4 is `fiberPermutation` and `fiberPermutation_rank`; item 5 is `columnSorting`, `columnSorting_mem` and `columnSorting_row`; item 6 is `transversal_eq_column` and `column_row_injective`. The file uses classical decidability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ColumnSorting.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ColumnSorting.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace YoungTabloid
noncomputable section
open Finset
open scoped Classical

lemma exists_sortingEquiv (α : Type*) [Fintype α] (r : α → ℕ) (hr : Function.Injective r)
    (n : ℕ) (hn : Fintype.card α=n) :
    ∃ e : α ≃ Fin n, StrictMono (fun i => r (e.symm i)) := by
  let : LinearOrder α := LinearOrder.lift' r hr
  let e := Fintype.orderIsoFinOfCardEq α hn
  exact ⟨e.toEquiv.symm, e.strictMono⟩

lemma strictMono_fin_nat_le {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  obtain ⟨i,hi⟩ := i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hi' : i<n := by omega
    have h := hf (show (⟨i,hi'⟩:Fin n)<⟨i+1,hi⟩ by simp)
    have ih' := ih hi'
    change i ≤ f ⟨i,hi'⟩ at ih'
    change i+1 ≤ f ⟨i+1,hi⟩
    omega

def Transversal (μ : YoungDiagram) (r : Tabloid μ) : Prop :=
  ∀ x y : μ.cells, col μ x=col μ y → r.1 x=r.1 y → x=y

lemma transversal_col_injective (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r)
    (j : ℕ) : Function.Injective (fun x : Col μ j => r.1 x.1) := by
  intro x y h
  apply Subtype.ext
  exact hr x.1 y.1 (x.2.trans y.2.symm) h

def sortedColumn (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) (j : ℕ) :
    Col μ j ≃ Fin (μ.colLen j) :=
  (exists_sortingEquiv (Col μ j) (fun x => r.1 x.1)
    (transversal_col_injective μ r hr j) _ (col_card μ j)).choose

lemma sortedColumn_mono (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) (j : ℕ) :
    StrictMono (fun i => r.1 ((sortedColumn μ r hr j).symm i).1) :=
  (exists_sortingEquiv (Col μ j) (fun x => r.1 x.1)
    (transversal_col_injective μ r hr j) _ (col_card μ j)).choose_spec

def fiberPermutation {α ι : Type*} (r : α → ι)
    (p : ∀ i, Equiv.Perm {a // r a=i}) : Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv r).symm.trans
    ((Equiv.sigmaCongrRight p).trans (Equiv.sigmaFiberEquiv r))

lemma fiberPermutation_rank {α ι : Type*} (r : α → ι)
    (p : ∀ i, Equiv.Perm {a // r a=i}) (a : α) :
    r (fiberPermutation r p a)=r a := (p (r a) ⟨a,rfl⟩).2

def columnSorting (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) :
    Equiv.Perm μ.cells :=
  fiberPermutation (col μ) (fun j => (sortedColumn μ r hr j).trans (columnEquiv μ j).symm)

lemma columnSorting_mem (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) :
    columnSorting μ r hr ∈ columnGroup μ :=
  fiberPermutation_rank (col μ) _

lemma columnSorting_row (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r)
    (x : μ.cells) : row μ (columnSorting μ r hr x) ≤ r.1 x := by
  let e := sortedColumn μ r hr (col μ x)
  have h := strictMono_fin_nat_le _ (sortedColumn_mono μ r hr (col μ x)) (e ⟨x,rfl⟩)
  change (e ⟨x,rfl⟩).val ≤ r.1 (e.symm (e ⟨x,rfl⟩)).val at h
  erw [Equiv.symm_apply_apply] at h
  exact h

lemma transversal_eq_column (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) :
    ∃ c : columnGroup μ, r.1=fun x => row μ (c.1 x) := by
  let c := columnSorting μ r hr
  have hle := columnSorting_row μ r hr
  have heq : (∑ x, row μ (c x))=∑ x, r.1 x := by
    rw [rowSum]
    exact Fintype.sum_equiv c _ _ (fun _ => rfl)
  refine ⟨⟨c,columnSorting_mem μ r hr⟩,funext (fun x => ?_)⟩
  exact (Finset.sum_eq_sum_iff_of_le (fun x _ => hle x)).mp heq x (Finset.mem_univ x) |>.symm

lemma column_row_injective (μ : YoungDiagram) :
    Function.Injective (fun c : columnGroup μ => fun x => row μ (c.1 x)) := by
  intro c d h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact Prod.ext (congrFun h x) ((c.2 x).trans (d.2 x).symm)

end
end YoungTabloid
end PartialPermutation
end

end OAI


