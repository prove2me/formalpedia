-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DeficitCounts
-- name    : OAI_RepresentationTheory_PartialPermutation_DeficitCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:44:27.432092+00:00
-- url     : https://prove2.me/theorems/de67da2f-b645-4666-86c9-fbab930fad6f
-- title:
--   Removing the top row of a Young diagram and coding the diagrams of fixed deficit
-- statement:
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ (row $i$, column $j$, both indexed from $0$) closed downwards for the componentwise order. Write $|\mu|$ for its number of cells, $r_0(\mu)$ and $c_0(\mu)$ for the lengths of its first row and first column, $\mu^{t}=\{(j,i) : (i,j)\in\mu\}$ for its transpose, and $\mathrm{Shape}(n)$ for the set of Young diagrams with $n$ cells.
--
--   1. **Removing the top row.** The diagram obtained by deleting row $0$ and moving every other row up by one is
--   $$
--   \mu^{\downarrow}=\{(i,j)\in\mathbb{N}\times\mathbb{N} : (i+1,j)\in\mu\}.
--   $$
--   It is again a Young diagram, and $(i,j)\mapsto(i+1,j)$ is a bijection from the cells of $\mu^{\downarrow}$ onto the cells of $\mu$ outside row $0$.
--   2. **Counts.** The map $(0,j)\mapsto j$ is a bijection from the cells of row $0$ onto $\{0,\dots,r_0(\mu)-1\}$; hence $|\mu^{\downarrow}|=|\mu|-r_0(\mu)$. Moreover $|\mu^{t}|=|\mu|$.
--   3. **Diagrams of fixed deficit.** The deficit of $\mu$ is $|\mu|-\max(r_0(\mu),c_0(\mu))$, the number of cells outside a longest line (the first row or the first column, whichever is longer). For $n,k\in\mathbb{N}$ let
--   $$
--   \mathrm{Shape}(n,k)=\{\mu\in\mathrm{Shape}(n) : |\mu|-\max(r_0(\mu),c_0(\mu))=k\},
--   $$
--   a finite set.
--   4. **Deficit code.** The map $\mathrm{Shape}(n,k)\to\{\mathrm{true},\mathrm{false}\}\times\mathrm{Shape}(k)$ removes a longest line:
--   $$
--   \mu\longmapsto\begin{cases}(\mathrm{true},\ \mu^{\downarrow}), & c_0(\mu)\le r_0(\mu),\\ (\mathrm{false},\ (\mu^{t})^{\downarrow}), & c_0(\mu)>r_0(\mu).\end{cases}
--   $$
--   In both cases the resulting diagram has exactly $k$ cells.
--
--   A diagram is determined by the length of its top row together with $\mu^{\downarrow}$, and the longest line of a diagram in $\mathrm{Shape}(n,k)$ has length $n-k$; hence the deficit code is injective and $|\mathrm{Shape}(n,k)|\le2p(k)$, where $p(k)$ is the number of Young diagrams with $k$ cells. This bound, uniform in $n$, controls how many shapes of a given deficit contribute to sums over all shapes of size $n$.
--
--   **Formalization Note** `dropTop μ` is item 1, with cells the `Finset.preimage` of `μ.cells` under the shift, whose injectivity is `shift_injective`; `mem_dropTop`, `lowerEquiv` and `rowEquiv` give the description and the bijections, and `dropTop_card`, `transpose_card` the counts. `ShapeDeficit n k` is item 3, written with natural-number subtraction, which is exact because a longest line has at most $|\mu|$ cells; `deficitCode n k` is item 4, with values in `Bool` paired with `Shape k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/DeficitCounts.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/DeficitCounts.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace DiagramCounting
noncomputable section
open Finset

lemma shift_injective : Function.Injective (fun x : ℕ × ℕ => (x.1+1,x.2)) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Nat.add_right_cancel h.1) h.2

def dropTop (μ : YoungDiagram) : YoungDiagram where
  cells := μ.cells.preimage (fun x : ℕ × ℕ => (x.1+1,x.2)) shift_injective.injOn
  isLowerSet := by
    intro y x hxy hy
    simp only [Finset.mem_coe,Finset.mem_preimage] at hy ⊢
    have hh : (x.1+1,x.2) ≤ (y.1+1,y.2) := ⟨Nat.add_le_add_right hxy.1 1,hxy.2⟩
    exact μ.isLowerSet hh hy

lemma mem_dropTop (μ : YoungDiagram) (i j : ℕ) :
    (i,j) ∈ dropTop μ ↔ (i+1,j) ∈ μ := by
  change (i,j) ∈ μ.cells.preimage (fun x : ℕ × ℕ => (x.1+1,x.2)) shift_injective.injOn ↔ _
  exact Finset.mem_preimage

def lowerEquiv (μ : YoungDiagram) : (dropTop μ).cells ≃ {x : μ.cells // x.1.1≠0} where
  toFun x := ⟨⟨(x.1.1+1,x.1.2), (mem_dropTop μ _ _).mp x.2⟩,Nat.succ_ne_zero _⟩
  invFun x := ⟨(x.1.1.1-1,x.1.1.2), by
    apply (mem_dropTop μ _ _).mpr
    have he : x.1.1.1-1+1=x.1.1.1 := by have h:=x.2; omega
    rw [he]; exact x.1.2⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · have h:=x.2; dsimp; omega
    · rfl

def rowEquiv (μ : YoungDiagram) : {x : μ.cells // x.1.1=0} ≃ Fin (μ.rowLen 0) where
  toFun x := ⟨x.1.1.2, by have h:=μ.mem_iff_lt_rowLen.mp x.1.2; simpa [x.2] using h⟩
  invFun i := ⟨⟨(0,i), μ.mem_iff_lt_rowLen.mpr i.2⟩,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.2.symm rfl
  right_inv _ := rfl

lemma dropTop_card (μ : YoungDiagram) :
    (dropTop μ).cells.card = μ.cells.card-μ.rowLen 0 := by
  have h := Fintype.card_congr (lowerEquiv μ)
  rw [Fintype.card_subtype_compl] at h
  have he := Fintype.card_congr (rowEquiv μ)
  simpa only [Fintype.card_coe,Fintype.card_fin,he] using h

lemma transpose_card (μ : YoungDiagram) : μ.transpose.cells.card=μ.cells.card := by
  have e : μ.cells ≃ μ.transpose.cells := {
    toFun := fun x => ⟨x.1.swap, by simpa only [YoungDiagram.mem_cells,
      YoungDiagram.mem_transpose,Prod.swap_swap] using x.2⟩
    invFun := fun x => ⟨x.1.swap,YoungDiagram.mem_transpose.mp x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm

def ShapeDeficit (n k : ℕ) :=
  {μ : Shape n // μ.1.cells.card-max (μ.1.rowLen 0) (μ.1.colLen 0)=k}

instance (n k : ℕ) : Fintype (ShapeDeficit n k) := by
  classical
  unfold ShapeDeficit
  infer_instance

def deficitCode (n k : ℕ) (μ : ShapeDeficit n k) : Bool × Shape k :=
  if h : μ.1.1.colLen 0 ≤ μ.1.1.rowLen 0 then
    (true,⟨dropTop μ.1.1, by rw [dropTop_card]; simpa only [max_eq_left h] using μ.2⟩)
  else
    (false,⟨dropTop μ.1.1.transpose, by
      rw [dropTop_card,transpose_card,YoungDiagram.rowLen_transpose]
      simpa only [max_eq_right (le_of_not_ge h)] using μ.2⟩)

end
end DiagramCounting
end PartialPermutation
end

end OAI


