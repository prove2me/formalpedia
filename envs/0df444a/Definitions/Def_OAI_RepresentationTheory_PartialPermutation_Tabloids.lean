-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Tabloids
-- name    : OAI_RepresentationTheory_PartialPermutation_Tabloids
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:49:52.853355+00:00
-- url     : https://prove2.me/theorems/79abce6a-0716-4ebc-887b-e6b4b142806e
-- title:
--   Tabloids of a Young diagram, the relabelling action and the column group
-- statement:
--   Let $\mu$ be a Young diagram, a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ closed downwards for the componentwise order, with $n=|\mu|$ cells. Write $\mathrm{row}(i,j)=i$ and $\mathrm{col}(i,j)=j$, and let $c_j$ be the length of column $j$. The group $\mathrm{Sym}(\mu)$ of all permutations of the set of cells plays the role of the symmetric group $S_n$, the cells themselves serving as the $n$ letters.
--
--   1. **Tabloids.** A tabloid of shape $\mu$ is a function $t:\mu\to\mathbb{N}$ of the form $t=\mathrm{row}\circ p$ for some $p\in\mathrm{Sym}(\mu)$: letter $x$ is placed in row $t(x)$, and each row receives exactly as many letters as it has cells. Equivalently, a tabloid is a numbering of the cells by the letters, remembered only up to permutations within each row. Since $p\mapsto\mathrm{row}\circ p$ maps $\mathrm{Sym}(\mu)$ onto the tabloids, there are finitely many of them.
--   2. **Canonical tabloid.** $t_0=\mathrm{row}$, coming from $p=\mathrm{id}$: every letter sits in its own row.
--   3. **Relabelling action.** For $g\in\mathrm{Sym}(\mu)$ and a tabloid $t$,
--   $$
--   (g\cdot t)(x)=t(g^{-1}x)\qquad(x\in\mu)
--   $$
--   is again a tabloid. This is a left action: $1\cdot t=t$ and $(gh)\cdot t=g\cdot(h\cdot t)$, so each $g$ induces a permutation of the set of tabloids.
--   4. **Row-sum invariant.** Every tabloid satisfies $\sum_{x\in\mu}t(x)=\sum_{x\in\mu}\mathrm{row}(x)$.
--   5. **Column group.** $C_\mu=\{g\in\mathrm{Sym}(\mu) : \mathrm{col}(gx)=\mathrm{col}(x)\text{ for all }x\in\mu\}$, the subgroup of permutations keeping every letter in its column.
--   6. **Columns.** $\mathrm{Col}_j=\{x\in\mu : \mathrm{col}(x)=j\}$; the map $x\mapsto\mathrm{row}(x)$ is a bijection from $\mathrm{Col}_j$ onto $\{0,\dots,c_j-1\}$, so $|\mathrm{Col}_j|=c_j$.
--
--   These are the ingredients of the permutation module spanned by the tabloids, on which $\mathrm{Sym}(\mu)$ acts by relabelling, and of the column antisymmetrizer $\sum_{c\in C_\mu}\mathrm{sgn}(c)\,c$ used to construct the Specht module of shape $\mu$.
--
--   **Formalization Note** `Tabloid μ` is the subtype of functions `μ.cells → ℕ` of the form `fun x => row μ (p x)`. The items correspond to `ofPerm` and `ofPerm_surjective` (item 1), `canonical` (item 2), `relabel`, `relabel_apply`, `relabel_one`, `relabel_mul` and `relabelEquiv` (item 3), `rowSum` (item 4), `columnGroup`, a `Subgroup (Equiv.Perm μ.cells)` (item 5), and `Col`, `columnEquiv`, `col_card` (item 6). The file uses classical decidability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Tabloids.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Tabloids.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace YoungTabloid
noncomputable section
open Finset
open scoped Classical

def row (μ : YoungDiagram) (x : μ.cells) : ℕ := x.1.1
def col (μ : YoungDiagram) (x : μ.cells) : ℕ := x.1.2

def Tabloid (μ : YoungDiagram) :=
  {r : μ.cells → ℕ // ∃ p : Equiv.Perm μ.cells, r = fun x => row μ (p x)}

def ofPerm (μ : YoungDiagram) (p : Equiv.Perm μ.cells) : Tabloid μ :=
  ⟨fun x => row μ (p x),p,rfl⟩

lemma ofPerm_surjective (μ : YoungDiagram) : Function.Surjective (ofPerm μ) := by
  rintro ⟨r,p,rfl⟩
  exact ⟨p,rfl⟩

instance (μ : YoungDiagram) : Finite (Tabloid μ) :=
  Finite.of_surjective (ofPerm μ) (ofPerm_surjective μ)
instance (μ : YoungDiagram) : Fintype (Tabloid μ) := Fintype.ofFinite _

def canonical (μ : YoungDiagram) : Tabloid μ := ofPerm μ 1

def relabel (μ : YoungDiagram) (g : Equiv.Perm μ.cells) (r : Tabloid μ) : Tabloid μ := by
  refine ⟨fun x => r.1 (g⁻¹ x),?_⟩
  obtain ⟨p,hp⟩ := r.2
  exact ⟨g⁻¹.trans p,by rw [hp]; rfl⟩

@[simp] lemma relabel_apply (μ : YoungDiagram) (g : Equiv.Perm μ.cells) (r : Tabloid μ)
    (x : μ.cells) : (relabel μ g r).1 x=r.1 (g⁻¹ x) := rfl

lemma relabel_one (μ : YoungDiagram) (r : Tabloid μ) : relabel μ 1 r=r := by rfl
lemma relabel_mul (μ : YoungDiagram) (g h : Equiv.Perm μ.cells) (r : Tabloid μ) :
    relabel μ (g*h) r=relabel μ g (relabel μ h r) := by
  apply Subtype.ext
  funext x
  simp only [relabel_apply,mul_inv_rev,Equiv.Perm.mul_apply]

def relabelEquiv (μ : YoungDiagram) (g : Equiv.Perm μ.cells) : Equiv.Perm (Tabloid μ) where
  toFun := relabel μ g
  invFun := relabel μ g⁻¹
  left_inv r := by rw [← relabel_mul,inv_mul_cancel,relabel_one]
  right_inv r := by rw [← relabel_mul,mul_inv_cancel,relabel_one]

lemma rowSum (μ : YoungDiagram) (r : Tabloid μ) :
    (∑ x, r.1 x) = ∑ x, row μ x := by
  obtain ⟨p,hp⟩ := r.2
  rw [hp]
  exact Fintype.sum_equiv p _ _ (fun _ => rfl)

def columnGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm μ.cells) where
  carrier := {g | ∀ x, col μ (g x)=col μ x}
  one_mem' _ := rfl
  mul_mem' hg hh x := (hg _).trans (hh x)
  inv_mem' := by
    intro g hg x
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hg (g⁻¹ x)).symm

def Col (μ : YoungDiagram) (j : ℕ) := {x : μ.cells // col μ x=j}

instance (μ : YoungDiagram) (j : ℕ) : Fintype (Col μ j) := by dsimp [Col]; infer_instance

def columnEquiv (μ : YoungDiagram) (j : ℕ) : Col μ j ≃ Fin (μ.colLen j) where
  toFun x := ⟨row μ x.1, by
    have h := μ.mem_iff_lt_colLen.mp x.1.2
    have hj : x.1.1.2=j := x.2
    simpa only [row, hj] using h⟩
  invFun i := ⟨⟨(i,j),μ.mem_iff_lt_colLen.mpr i.2⟩,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.2.symm
  right_inv _ := rfl

lemma col_card (μ : YoungDiagram) (j : ℕ) : Fintype.card (Col μ j)=μ.colLen j := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (columnEquiv μ j)

end
end YoungTabloid
end PartialPermutation
end

end OAI


