-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RowBounds
-- name    : OAI_RepresentationTheory_PartialPermutation_RowBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:36:40.182777+00:00
-- url     : https://prove2.me/theorems/2b6a4aad-8412-4b90-8b4e-0a4c6e5692c4
-- title:
--   Initial segments of the top row of a Young diagram and the cells below the top row
-- statement:
--   Let $\mu$ be a Young diagram: a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ (row $i$, column $j$, both indexed from $0$) closed downwards for the componentwise order. Write $|\mu|$ for its number of cells and $r_i$ for the length of row $i$, so that the top row (row $0$) consists of the cells $(0,j)$ with $j<r_0$.
--
--   1. **Top-row prefix.** For $c\in\mathbb{N}$, the predicate $\mathrm{Pre}_c$ on cells holds at $(i,j)$ if and only if $i=0$ and $j<c$; it selects the first $c$ cells of the top row (the whole top row if $c\ge r_0$).
--   2. **Counting the prefix.** If $c\le r_0$, the map $(0,j)\mapsto j$ is a bijection from $\{x\in\mu : \mathrm{Pre}_c(x)\}$ onto $\{0,\dots,c-1\}$.
--   3. **Counting the top row.** The map $(0,j)\mapsto j$ is a bijection from the cells of row $0$ onto $\{0,\dots,r_0-1\}$.
--   4. **Cells below the top row.** The number of cells outside row $0$ is
--   $$
--   \#\{(i,j)\in\mu : i\ne0\}=|\mu|-r_0.
--   $$
--   5. **Lower cells outside the prefix.** For every $c$, a cell outside row $0$ automatically lies outside $\mathrm{Pre}_c$, and the identity gives a bijection between the cells that lie outside $\mathrm{Pre}_c$ and outside row $0$ and the cells outside row $0$.
--
--   The prefix $\mathrm{Pre}_c$ is a lower set of the poset of cells, and when $c=r_1$ is the length of the second row, the top-row cells outside the prefix are incomparable with all cells below the top row. These bookkeeping facts give the binomial lower bound $\binom{|\mu|-r_1}{|\mu|-r_0}\le f^\mu$ for the number $f^\mu$ of standard Young tableaux of shape $\mu$, i.e. of strictly increasing bijections from the cells onto $\{0,\dots,|\mu|-1\}$.
--
--   **Formalization Note** Item 1 is `topPrefix μ c` (with a `DecidablePred` instance), item 2 is `topPrefixEquiv` (assuming `c ≤ μ.rowLen 0`), item 3 is `topRowEquiv`, item 4 is `lower_card`, and item 5 is `lowerInUpperEquiv`. The subtraction in item 4 is natural-number subtraction, which is exact here because the top row has at most $|\mu|$ cells.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/RowBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/RowBounds.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

def topPrefix (μ : YoungDiagram) (c : ℕ) (x : μ.cells) : Prop :=
  x.1.1=0 ∧ x.1.2<c

instance (μ : YoungDiagram) (c : ℕ) : DecidablePred (topPrefix μ c) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

def topPrefixEquiv (μ : YoungDiagram) (c : ℕ) (hc : c ≤ μ.rowLen 0) :
    {x // topPrefix μ c x} ≃ Fin c where
  toFun x := ⟨x.1.1.2,x.2.2⟩
  invFun i := ⟨⟨(0,i), μ.mem_iff_lt_rowLen.mpr (i.2.trans_le hc)⟩,rfl,i.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.2.1.symm rfl
  right_inv _ := rfl

def topRowEquiv (μ : YoungDiagram) : {x : μ.cells // x.1.1=0} ≃ Fin (μ.rowLen 0) where
  toFun x := ⟨x.1.1.2, by have h:=μ.mem_iff_lt_rowLen.mp x.1.2; simpa [x.2] using h⟩
  invFun i := ⟨⟨(0,i), μ.mem_iff_lt_rowLen.mpr i.2⟩,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.2.symm rfl
  right_inv _ := rfl

lemma lower_card (μ : YoungDiagram) :
    Fintype.card {x : μ.cells // x.1.1 ≠ 0} = μ.cells.card - μ.rowLen 0 := by
  rw [Fintype.card_subtype_compl]
  have h := Fintype.card_congr (topRowEquiv μ)
  rw [Fintype.card_fin] at h
  rw [h, Fintype.card_coe]

def lowerInUpperEquiv (μ : YoungDiagram) (c : ℕ) :
    {x : {x // ¬topPrefix μ c x} // x.1.1.1 ≠ 0} ≃ {x : μ.cells // x.1.1 ≠ 0} where
  toFun x := ⟨x.1.1,x.2⟩
  invFun x := ⟨⟨x.1,fun h => x.2 h.1⟩,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end Tableau
end PartialPermutation
end

end OAI


