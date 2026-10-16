-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Truncation
-- name    : OAI_RepresentationTheory_PartialPermutation_Truncation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:38:59.186781+00:00
-- url     : https://prove2.me/theorems/e1ed8776-788e-4b0c-9069-ed1d3f3dc784
-- title:
--   Truncating the lower rows of a Young diagram along a standard filling
-- statement:
--   Let $\mu$ be a Young diagram, a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ (row $i$, column $j$, both indexed from $0$) closed downwards for the componentwise order, with $|\mu|$ cells and top row of length $r_0$. Let $L(\mu)=\{(i,j)\in\mu : i\ne0\}$ be the poset of cells below the top row, and let $T$ be a standard filling of $L(\mu)$, i.e. a strictly increasing bijection $T:L(\mu)\to\{0,\dots,|L(\mu)|-1\}$. Let $b\in\mathbb{N}$.
--
--   1. **Truncated diagram.** The truncation of $\mu$ at level $b$ along $T$ is
--   $$
--   \mu_{T,b}=\{(i,j)\in\mu : i=0\}\ \cup\ \{x\in L(\mu) : T(x)<b\},
--   $$
--   the whole top row together with the lower cells carrying one of the labels $0,\dots,b-1$. Because $T$ is increasing, $\mu_{T,b}$ is again a Young diagram.
--   2. **Membership and inclusion.** A pair $x\in\mathbb{N}\times\mathbb{N}$ is a cell of $\mu_{T,b}$ if and only if $x\in\mu$ and, in case $x$ is not in row $0$, $T(x)<b$. In particular $\mu_{T,b}\subseteq\mu$.
--   3. **Counting the lower cells.** If $b\le|\mu|-r_0$, then $T$ restricts to a bijection from the cells of $\mu_{T,b}$ outside row $0$ onto $\{0,\dots,b-1\}$; thus $\mu_{T,b}$ has exactly $b$ cells below its top row.
--
--   The truncation produces a subdiagram of $\mu$ with the same top row and exactly $b$ further cells, hence with $r_0+b$ cells. Since the number $f^\mu$ of standard Young tableaux is monotone under inclusion of diagrams, this reduces lower bounds for $f^\mu$ to diagrams of controlled size, and it yields $\binom{r_0}{b}\le f^\mu$ whenever $b\le\min(r_0,|\mu|-r_0)$.
--
--   **Formalization Note** The filling $T$ is an element of `StandardFilling {x : μ.cells // x.1.1 ≠ 0}`. Item 1 is `truncateLower μ T b`, built as a filter of `μ.cells`; `mem_truncateLower` and `truncateLower_le` are item 2; `truncatedLowerEquiv` is item 3, with the hypothesis `b ≤ μ.cells.card - μ.rowLen 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Truncation.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Truncation.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

def truncateLower (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ) : YoungDiagram := by
  classical
  let P : ℕ × ℕ → Prop := fun x => ∃ hx : x ∈ μ.cells,
    ∀ hn : x.1 ≠ 0, (T.1 ⟨⟨x,hx⟩,hn⟩).val < b
  refine ⟨μ.cells.filter P, ?_⟩
  intro y x hxy hy
  obtain ⟨hy,hpy⟩ := Finset.mem_filter.mp hy
  obtain ⟨_,hty⟩ := hpy
  have hx := μ.isLowerSet hxy hy
  apply Finset.mem_filter.mpr
  refine ⟨hx,hx,?_⟩
  intro hn
  have hny : y.1≠0 := by intro he; exact hn (Nat.eq_zero_of_le_zero (hxy.1.trans_eq he))
  have hmono : (T.1 ⟨⟨x,hx⟩,hn⟩).val ≤ (T.1 ⟨⟨y,hy⟩,hny⟩).val :=
    T.2.monotone (show (⟨⟨x,hx⟩,hn⟩ : {x : μ.cells // x.1.1≠0}) ≤
      ⟨⟨y,hy⟩,hny⟩ from hxy)
  exact hmono.trans_lt (hty hny)

lemma mem_truncateLower (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ) (x : ℕ × ℕ) :
    x ∈ (truncateLower μ T b).cells ↔ ∃ hx : x ∈ μ.cells,
      ∀ hn : x.1 ≠ 0, (T.1 ⟨⟨x,hx⟩,hn⟩).val < b := by
  classical
  simp only [truncateLower, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.choose,h⟩⟩

lemma truncateLower_le (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ) :
    truncateLower μ T b ≤ μ := by
  intro x hx
  exact (mem_truncateLower μ T b x).mp hx |>.choose

def truncatedLowerEquiv (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ)
    (hb : b ≤ μ.cells.card - μ.rowLen 0) :
    {x : (truncateLower μ T b).cells // x.1.1 ≠ 0} ≃ Fin b := by
  let incl : {x : (truncateLower μ T b).cells // x.1.1 ≠ 0} →
      {x : μ.cells // x.1.1 ≠ 0} := fun x =>
    ⟨⟨x.1.1,truncateLower_le μ T b x.1.2⟩,x.2⟩
  have hb' : b ≤ Fintype.card {x : μ.cells // x.1.1≠0} := by rwa [lower_card]
  let val : Fin b → {x : μ.cells // x.1.1 ≠ 0} := fun i =>
    T.1.symm ⟨i.val,i.isLt.trans_le hb'⟩
  have hv : ∀ i, (val i).1.1 ∈ (truncateLower μ T b).cells := by
    intro i
    apply (mem_truncateLower μ T b _).mpr
    refine ⟨(val i).1.2,?_⟩
    intro hn
    have he : (⟨⟨(val i).1.1,(val i).1.2⟩,hn⟩ : {x : μ.cells // x.1.1 ≠ 0}) = val i := rfl
    rw [he]
    simp [val]
  have ht : ∀ x, (T.1 (incl x)).val < b := by
    intro x
    exact ((mem_truncateLower μ T b x.1.1).mp x.1.2).choose_spec x.2
  refine {toFun := fun x => ⟨T.1 (incl x), ht x⟩
          invFun := fun i => ⟨⟨(val i).1.1,hv i⟩,(val i).2⟩
          left_inv := ?_
          right_inv := ?_}
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    have he : val ⟨T.1 (incl x), ht x⟩ = incl x := by simp [val]
    exact congrArg (fun y : {x : μ.cells // x.1.1≠0} => y.1.1) he
  · intro i
    apply Fin.ext
    change (T.1 (val i)).val = i.val
    simp [val]

end
end Tableau
end PartialPermutation
end

end OAI


