-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_FillingExtensions
-- name    : OAI_RepresentationTheory_PartialPermutation_FillingExtensions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:32:02.137081+00:00
-- url     : https://prove2.me/theorems/40491555-7108-44f5-96ba-0ba2e149fc89
-- title:
--   Transporting and concatenating standard fillings of finite posets
-- statement:
--   A *standard filling* of a finite poset $\alpha$ with $n=|\alpha|$ elements is a bijection $T:\alpha\to\{0,1,\dots,n-1\}$ that is strictly increasing: $a<b$ implies $T(a)<T(b)$. Equivalently, it is a linear extension of $\alpha$ written as a labelling. Write $\mathrm{SF}(\alpha)$ for the set of standard fillings of $\alpha$. Throughout, $P$ is a decidable predicate on $\alpha$, $A=\{a\in\alpha : P(a)\}$ and $B=\alpha\setminus A$, both with the induced order.
--
--   1. **Transport along order isomorphisms.** An order isomorphism $e:\alpha\to\beta$ of finite posets induces a bijection $\mathrm{SF}(\alpha)\to\mathrm{SF}(\beta)$, $T\mapsto T\circ e^{-1}$ (the label sets are identified using $|\alpha|=|\beta|$), with inverse $S\mapsto S\circ e$.
--   2. **Concatenated enumeration.** One has $|A|+|B|=|\alpha|$, and standard fillings $T\in\mathrm{SF}(A)$, $U\in\mathrm{SF}(B)$ combine into the bijection $T\sqcup U:\alpha\to\{0,\dots,|\alpha|-1\}$,
--   $$
--   (T\sqcup U)(a)=\begin{cases}T(a), & a\in A,\\ |A|+U(a), & a\in B,\end{cases}
--   $$
--   which labels $A$ first, with $0,\dots,|A|-1$, and then $B$, with $|A|,\dots,|\alpha|-1$.
--   3. **Extension from a lower set.** If $A$ is a lower set of $\alpha$ (whenever $a\le b$ and $b\in A$, also $a\in A$), then $T\sqcup U$ is a standard filling of $\alpha$; this defines the extension map $\mathrm{SF}(A)\times\mathrm{SF}(B)\to\mathrm{SF}(\alpha)$.
--   4. **Cells of a subdiagram.** For Young diagrams $\mu\subseteq\nu$ (finite sets of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ closed downwards for the componentwise order, which is also the order on cells), the identity on coordinates is an order isomorphism between the cells of $\mu$ and the subposet $\{x\in\nu : x\in\mu\}$ of the cells of $\nu$.
--
--   These constructions compare numbers of standard fillings. With one filling of $B$ (or of $A$) held fixed, the extension map is injective in the other argument, so both a lower set $A$ and its complement $B$ have at most as many standard fillings as $\alpha$. Combined with items 1 and 4 this shows that the number of standard Young tableaux is monotone under inclusion of Young diagrams.
--
--   **Formalization Note** `StandardFilling α` is the subtype of `α ≃ Fin (Fintype.card α)` consisting of strictly monotone equivalences. Item 1 is `fillingCongr`; item 2 is `concatEnumeration`, with `concatEnumeration_pos` and `concatEnumeration_neg` recording its two cases and `sum_subtype_card` the cardinality identity; item 3 is `extendFilling`; item 4 is `subdiagramCellsEquiv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/FillingExtensions.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/FillingExtensions.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

section Extension
variable {α β : Type*} [Fintype α] [PartialOrder α] [Fintype β] [PartialOrder β]

def fillingCongr (e : α ≃o β) : StandardFilling α ≃ StandardFilling β where
  toFun T := ⟨e.symm.toEquiv.trans (T.1.trans (finCongr (Fintype.card_congr e.toEquiv))),
    (Fin.cast_strictMono (Fintype.card_congr e.toEquiv)).comp (T.2.comp e.symm.strictMono)⟩
  invFun T := ⟨e.toEquiv.trans (T.1.trans (finCongr (Fintype.card_congr e.symm.toEquiv))),
    (Fin.cast_strictMono (Fintype.card_congr e.symm.toEquiv)).comp (T.2.comp e.strictMono)⟩
  left_inv T := by apply Subtype.ext; apply Equiv.ext; intro a; apply Fin.ext; simp
  right_inv T := by apply Subtype.ext; apply Equiv.ext; intro a; apply Fin.ext; simp

omit [PartialOrder α] in
lemma sum_subtype_card (P : α → Prop) [DecidablePred P] :
    Fintype.card {a // P a} + Fintype.card {a // ¬P a} = Fintype.card α := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.sumCompl P)

def concatEnumeration (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a}) :
    α ≃ Fin (Fintype.card α) :=
  (Equiv.sumCompl P).symm.trans ((Equiv.sumCongr T.1 U.1).trans
    (finSumFinEquiv.trans (finCongr (sum_subtype_card P))))

lemma concatEnumeration_pos (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (a : α) (ha : P a) : (concatEnumeration P T U a).val = (T.1 ⟨a,ha⟩).val := by
  simp [concatEnumeration, Equiv.sumCompl_symm_apply_of_pos ha]

lemma concatEnumeration_neg (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (a : α) (ha : ¬P a) : (concatEnumeration P T U a).val =
      Fintype.card {a // P a} + (U.1 ⟨a,ha⟩).val := by
  simp [concatEnumeration, Equiv.sumCompl_symm_apply_of_neg ha]

def extendFilling (P : α → Prop) [DecidablePred P] (hP : IsLowerSet {a | P a})
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a}) :
    StandardFilling α := by
  refine ⟨concatEnumeration P T U, ?_⟩
  intro a b hab
  change (concatEnumeration P T U a).val < (concatEnumeration P T U b).val
  by_cases ha : P a <;> by_cases hb : P b
  · rw [concatEnumeration_pos P T U a ha, concatEnumeration_pos P T U b hb]
    exact T.2 (show (⟨a,ha⟩ : {a // P a}) < ⟨b,hb⟩ from hab)
  · rw [concatEnumeration_pos P T U a ha, concatEnumeration_neg P T U b hb]
    have h := (T.1 ⟨a,ha⟩).isLt
    omega
  · exact (ha (hP hab.le hb)).elim
  · rw [concatEnumeration_neg P T U a ha, concatEnumeration_neg P T U b hb]
    exact Nat.add_lt_add_left (U.2 (show (⟨a,ha⟩ : {a // ¬P a}) < ⟨b,hb⟩ from hab)) _

end Extension

def subdiagramCellsEquiv {μ ν : YoungDiagram} (h : μ ≤ ν) :
    μ.cells ≃o {x : ν.cells // x.1 ∈ μ.cells} where
  toFun x := ⟨⟨x.1,h x.2⟩,x.2⟩
  invFun x := ⟨x.1.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end
end Tableau
end PartialPermutation
end

end OAI


