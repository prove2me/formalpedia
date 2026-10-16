-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Interleavings
-- name    : OAI_RepresentationTheory_PartialPermutation_Interleavings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:33:10.438961+00:00
-- url     : https://prove2.me/theorems/a0c46430-da99-40b8-b738-8da17e14193c
-- title:
--   Interleaving standard fillings of two mutually incomparable parts of a finite poset
-- statement:
--   Let $\alpha$ be a finite poset with $n=|\alpha|$ elements and let $P$ be a decidable predicate on $\alpha$, which splits $\alpha$ into $A=\{a\in\alpha : P(a)\}$ and its complement $B$, each with the induced order. A *standard filling* of a finite poset with $m$ elements is a strictly increasing bijection onto $\{0,\dots,m-1\}$. For a subset $s\subseteq\{0,\dots,n-1\}$ write $s_{(0)}<s_{(1)}<\cdots$ for its elements in increasing order, and $s^{\mathrm c}=\{0,\dots,n-1\}\setminus s$.
--
--   1. **Complement size.** If $|s|=|A|$, then $|s^{\mathrm c}|=|B|$.
--   2. **Interleaved enumeration.** For standard fillings $T$ of $A$ and $U$ of $B$ and a subset $s\subseteq\{0,\dots,n-1\}$ with $|s|=|A|$, define the bijection $\phi_{T,U,s}:\alpha\to\{0,\dots,n-1\}$ by
--   $$
--   \phi_{T,U,s}(a)=\begin{cases}s_{(T(a))}, & a\in A,\\ (s^{\mathrm c})_{(U(a))}, & a\in B.\end{cases}
--   $$
--   Thus $A$ receives the labels in $s$, in the order prescribed by $T$, and $B$ receives the labels in $s^{\mathrm c}$, in the order prescribed by $U$.
--   3. **Interleaved filling.** If $P$ is constant along strict comparabilities, that is, $P(a)\iff P(b)$ whenever $a<b$ in $\alpha$ (no element of $A$ is comparable with an element of $B$), then $\phi_{T,U,s}$ is a standard filling of $\alpha$.
--
--   For fixed $T$ and $U$, distinct subsets $s$ give distinct fillings, so a finite poset that splits into two mutually incomparable parts $A$ and $B$ has at least $\binom{n}{|A|}$ standard fillings. For Young diagrams this is applied after removing the initial segment of the top row whose length is that of the second row: the remaining top-row cells and the cells of the lower rows are mutually incomparable, which yields binomial lower bounds for the number of standard Young tableaux.
--
--   **Formalization Note** The subset $s$ is a `Finset (Fin (Fintype.card α))` bundled with the proof that its cardinality equals `Fintype.card {a // P a}`, and $s_{(k)}$ is `s.orderEmbOfFin`. Item 1 is `interleaving_compl_card`, item 2 is `interleavingEnumeration` (with its two cases `interleavingEnumeration_pos` and `interleavingEnumeration_neg`), and item 3 is `interleaveFilling`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Interleavings.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Interleavings.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

section Interleave
variable {α : Type*} [Fintype α] [PartialOrder α]

omit [PartialOrder α] in
lemma interleaving_compl_card (P : α → Prop) [DecidablePred P]
    (s : {s : Finset (Fin (Fintype.card α)) // s.card=Fintype.card {a // P a}}) :
    s.1ᶜ.card = Fintype.card {a // ¬P a} := by
  rw [Finset.card_compl, Fintype.card_fin, s.2, Fintype.card_subtype_compl]

def interleavingEnumeration (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (s : {s : Finset (Fin (Fintype.card α)) // s.card=Fintype.card {a // P a}}) :
    α ≃ Fin (Fintype.card α) :=
  (Equiv.sumCompl P).symm.trans ((Equiv.sumCongr T.1 U.1).trans
    (finSumEquivOfFinset s.2 (interleaving_compl_card P s)))

lemma interleavingEnumeration_pos (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (s : {s : Finset (Fin (Fintype.card α)) // s.card=Fintype.card {a // P a}})
    (a : α) (ha : P a) :
    interleavingEnumeration P T U s a = s.1.orderEmbOfFin s.2 (T.1 ⟨a,ha⟩) := by
  simp [interleavingEnumeration, Equiv.sumCompl_symm_apply_of_pos ha]

lemma interleavingEnumeration_neg (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (s : {s : Finset (Fin (Fintype.card α)) // s.card=Fintype.card {a // P a}})
    (a : α) (ha : ¬P a) :
    interleavingEnumeration P T U s a = s.1ᶜ.orderEmbOfFin
      (interleaving_compl_card P s) (U.1 ⟨a,ha⟩) := by
  simp [interleavingEnumeration, Equiv.sumCompl_symm_apply_of_neg ha]

def interleaveFilling (P : α → Prop) [DecidablePred P]
    (hP : ∀ a b, a < b → (P a ↔ P b))
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (s : {s : Finset (Fin (Fintype.card α)) // s.card=Fintype.card {a // P a}}) :
    StandardFilling α := by
  refine ⟨interleavingEnumeration P T U s, ?_⟩
  intro a b hab
  by_cases ha : P a
  · have hb := (hP a b hab).mp ha
    rw [interleavingEnumeration_pos P T U s a ha, interleavingEnumeration_pos P T U s b hb]
    exact (s.1.orderEmbOfFin s.2).strictMono (T.2 hab)
  · have hb : ¬P b := fun hp => ha ((hP a b hab).mpr hp)
    rw [interleavingEnumeration_neg P T U s a ha, interleavingEnumeration_neg P T U s b hb]
    exact (s.1ᶜ.orderEmbOfFin _).strictMono (U.2 hab)

end Interleave

end
end Tableau
end PartialPermutation
end

end OAI


