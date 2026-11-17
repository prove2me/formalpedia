-- Prove2me | Definitions.Def_APFPaper5_K2_HoldScore
-- name    : APFPaper5_K2_HoldScore
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:22:04.798486+00:00
-- url     : https://prove2.me/theorems/8a5a26d0-0d7d-4cd2-beeb-3ae3786152b7
-- title:
--   Rearranged classes and scores through holds
-- statement:
--   RearrangesFamily records a state map, rearrangement and side flips. heldAfter acts by precomposition, while holdScore uses a supplied table and ignores flips. KeepsTable and ExecutesAs are explicit predicates, not derived physical properties.
--
--   **Supplied data and hypotheses**
--
--   - Every parameter and hypothesis in the exact source declaration remains exposed; no author input is adopted.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFPaper5_K2_HoldScore; Pullbacks v39, SHA-256 db42864b67d77b051dbb30a85f269d1f3910440f7fcb471b88f1dcb0b9c7bc0f. Definitions.Def_APFPaper5_K2_HoldScore; pullbacks v39; SHA-256 db42864b67d77b051dbb30a85f269d1f3910440f7fcb471b88f1dcb0b9c7bc0f

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_HoldScore
title: K2's score with a hold in the channel: K1's score between what the hold makes of what is held and what the test reads
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
ruling: the author, 2026-11-15 11:56 HST, "C, proceed as suggested", on
 TEE_UP_K2_score_of_a_completed_word_2026-11-15 (RULING_K2_score_is_K1s_score_through_the_word_2026-11-15):
 the score of a completed word is K1's score between what the word makes of what is held and what the test
 reads; for now the action of a word on what is held is taken from holds only.
source: Paper 5 Supplement v7.33:396-409 (with a process T in the channel the closed score is B(Tx, y)),
 410-420 (orientation closure: reversing the two ends preserves the score). The builder seat's
 Def_APFB02_HoldOnDistinctions (readsAfter, NothingDrawn: the adopted reading of a hold, ruled 2026-11-14
 11:33 HST) and Def_APFPaper5_K1_MarkTable (tableForm). The author, 2026-11-13 15:43 HST: "Under a hold,
 distinctions aren't drawn or erased, just rearranged."
standing: DEFINITIONS. heldAfter and holdScore carry the ruling. RearrangesFamily is the adopted reading
 NothingDrawn with its witness written out and said of a listed family. KeepsTable and HoldScoreNull are
 predicates; neither is assumed anywhere in this file and neither is an adopted reading.
definitions:
 - RearrangesFamily: after the map h of states, each listed distinction reads what the listed distinction
   sigma of it read before, on one side or the other (flip).
 - heldAfter: what a rearrangement makes of a class. The class holds, on a distinction, what it held on the
   distinction that one read before.
 - holdScore: K1's form of a table between heldAfter of the class held and the class read.
 - KeepsTable: the table has the same entry on two distinctions and on the two they are rearranged from.
 - HoldScoreNull: a finite real combination of rearrangements whose scores add to 0 for every class held and
   every class read.
 - ExecutesAs: a closed word of the foundation's words runs as a map of raw possibilities: from each one it
   runs to the map's value and to nothing else.
not claimed: that a hold keeps the table; anything about words that are not holds; what a raw possibility
 holds as a class.
no structure, no class, no Prop-valued field.
-/
import Definitions.Def_APFPaper5_K1_MarkTable
import Definitions.Def_APFB02_HoldOnDistinctions
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper5.K1 APFPaper1.Continuation

namespace APFPaper5.K2

universe uI uX uD uK uC uF uW
variable {ι : Type uI}

/-- After the map `h` of states, each listed distinction reads what the listed distinction `sigma` of it read
before `h`, on one side or the other. -/
def RearrangesFamily {X : Type uX} {D : Type uD} (reads : D → X → Bool) (dist : ι → D) (h : X → X)
    (sigma : ι → ι) (flip : ι → Bool) : Prop :=
  ∀ (i : ι) (x : X), reads (dist i) (h x) = xor (flip i) (reads (dist (sigma i)) x)

/-- What a rearrangement makes of a class: on a distinction it holds what was held on the distinction that
one read before. -/
def heldAfter (sigma : ι → ι) (x : ι → ℝ) : ι → ℝ := fun d => x (sigma d)

/-- The score with a hold in the channel: K1's form of the table between what the hold makes of the class
held and the class read. -/
def holdScore [Fintype ι] (G : ι → ι → ℝ) (sigma : ι → ι) (x y : ι → ℝ) : ℝ :=
  tableForm G (heldAfter sigma x) y

/-- The table has the same entry on two distinctions and on the two they are rearranged from. -/
def KeepsTable (G : ι → ι → ℝ) (sigma : ι → ι) : Prop :=
  ∀ a b : ι, G (sigma a) (sigma b) = G a b

/-- A finite real combination of rearrangements that no score can see. -/
def HoldScoreNull [Fintype ι] {κ : Type uK} [Fintype κ] (G : ι → ι → ℝ) (coef : κ → ℝ)
    (sigma : κ → ι → ι) : Prop :=
  ∀ x y : ι → ℝ, ∑ k, coef k * holdScore G (sigma k) x y = 0

/-- The closed word runs as the map `h` of raw possibilities: from each raw possibility it runs to `h` of it
and to nothing else. -/
def ExecutesAs {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uW}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context}
    (W : Word Frag a a) (h : Raw a → Raw a) : Prop :=
  ∀ x y : Raw a, Executes step W x y ↔ y = h x

end APFPaper5.K2


