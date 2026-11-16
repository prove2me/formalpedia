-- Prove2me | Definitions.Def_APFPaper5_K3_UndoneWhereItLands
-- name    : APFPaper5_K3_UndoneWhereItLands
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:46:33.257344+00:00
-- url     : https://prove2.me/theorems/5aacd17a-8c75-45be-a60c-2274930ca35f
-- title:
--   Undoability at the landing place and conditions on a move relation
-- statement:
--   Defines undoability by reflexive transitive reachability, single outcome, no erasure and continuation from each landing place. An adopted interpretation of a named K-layer clause is not a Foundation input. The three auxiliary relation conditions are supplied predicates; existence of any move and global finiteness are not encoded by them.
--
--   **Supplied data and hypotheses**
--
--   - An adopted interpretation of a named K-layer clause is not a Foundation input. The three auxiliary relation conditions are supplied predicates; existence of any move and global finiteness are not encoded by them.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFPaper5_K3_UndoneWhereItLands; Sib v66 / pullbacks v22, SHA-256 35cf5fc9ddb01050fdbf098551710ed949776bed1c2778b2d19fa3deeeac2611. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Definitions\Def_APFPaper5_K3_UndoneWhereItLands.lean

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K3_UndoneWhereItLands
title: "Loses nothing" read across contexts: every admitted move is undone by admitted moves from where it lands; and the three conditions on a move
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's ruling of 2026-11-14 16:52 HST ("Yes, that's correct"), on the question "is that how you
 mean 'loses nothing': every admitted move can be undone from where it lands?"
 (RULING_loses_nothing_across_contexts_2026-11-14). The clause read is the third part of the continuity
 clause adopted 2026-11-12, first typed as APFPaper5.K3.TurnsLoseNothing. FOUNDATION_INPUTS is not consumed.
standing: UndoneWhereItLands is an ADOPTED READING of a named clause of the K layer. It is not a declared
 input and no declared input produces it. OneOutcome, ErasesNothing and GoesOn are conditions named by this
 seat for the theorem that derives the reading from them; they are not rulings.
reading: a place is where the occupant can be (a context with a state, or a state alone when there is one
 context). `mv u v` says an admitted move takes place u to place v. The undo may take several moves. It
 starts at v, where the move landed.
statement: UndoneWhereItLands, OneOutcome (where a move leads is fixed by where it starts), ErasesNothing
 (different places are taken to different places), GoesOn (the move can be taken again from where it lands).
-/
import Mathlib.Logic.Relation

set_option autoImplicit false
namespace APFPaper5.K3

universe u

/-- Every admitted move is undone by admitted moves from where it lands. -/
def UndoneWhereItLands {N : Type u} (mv : N → N → Prop) : Prop :=
  ∀ u v : N, mv u v → Relation.ReflTransGen mv v u

/-- Where a move leads is fixed by where it starts. -/
def OneOutcome {N : Type u} (mv : N → N → Prop) : Prop :=
  ∀ u v v' : N, mv u v → mv u v' → v = v'

/-- The move erases nothing: different places are taken to different places. -/
def ErasesNothing {N : Type u} (mv : N → N → Prop) : Prop :=
  ∀ u u' v : N, mv u v → mv u' v → u = u'

/-- The move can be taken again from where it lands. -/
def GoesOn {N : Type u} (mv : N → N → Prop) : Prop :=
  ∀ u v : N, mv u v → ∃ w : N, mv v w

end APFPaper5.K3


