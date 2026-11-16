-- Prove2me | Definitions.Def_APFPaper5_K3_ReadingInvariance
-- name    : APFPaper5_K3_ReadingInvariance
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:46:31.979806+00:00
-- url     : https://prove2.me/theorems/96eb444f-7b99-4f2a-9fde-19035c23d65a
-- title:
--   Move-as-reading and invariance of admission: two test conditions
-- statement:
--   Defines a relation being the graph of a reading map where admitted, and preservation of admitted edges under that map. Both are contributor-named conditions for a test. Neither is an installed input nor an adopted claim that physical moves are re-readings.
--
--   **Supplied data and hypotheses**
--
--   - Both are contributor-named conditions for a test. Neither is an installed input nor an adopted claim that physical moves are re-readings.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFPaper5_K3_ReadingInvariance; Sib v66 / pullbacks v22, SHA-256 6f7777ae9ecd5fd6be54ef476926dd405e25168c887d68d2f35442b4537a2a17. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Definitions\Def_APFPaper5_K3_ReadingInvariance.lean

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K3_ReadingInvariance
title: A move that is a re-reading of the place, and admission that does not depend on the reading
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's "Proceed" of 2026-11-14 17:01 HST, on this seat's proposal to test whether the ruling of
 2026-11-13 23:32 HST ("reading is an action, a distinction is a thing. Taking a different action does not
 change the thing", RULING_reading_is_an_action) gives the condition that a move can be taken again from
 where it lands. FOUNDATION_INPUTS is not consumed.
standing: CONDITIONS named by this seat for a test. Neither is a ruling, a reading the author has adopted,
 or an input.
reading: a place is where the occupant can be. `sigma` is a re-reading of places: the same situation, read
 another way. MoveIsReading says the move takes each place to that place re-read. AdmittedUnderReading says
 a move admitted between two places is admitted between the same two places re-read.
statement: MoveIsReading, AdmittedUnderReading.
-/
set_option autoImplicit false
namespace APFPaper5.K3

universe u

/-- The move is a re-reading: it takes each place where it is admitted to that place read another way. -/
def MoveIsReading {N : Type u} (mv : N → N → Prop) (sigma : N → N) : Prop :=
  ∀ a b : N, mv a b → b = sigma a

/-- What is admitted does not depend on the reading: a move admitted between two places is admitted
between the same two places read the other way. -/
def AdmittedUnderReading {N : Type u} (mv : N → N → Prop) (sigma : N → N) : Prop :=
  ∀ a b : N, mv a b → mv (sigma a) (sigma b)

end APFPaper5.K3


