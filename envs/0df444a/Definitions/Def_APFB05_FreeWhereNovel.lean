-- Prove2me | Definitions.Def_APFB05_FreeWhereNovel
-- name    : APFB05_FreeWhereNovel
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:01:48.235803+00:00
-- url     : https://prove2.me/theorems/8d6cdeca-9cd5-4802-bb4f-8e0ad3f5045c
-- title:
--   Conditional extension of a finite side pattern
-- statement:
--   FreeWhereNovel requires a novel distinction to take both sides while preserving the existing finite readings at each starting state.
--
--   **Meaning and scope**
--
--   The novelty predicate is supplied. This conditioned candidate was never adopted; it is vacuous when X is empty and does not by itself supply a starting state.
--
--   **Status:** conditional reference mathematics. The supplied predicates and model assumptions are not additional Foundation inputs. These records do not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFB05_FreeWhereNovel.lean; Sib v52 / pullbacks v6; SHA-256 4b439f71168d5b30334875c20d5e5827ec002d0ac4c07478bdfba66a1563c6c7. Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex; lines 1224-1243,1276-1332,1741-1771,1833-1885,2601-2680; APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-11-14.1; input B02; source/Definitions/Def_APFB05_FreeWhereNovel.lean

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFB05_FreeWhereNovel
title: A candidate clause: a distinction that is new over a family takes both sides on every part marked out by the sides of that family
inputs_revision: 2026-11-14.1
revision_note: a candidate clause of pass 37, never adopted. Its condition was withdrawn on the author's
 statement of 2026-11-14 02:51 HST, and the unconditioned sentence is what entered B02 at inputs revision
 2026-11-14.1. Kept because APFB02.EachTakesBothSides is written with it.
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's question of 2026-11-14 02:38 HST ("Seems like the clause we add to B should be more
 primitive?"). FOUNDATION_INPUTS B02 (a distinction takes both values) and B05 (support novelty), declared
 forms unchanged.
standing: a CANDIDATE, typed so that it can be tested. It is not an input and not adopted. Only the author
 edits the inputs.
statement: FreeWhereNovel novel reads says: whenever d is new over the family S (novel S d), then for every
 state x there is a state that holds the members of S on the sides x holds them and holds d on its true side,
 and another that does the same and holds d on its false side. With S empty this is B02's own clause that a
 distinction takes both values.
-/
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
namespace APFB05

/-- A distinction that is new over a family takes both sides whatever sides the family is held on. -/
def FreeWhereNovel {X D : Type*} (novel : Finset D → D → Prop) (reads : D → X → Bool) : Prop :=
  ∀ (S : Finset D) (d : D), novel S d → ∀ x : X,
    (∃ y : X, (∀ e ∈ S, reads e y = reads e x) ∧ reads d y = true) ∧
    (∃ z : X, (∀ e ∈ S, reads e z = reads e x) ∧ reads d z = false)

end APFB05


