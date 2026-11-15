-- Prove2me | Definitions.Def_APFB02_EachTakesBothSides
-- name    : APFB02_EachTakesBothSides
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:03:53.726218+00:00
-- url     : https://prove2.me/theorems/f1ac7683-af19-4416-bbd7-e713785b1796
-- title:
--   Individual side extension and finite pattern realization
-- statement:
--   EachTakesBothSides specializes FreeWhereNovel to nonmembership in the finite family; EveryCombinationHeld realizes every finite Boolean assignment.
--
--   **Meaning and scope**
--
--   These are distinct predicates before the stated equivalence hypotheses: extension can be vacuous on empty X, whereas finite-pattern realization cannot.
--
--   **Status:** conditional reference mathematics. The supplied predicates and model assumptions are not additional Foundation inputs. These records do not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFB02_EachTakesBothSides.lean; Sib v52 / pullbacks v6; SHA-256 16ca832874fd9e2a8db28ebc777d2d1dd4fa08ad6f1baf1a7367990a52290b39. Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex; lines 1224-1243,1276-1332,1741-1771,1833-1885,2601-2680; APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-11-14.1; input B02; source/Definitions/Def_APFB02_EachTakesBothSides.lean

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFB02_EachTakesBothSides
title: A candidate clause without a condition: each distinction takes both sides, whatever sides the others are held on; and the statement that every combination of sides of every finite family is held
inputs_revision: 2026-11-14.1
revision_note: APFB02.EveryCombinationHeld, defined here, is the finite-set form of the sentence the author added
 to B02 at inputs revision 2026-11-14.1 (2026-11-14 03:11 and 06:10 HST). Where this header says the clause is a
 candidate or is not adopted, that was its standing before the install. EachTakesBothSides is an equivalent
 wording and is not itself the input.
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's statement of 2026-11-14 02:51 HST ("There are no new distinctions - each one fired out of
 the big bang"), on the candidate clause of pass 37. Def_APFB05_FreeWhereNovel. FOUNDATION_INPUTS B02 (a
 distinction takes both values), declared form unchanged.
standing: a CANDIDATE, typed so that it can be tested. It is not an input and not adopted. Only the author
 edits the inputs.
statement: the family is indexed by the distinctions themselves, one reading for each. EachTakesBothSides
 reads says: for every distinction d, every finite family S that does not contain d and every state x, some
 state holds the members of S on the sides x holds them and holds d on its true side, and another holds d on
 its false side. EveryCombinationHeld reads says: for every finite family and every assignment of sides to it,
 some state holds that assignment.
-/
import Definitions.Def_APFB05_FreeWhereNovel

set_option autoImplicit false
namespace APFB02

/-- Each distinction takes both sides, whatever sides the others are held on. -/
def EachTakesBothSides {X D : Type*} (reads : D → X → Bool) : Prop :=
  APFB05.FreeWhereNovel (fun (S : Finset D) (d : D) => d ∉ S) reads

/-- Every combination of sides of every finite family of the distinctions is held by some state. -/
def EveryCombinationHeld {X D : Type*} (reads : D → X → Bool) : Prop :=
  ∀ (S : Finset D) (v : D → Bool), ∃ x : X, ∀ e ∈ S, reads e x = v e

end APFB02


