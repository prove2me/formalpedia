-- Prove2me | Definitions.Def_APF_B02_r2_clause_init_proposed
-- name    : APF_B02_r2_clause_init_proposed
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:01:45.575098+00:00
-- url     : https://prove2.me/theorems/ef87638d-8f36-4d54-81d6-a9e74a4fbdc8
-- title:
--   Finite side-assignment realization in list form
-- statement:
--   EveryCombinationHeldList requires each finite list and global assignment of Boolean sides to have a realizing state.
--
--   **Meaning and scope**
--
--   This is a predicate, not an independently adopted premise. Repetitions must share a side; the empty list enforces Nonempty X.
--
--   **Status:** conditional reference mathematics. The supplied predicates and model assumptions are not additional Foundation inputs. These records do not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APF_B02_r2_clause_init_proposed.lean; Sib v52 / pullbacks v6; SHA-256 ae1a68a72b06a1aae97cc7feed20cddb790d607eedfe77242f07264d7ed93d30. Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex; lines 1224-1243,1276-1332,1741-1771,1833-1885,2601-2680; APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-11-14.1; input B02; source/Definitions/Def_APF_B02_r2_clause_init_proposed.lean

/-
APF Foundation Ledger — definition node DRAFT, PROPOSED FORM ONLY (session EthanBrooke-01WrrBvu, 2026-11-14;
 not gated, not reviewed, not released, not a live node)
name: APF_B02_r2_clause_init_proposed
title: The sentence added to B02 at inputs revision 2026-11-14.1, written with lists so that it needs only Init
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-11-14.1; SHA-256
 c0fbd55c797afd5a342a5362ceb2cb79efb13186edd487205ef04c5eaa26ffbd; declared input B02, current_wording, second
 sentence: "Every combination of sides of every finite family of distinctions is held by some potential
 state."
standing: a PROPOSAL for the publishing seat and the author. The live declared form of B02
 (APFB02.B02SourceMeaning, node 2d6854de-b2dd-4db3-8be5-57bbbb64efb6) imports only Init; this form of the new
 sentence does too.
statement: EveryCombinationHeldList reads says: for every finite list of the distinctions and every assignment
 of a side to each distinction, some state holds each listed distinction on its assigned side. The assignment
 is made to distinctions, not to places in the list, so a distinction listed twice asks nothing more.
fidelity exposure: said of the domain as the distinctions themselves, each once. A reading made from
 distinctions, placed in the domain beside them, would make the sentence false.
-/
import Init

set_option autoImplicit false
universe uX uD
namespace APFB02

/-- Every combination of sides of every finite list of the distinctions is held by some state. -/
def EveryCombinationHeldList {X : Type uX} {D : Type uD} (reads : D → X → Bool) : Prop :=
  ∀ (l : List D) (v : D → Bool), ∃ x : X, ∀ e ∈ l, reads e x = v e

end APFB02


