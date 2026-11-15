-- Prove2me | Definitions.Def_APFB02_ToldApart
-- name    : APFB02_ToldApart
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T17:59:59.220888+00:00
-- url     : https://prove2.me/theorems/422a6627-baa1-4d28-a6a6-edf6a05d188e
-- title:
--   Candidate separation by the distinction family
-- statement:
--   ToldApart says equality of every distinction reading implies equality of continuation profiles.
--
--   **Meaning and scope**
--
--   Unadopted named predicate. It concludes continuation equality, not equality of arbitrary raw representatives. B01 quotient equality follows only with the correct original profile binding.
--
--   **Status:** conditional reference mathematics. The supplied predicates and model assumptions are not additional Foundation inputs. These records do not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFB02_ToldApart.lean; Sib v52 / pullbacks v6; SHA-256 b965aaaf22fd2484c4af4fb565c0f3e63d2e1592b784fc880854c989a24689c8. Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex; lines 1224-1243,1276-1332,1741-1771,1833-1885,2601-2680; APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-11-14.1; input B02; source/Definitions/Def_APFB02_ToldApart.lean

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFB02_ToldApart
title: The statement that a region's distinctions tell its states apart
inputs_revision: 2026-11-14.1
revision_note: a named clause on the author's statement of 2026-11-14 03:12 HST. It is NOT in the inputs at
 revision 2026-11-14.1.
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's statement of 2026-11-14 03:12 HST ("This is next - region's distinctions tell its states
 apart. It's true."). FOUNDATION_INPUTS B01 (a physical state is a class of raw states with one continuation
 profile) and B02 ("A distinction is a finite, enforceable separator of continuation profiles"), unchanged.
standing: a named clause of the K layer, typed so that it can be tested. It is not one of the eight declared
 inputs.
statement: ToldApart Cont reads says: two raw states that every distinction reads alike have the same
 continuation profile. By B01 they are then one physical state.
-/
import Mathlib.Logic.Basic

set_option autoImplicit false
namespace APFB02

/-- States that no distinction tells apart have the same continuation profile. -/
def ToldApart {X Q D : Type*} (Cont : X → Q → Prop) (reads : D → X → Bool) : Prop :=
  ∀ x y : X, (∀ d : D, reads d x = reads d y) → Cont x = Cont y

end APFB02


