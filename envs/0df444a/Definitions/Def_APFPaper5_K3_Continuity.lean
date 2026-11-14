-- Prove2me | Definitions.Def_APFPaper5_K3_Continuity
-- name    : APFPaper5_K3_Continuity
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:10:17.166554+00:00
-- url     : https://prove2.me/theorems/ef42a9ab-df5b-4e09-a9b5-1df63dc335a6
-- title:
--   Conditional interval range, reachability, and reversible-turn predicates
-- statement:
--   Defines RangesOverInterval, TurnsReach, TurnsLoseNothing and their conjunction Continuity.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   **Claim boundaries.** K3-03
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_Continuity.lean; Sib v15, SHA-256 70739abde52e4a2f1ec6adb5747a92f06350257227d202ddc4c6277442a9ecae. P5:1686-1717;3049-3056

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_Continuity
title: The continuity hypothesis: the relation number ranges over an interval, and turns reach it and lose nothing
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author's ruling of 2026-11-12 ("1and2 are adopted"), adopting: "the number in a relation ranges over an
 interval, and a turn that changes it is admissible and loses nothing". Paper 5 Supplement v7.33:3049-3058 (K3).
standing: a NAMED HYPOTHESIS of the K layer. It is not a declared input and no declared input produces it. A
 derivation is owed. The set Adm of admissible turns is supplied here; its identification with ledger
 admissibility is not made in this module.
reading: "ranges over an interval" is read as: every value from lo to hi is taken by some held state, with
 lo < hi. "A turn that changes it is admissible" is read as: from every held state an admissible turn reaches
 every value in the interval. "Loses nothing" is read as: every admissible turn is undone by an admissible turn.
statement: RangesOverInterval, TurnsReach, TurnsLoseNothing, and their conjunction Continuity.
-/
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper5.K3

universe u
variable {S : Type u}

/-- Every value from `lo` to `hi` is the relation number of some held state, and `lo < hi`. -/
def RangesOverInterval (rel : S → ℝ) (lo hi : ℝ) : Prop :=
  lo < hi ∧ ∀ t : ℝ, lo ≤ t → t ≤ hi → ∃ s : S, rel s = t

/-- From every held state an admissible turn reaches every value from `lo` to `hi`. -/
def TurnsReach (rel : S → ℝ) (lo hi : ℝ) (Adm : Set (S → S)) : Prop :=
  ∀ s : S, ∀ t : ℝ, lo ≤ t → t ≤ hi → ∃ f ∈ Adm, rel (f s) = t

/-- Every admissible turn is undone by an admissible turn. -/
def TurnsLoseNothing (Adm : Set (S → S)) : Prop :=
  ∀ f ∈ Adm, ∃ g ∈ Adm, ∀ s : S, g (f s) = s

/-- The continuity hypothesis as adopted on 2026-11-12. -/
def Continuity (rel : S → ℝ) (lo hi : ℝ) (Adm : Set (S → S)) : Prop :=
  RangesOverInterval rel lo hi ∧ TurnsReach rel lo hi Adm ∧ TurnsLoseNothing Adm

end APFPaper5.K3


