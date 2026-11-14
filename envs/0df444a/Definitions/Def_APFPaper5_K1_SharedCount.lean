-- Prove2me | Definitions.Def_APFPaper5_K1_SharedCount
-- name    : APFPaper5_K1_SharedCount
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:09:34.585487+00:00
-- url     : https://prove2.me/theorems/50e64a82-d896-4ab6-8623-e21af05541b0
-- title:
--   The author-chosen shared-distinction count score
-- statement:
--   Defines sharedTable as the unit-weight Boolean overlap table of finite held families. The author chose this score on the record-book side; that choice is not derived from the declared inputs.
--
--   **Representation and scope.** Matches the author’s explicit record-side definition; it is an unnormalized count, not a turn probability or generic algebraic PairNumbers table.
--
--   **Supplied data or hypotheses.** Finite distinction type, decidable membership and supplied finite families.
--
--   **Claim boundaries.** Off-record score identification and continuity remain separate.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_SharedCount.lean; Sib v15, SHA-256 4d0ba80be4e1a40df36bbbaed4ba2fc45f2fefdf95af092e783aa90323522e9a. [{'path': 'Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_two_adoptions_2026-11-12.md', 'lines_or_section': 'adoption 1'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'lines_or_section': '3721-3749'}]

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_SharedCount
title: The score of two held families as their shared distinctions, each counted once
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author's remark of 2026-11-12, "Numbers are a count of distinctions".
standing: ADOPTED by the author on 2026-11-12 ("1and2 are adopted") as the K layer's score on the record-book
 side. It is a definition of a score from ledger objects: a choice, not a consequence of any input. Off the
 record-book side the identification of a score stays deferred (ruling 4 of the eight decisions).
statement: sharedTable fam i j is the atom table whose atoms are the distinctions, each with weight 1, and in
 which family i marks exactly the distinctions it holds. Read: the number of distinctions that families i and
 j both hold. The equality with the cardinality of the intersection is Thm_APFPaper5_K1_shared_count_card.
-/
import Definitions.Def_APFPaper5_K1_MarkTable

set_option autoImplicit false
namespace APFPaper5.K1

universe u v
variable {ι : Type u} {D : Type v} [Fintype D] [DecidableEq D]

/-- Unit weight on every distinction; family `i` marks the distinctions it holds. -/
def sharedTable (fam : ι → Finset D) : ι → ι → ℝ :=
  atomTable (fun _ : D => (1 : ℝ)) (fun i d => decide (d ∈ fam i))

end APFPaper5.K1


