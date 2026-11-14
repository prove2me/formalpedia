-- Prove2me | Definitions.Def_APFPaper5_K3_AmplitudePair
-- name    : APFPaper5_K3_AmplitudePair
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:09:36.425654+00:00
-- url     : https://prove2.me/theorems/acaf2181-f1e0-489e-88c5-670a3e2d04f0
-- title:
--   Real-pair multiplication and doubling
-- statement:
--   Defines pairMul and double by the real arithmetic of planar rotations.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_AmplitudePair.lean; Sib v15, SHA-256 dabceb87ec9b9bedb577648e357284219637e774e04ac3fca54ef31eb174c510. P5:1686-1717

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_AmplitudePair
title: Pairs composed as turns compose, and the double of a pair
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Thm_APFPaper5_K3_two_mark_turn (turn_compose). Ordinary mathematics.
standing: DEFINITIONS in pure arithmetic. Nothing here is ledger data.
statement: pairMul p q is the pair of the turn by p followed by the turn by q. double p is p composed with
 itself: the pair (p.1 * p.1 - p.2 * p.2, p.1 * p.2 + p.2 * p.1).
-/
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper5.K3

/-- Two pairs composed as turns compose. -/
def pairMul (p q : ℝ × ℝ) : ℝ × ℝ := (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

/-- A pair composed with itself. -/
def double (p : ℝ × ℝ) : ℝ × ℝ := pairMul p p

end APFPaper5.K3


