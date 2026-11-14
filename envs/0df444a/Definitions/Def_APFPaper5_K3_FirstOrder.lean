-- Prove2me | Definitions.Def_APFPaper5_K3_FirstOrder
-- name    : APFPaper5_K3_FirstOrder
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:10:23.56571+00:00
-- url     : https://prove2.me/theorems/f65ebcc4-df83-4b90-80c8-5da04bd619ef
-- title:
--   Candidate cyclic-span closure condition for an iterated map
-- statement:
--   FirstOrder T z means that T(T z) is a real linear combination of z and T z.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   **Claim boundaries.** K3-04
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_FirstOrder.lean; Sib v15, SHA-256 c55f61d21a26b24796937e718dc289b094def1575d34a52313218d1987adb766. P5:1621-1649

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_FirstOrder
title: The first-order clause: the second turn of a combination is fixed by the combination and its first turn
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author's ruling of 2026-11-12 ("Yes yes yes"), naming the first-order clause. Paper 5 Supplement
 v7.33:1621-1647 (minimum complete first-order carrier) and its declared first-order regime.
standing: a NAMED HYPOTHESIS of the K layer. Not a declared input; a derivation is owed. Plain reading: a
 held relation is fixed by its present number and its rate.
statement: FirstOrder T z says that T (T z) is a real combination of z and T z.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Defs

set_option autoImplicit false
namespace APFPaper5.K3

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The second turn of `z` is a combination of `z` and its first turn. -/
def FirstOrder (T : V → V) (z : V) : Prop :=
  ∃ alpha beta : ℝ, T (T z) = alpha • z + beta • T z

end APFPaper5.K3


