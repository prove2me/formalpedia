-- Prove2me | solution 1 for APFB01.common_turn_changes_no_fact
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:28:01.787807+00:00
-- url     : https://prove2.me/submissions/8fa05970-d600-42ba-a98d-00ac1457b5ee

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB01_global_phase_kernel
title: On two held components, under B01, the common turn changes no physical fact
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:1808-1823, Global-phase kernel theorem ("the common held orientation is
 faithful in Held but is killed by the record functor"). FOUNDATION_INPUTS B01 in its designated descent form.
 Thm_APFPaper5_K3_two_components (commonTurn_unseen); Thm_APFB01_unseen_turn.
consumes_inputs: B01, as the hypothesis that the fact in question descends to the quotient by record profile.
 CONDITIONAL INSTANCE in a supplied model whose continuation profile is its four records.
statement: (recordProfile_commonTurn) a common turn by a unit pair leaves the record profile unchanged.
 (APFB01.common_turn_changes_no_fact) so every fact that descends holds after the common turn exactly when it
 held before.
not_claimed: that the common turn is the identity on held states. It is not: it moves the state. This is the
 Supplement's point that the record functor is not faithful.
-/
import Definitions.Def_APFPaper5_K3_RecordProfile
import Theorems.Thm_APFPaper5_K3_commonTurn_unseen
import Theorems.Thm_APFPaper5_K3_records_are_cross_data
import Theorems.Thm_APFPaper5_K3_commonQuarter_commutes_common
import Theorems.Thm_APFPaper5_K3_same_records_give_common_turn
import Theorems.Thm_APFB01_unseen_turn_changes_no_fact

set_option autoImplicit false
open APFPaper5.K3

theorem APFPaper5.K3.recordProfile_commonTurn (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    recordProfile (commonTurn c s h) = recordProfile h := by
  obtain ⟨hA, hB, hS, hQ⟩ := commonTurn_unseen c s hcs h
  funext t
  unfold recordProfile
  rw [hA, hB, hS, hQ]

theorem APFB01.common_turn_changes_no_fact (c s : ℝ) (hcs : c * c + s * s = 1)
    (fact : Held2 → Prop) (hd : APFB01.Descends recordProfile fact) (h : Held2) :
    fact (commonTurn c s h) ↔ fact h :=
  APFB01.unseen_turn_changes_no_fact recordProfile (commonTurn c s)
    (recordProfile_commonTurn c s hcs) fact hd h


theorem solution :
∀ (c s : Real)
  (hcs :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c c)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s s))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (fact : APFPaper5.K3.Held2 → Prop)
  (hd :
    @APFB01.Descends.{0, 0} APFPaper5.K3.Held2 (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real)))
      APFPaper5.K3.recordProfile fact)
  (h : APFPaper5.K3.Held2), Iff (fact (APFPaper5.K3.commonTurn c s h)) (fact h) := by
  exact @APFB01.common_turn_changes_no_fact
