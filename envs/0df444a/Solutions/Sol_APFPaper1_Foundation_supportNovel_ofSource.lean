-- Prove2me | solution 1 for APFPaper1.Foundation.supportNovel_ofSource
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:22:34.707045+00:00
-- url     : https://prove2.me/submissions/f813e394-8a12-4133-9f86-f15f1ecf957c

import Definitions.Def_APFPaper1_CostLedger
import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APFPaper1_LedgerOfSource
import Definitions.Def_APFPaper1_SupportNovel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.NNReal.Basic
import Theorems.Thm_APFPaper1_Foundation_cost_ofSource
set_option autoImplicit false
open Classical
open APFPaper1.Source

/-
APF Foundation Ledger — theorem node (Batch 1, bridge)
name: APFPaper1.Foundation.cost_ofSource
title: The infimal cost of the source ledger is the family cost
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.27:1754-1757,1778-1787,2880-2883 (null-bill convention as hypothesis hnull).
statement: If the designated null protocol's calibrated whole resource is zero, then for every finite family S
  the CostLedger infimal cost of Ledger.ofSource … equals familyCost … S. The cost sets coincide, so no
  feasibility hypothesis is needed.
-/
set_option autoImplicit false
open Classical

namespace APFPaper1.Foundation

theorem price_ofSource {D P R Record : Type*} (p0 : P)
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop)
    (hnull : calibration (wholeResource p0) = 0) (p : P) :
    (Ledger.ofSource p0 wholeResource calibration maintained sufficient usesToRealize).price p =
      (calibration (wholeResource p) : ℝ) := by
  unfold Ledger.price Ledger.ofSource billFromNonNull
  by_cases h : p = p0
  · subst h; simp [hnull]
  · simp [h]



end APFPaper1.Foundation

open APFPaper1.Foundation in
theorem solution {D P R Record : Type*} (p0 : P)
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop)
    (hnull : calibration (wholeResource p0) = 0) (S : Finset D) (d : D) :
    SupportNovel (Ledger.ofSource p0 wholeResource calibration maintained sufficient usesToRealize) S d ↔
      APFPaper1.Source.supportNovel wholeResource calibration maintained sufficient usesToRealize S d := by
  unfold SupportNovel APFPaper1.Source.supportNovel
  simp only [price_ofSource p0 wholeResource calibration maintained sufficient usesToRealize hnull,
    cost_ofSource p0 wholeResource calibration maintained sufficient usesToRealize hnull]
  rfl
