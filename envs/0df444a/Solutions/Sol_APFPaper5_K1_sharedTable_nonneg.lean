-- Prove2me | solution 1 for APFPaper5.K1.sharedTable_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:16:30.773542+00:00
-- url     : https://prove2.me/submissions/0ecc0a8a-d0ac-4270-b6b3-06384bbdd8f3

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_shared_count
title: Counting shared distinctions gives a symmetric, positive score with no weights supplied
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K1_SharedCount.
consumes_inputs: none as a hypothesis. The only data are finitely many held families of distinctions.
statement: (sharedTable_symm) the shared-count table is symmetric. (sharedTable_nonneg) its form is nonnegative.
 (sharedTable_satisfies_K1) if every family holds a distinction that no other listed family holds, the typed K1
 hypotheses hold on coefficient vectors with the identity as role exchange.
not_claimed: that the physical score is this count; any value strictly between 0 and 1 between two single
 distinctions (two different single distinctions share none); anything off the record-book side; continuity.
-/
import Definitions.Def_APFPaper5_K1_SharedCount
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1

set_option autoImplicit false
namespace APFPaper5.K1

universe u v
variable {ι : Type u} [Fintype ι] {D : Type v} [Fintype D] [DecidableEq D]

omit [Fintype ι] in
theorem sharedTable_symm (fam : ι → Finset D) (i j : ι) :
    sharedTable fam i j = sharedTable fam j i :=
  atomTable_symm _ _ i j

theorem sharedTable_nonneg (fam : ι → Finset D) (x : ι → ℝ) :
    0 ≤ tableForm (sharedTable fam) x x :=
  atomTable_nonneg _ (fun _ => zero_le_one) _ x

theorem sharedTable_satisfies_K1 [DecidableEq ι] (fam : ι → Finset D)
    (hprivate : ∀ i, ∃ d : D, ∀ j, decide (d ∈ fam j) = decide (j = i)) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (sharedTable fam)) ∧
      FaithfulNonnegDiagonal (tableForm (sharedTable fam)) (LinearEquiv.refl ℝ (ι → ℝ)) :=
  record_book_table_satisfies_K1 _ (fun _ => zero_le_one) _
    (fun i => by
      obtain ⟨d, hd⟩ := hprivate i
      exact ⟨d, zero_lt_one, hd⟩)

end APFPaper5.K1


universe apfNative_u apfNative_v
theorem solution :
∀ {ι : Type apfNative_u} [inst : Fintype.{apfNative_u} ι] {D : Type apfNative_v} [inst_1 : Fintype.{apfNative_v} D]
  [inst_2 : DecidableEq.{apfNative_v + 1} D] (fam : ι → Finset.{apfNative_v} D) (x : ι → Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@APFPaper5.K1.tableForm.{apfNative_u} ι inst
      (@APFPaper5.K1.sharedTable.{apfNative_u, apfNative_v} ι D inst_1 inst_2 fam) x x) := by
  exact @APFPaper5.K1.sharedTable_nonneg
