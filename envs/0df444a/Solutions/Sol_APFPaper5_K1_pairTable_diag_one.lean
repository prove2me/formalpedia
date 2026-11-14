-- Prove2me | solution 1 for APFPaper5.K1.pairTable_diag_one
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:00:09.368068+00:00
-- url     : https://prove2.me/submissions/8c21ed57-6c23-4970-868a-4f17dc01404d

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_pair_table_symm
title: Under the numbers hypothesis the table of pair numbers is symmetric and has unit diagonal
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Thm_APFPaper1_pair_number_symm; Paper 5 Supplement v7.33:3037-3040 (K1). Author's ruling of
 2026-11-12 retiring symmetry as a separate hypothesis.
consumes_inputs: none. CONDITIONAL on the named hypothesis PairNumbers.
statement: (pairNumbers_symm) under PairNumbers for nonzero marks, c i j = c j i. (pairTable_form_symm) so the
 form of the table is unchanged when its two arguments are exchanged. (pairTable_diag_one) for repeatable
 marks every diagonal entry is 1.
not_claimed: that PairNumbers holds at any interface; that the form is nonnegative or faithful; that the
 numbers lie from 0 to 1; the boundary-role isomorphism as a map; K1.
-/
import Definitions.Def_APFPaper5_K1_PairNumbers
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Theorems.Thm_APFPaper1_RecordBook_pair_number_symm
import Theorems.Thm_APFPaper1_RecordBook_pair_table_symm
import Theorems.Thm_APFPaper1_RecordBook_pair_number_self

set_option autoImplicit false
namespace APFPaper5.K1

universe u uA
variable {ι : Type u} [Fintype ι] {A : Type uA} [Ring A] [Algebra ℝ A]

omit [Fintype ι] in
theorem pairNumbers_symm (p : ι → A) (c : ι → ι → ℝ) (hp0 : ∀ i, p i ≠ 0)
    (h : PairNumbers p c) : ∀ i j, c i j = c j i :=
  APFPaper1.RecordBook.pair_table_symm p c hp0 h

theorem pairTable_form_symm (p : ι → A) (c : ι → ι → ℝ) (hp0 : ∀ i, p i ≠ 0)
    (h : PairNumbers p c) (x y : ι → ℝ) : tableForm c x y = tableForm c y x :=
  tableForm_symm c (pairNumbers_symm p c hp0 h) x y

omit [Fintype ι] in
theorem pairTable_diag_one (p : ι → A) (c : ι → ι → ℝ) (hp0 : ∀ i, p i ≠ 0)
    (hidem : ∀ i, p i * p i = p i) (h : PairNumbers p c) : ∀ i, c i i = 1 :=
  fun i => APFPaper1.RecordBook.pair_number_self (p i) (c i i) (hp0 i) (hidem i) (h i i)

end APFPaper5.K1


universe apfNative_u apfNative_uA
theorem solution :
∀ {ι : Type apfNative_u} {A : Type apfNative_uA} [inst : Ring.{apfNative_uA} A]
  [inst_1 : @Algebra.{0, apfNative_uA} Real A Real.instCommSemiring (@Ring.toSemiring.{apfNative_uA} A inst)]
  (p : ι → A) (c : ι → ι → Real)
  (hp0 :
    ∀ (i : ι),
      @Ne.{apfNative_uA + 1} A (p i)
        (@OfNat.ofNat.{apfNative_uA} A (nat_lit 0)
          (@Zero.toOfNat0.{apfNative_uA} A
            (@MulZeroClass.toZero.{apfNative_uA} A
              (@instMulZeroClassOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))))
  (hidem :
    ∀ (i : ι),
      @Eq.{apfNative_uA + 1} A
        (@HMul.hMul.{apfNative_uA, apfNative_uA, apfNative_uA} A A A
          (@instHMul.{apfNative_uA} A
            (@Distrib.toMul.{apfNative_uA} A
              (@instDistribOfSemiring.{apfNative_uA} A (@Ring.toSemiring.{apfNative_uA} A inst))))
          (p i) (p i))
        (p i))
  (h : @APFPaper5.K1.PairNumbers.{apfNative_u, apfNative_uA} ι A inst inst_1 p c) (i : ι),
  @Eq.{1} Real (c i i) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) := by
  exact @APFPaper5.K1.pairTable_diag_one
