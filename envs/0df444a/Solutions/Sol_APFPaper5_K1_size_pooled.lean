-- Prove2me | solution 1 for APFPaper5.K1.size_pooled
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:46:33.110289+00:00
-- url     : https://prove2.me/submissions/d68d35f0-27e5-4e2f-a46c-97dd418a77c1

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_pooled_counts
title: Counts over pooled runs add
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:3037-3041 (K1, the completed ordered score), read as a count over runs.
consumes_inputs: none. A list of runs and a pass/fail reading of each run are supplied data.
statement: (passes_pooled) the number of passing runs in two pooled lists of runs is the sum of the two
 numbers. (size_pooled) the same for the number of runs.
not_claimed: that any preparation has a stable pass frequency; that pooled lists represent a physical
 mixture; any real-number or limiting statement.
-/
set_option autoImplicit false
namespace APFPaper5.K1

universe u

theorem passes_pooled {Run : Type u} (passes : Run → Bool) (A B : List Run) :
    (A ++ B).countP passes = A.countP passes + B.countP passes :=
  List.countP_append

theorem size_pooled {Run : Type u} (A B : List Run) : (A ++ B).length = A.length + B.length :=
  List.length_append

end APFPaper5.K1


universe apfNative_u
theorem solution :
∀ {Run : Type apfNative_u} (A B : List.{apfNative_u} Run),
  @Eq.{1} Nat
    (@List.length.{apfNative_u} Run
      (@HAppend.hAppend.{apfNative_u, apfNative_u, apfNative_u} (List.{apfNative_u} Run) (List.{apfNative_u} Run)
        (List.{apfNative_u} Run)
        (@instHAppendOfAppend.{apfNative_u} (List.{apfNative_u} Run) (@List.instAppend.{apfNative_u} Run)) A B))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{apfNative_u} Run A)
      (@List.length.{apfNative_u} Run B)) := by
  exact @APFPaper5.K1.size_pooled
