-- Prove2me | solution 1 for APFPaper5.K1.sharedTable_satisfies_K1
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:17:07.5041+00:00
-- url     : https://prove2.me/submissions/d3d0ca12-ddde-4a38-98c0-185cd582ac74

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
  [inst_2 : DecidableEq.{apfNative_v + 1} D] [inst_3 : DecidableEq.{apfNative_u + 1} ι]
  (fam : ι → Finset.{apfNative_v} D)
  (hprivate :
    ∀ (i : ι),
      @Exists.{apfNative_v + 1} D fun (d : D) =>
        ∀ (j : ι),
          @Eq.{1} Bool
            (@Decidable.decide
              (@Membership.mem.{apfNative_v, apfNative_v} D (Finset.{apfNative_v} D)
                (@SetLike.instMembership.{apfNative_v, apfNative_v} (Finset.{apfNative_v} D) D
                  (@Finset.instSetLike.{apfNative_v} D))
                (fam j) d)
              (@Finset.decidableMem.{apfNative_v} D inst_2 d (fam j)))
            (@Decidable.decide (@Eq.{apfNative_u + 1} ι j i) (inst_3 j i))),
  And
    (@APFPaper5.K1.IsBilinear.{apfNative_u, apfNative_u} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u} ι inst
        (@APFPaper5.K1.sharedTable.{apfNative_u, apfNative_v} ι D inst_1 inst_2 fam)))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u, apfNative_u} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u} ι inst
        (@APFPaper5.K1.sharedTable.{apfNative_u, apfNative_v} ι D inst_1 inst_2 fam))
      (@LinearEquiv.refl.{0, apfNative_u} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by
  exact @APFPaper5.K1.sharedTable_satisfies_K1
