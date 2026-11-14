-- Prove2me | solution 1 for APFPaper5.K1.ledgerForm_posDef
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:40:03.946204+00:00
-- url     : https://prove2.me/submissions/b9c51eea-aae0-40a8-b500-decab59d43ff

/-
APF — conditional theorem for Paper 5 obligation K1. DRAFT for author and cold review. Not gated, not released, not
uploaded.
name: APFPaper5.K1.ledgerForm_of_ordered_score
title: Given the K1 hypotheses, the symmetric part of the exchanged score is a positive definite symmetric bilinear form whose diagonal is the score diagonal
inputs_revision: 2026-10-04.1 (consumes no declared input)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Technical Supplement v7.33:353-391 (theorem and proof), 312-334 (the alternating part is invisible
  on the diagonal).
statement: Under IsBilinear C: the ledger form is symmetric and real-bilinear; its diagonal equals C (theta x) x; the
  exchanged pairing is the sum of the ledger form and the orientation form; the orientation form is alternating; the
  diagonal satisfies the parallelogram identity. Under FaithfulNonnegDiagonal in addition: the ledger form is
  positive definite.
label: CONDITIONAL. Every hypothesis is a named predicate of APFPaper5_K1_OrderedScore and none is discharged from
  the declared inputs. Ordinary linear algebra.
observation recorded for the reviewer: no statement below uses that theta is invertible, and none uses
  IsNondegenerate. Only additivity and homogeneity of theta enter.
-/
import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1

variable {VP VE : Type*} [AddCommGroup VP] [Module ℝ VP] [AddCommGroup VE] [Module ℝ VE]

theorem ledgerForm_symm (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (x y : VP) :
    ledgerForm C theta x y = ledgerForm C theta y x := by
  unfold ledgerForm; ring

theorem ledgerForm_diag (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (x : VP) :
    ledgerForm C theta x x = C (theta x) x := by
  unfold ledgerForm; ring

theorem orientationForm_diag (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (x : VP) :
    orientationForm C theta x x = 0 := by
  unfold orientationForm; ring

theorem orientationForm_antisymm (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (x y : VP) :
    orientationForm C theta x y = - orientationForm C theta y x := by
  unfold orientationForm; ring

/-- The exchanged ordered pairing is its symmetric part plus its alternating part. -/
theorem exchanged_eq_ledger_add_orientation (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (x y : VP) :
    C (theta x) y = ledgerForm C theta x y + orientationForm C theta x y := by
  unfold ledgerForm orientationForm; ring

theorem ledgerForm_add_left (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (hC : IsBilinear C)
    (x y z : VP) : ledgerForm C theta (x + y) z = ledgerForm C theta x z + ledgerForm C theta y z := by
  obtain ⟨hl, _, hr, _⟩ := hC
  unfold ledgerForm
  rw [map_add, hl, hr]; ring

theorem ledgerForm_smul_left (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (hC : IsBilinear C)
    (r : ℝ) (x z : VP) : ledgerForm C theta (r • x) z = r * ledgerForm C theta x z := by
  obtain ⟨_, hl, _, hr⟩ := hC
  unfold ledgerForm
  rw [map_smul, hl, hr]; ring

/-- Positive definiteness of the ledger form is exactly the faithful nonnegative diagonal. -/
theorem ledgerForm_posDef (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE)
    (hq : FaithfulNonnegDiagonal C theta) (x : VP) :
    0 ≤ ledgerForm C theta x x ∧ (ledgerForm C theta x x = 0 → x = 0) := by
  rw [ledgerForm_diag]
  exact ⟨hq.1 x, hq.2 x⟩

/-- The diagonal satisfies the parallelogram identity. Derived from bilinearity, not assumed. -/
theorem diagonal_parallelogram (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (hC : IsBilinear C)
    (x y : VP) :
    C (theta (x + y)) (x + y) + C (theta (x - y)) (x - y) =
      2 * C (theta x) x + 2 * C (theta y) y := by
  obtain ⟨hl, hls, hr, hrs⟩ := hC
  have hneg : x - y = x + (-1 : ℝ) • y := by rw [neg_one_smul, sub_eq_add_neg]
  rw [hneg]
  simp only [map_add, map_smul, hl, hr, hls, hrs]
  ring

end APFPaper5.K1


universe apfNative_u_1 apfNative_u_2
theorem solution :
∀ {VP : Type apfNative_u_1} {VE : Type apfNative_u_2} [inst : AddCommGroup.{apfNative_u_1} VP]
  [inst_1 :
    @_root_.Module.{0, apfNative_u_1} Real VP Real.semiring (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} VP inst)]
  [inst_2 : AddCommGroup.{apfNative_u_2} VE]
  [inst_3 :
    @_root_.Module.{0, apfNative_u_2} Real VE Real.semiring (@AddCommGroup.toAddCommMonoid.{apfNative_u_2} VE inst_2)]
  (C : VE → VP → Real)
  (theta :
    @LinearEquiv.{0, 0, apfNative_u_1, apfNative_u_2} Real Real Real.semiring Real.semiring
      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
      (@RingHomInvPair.ids.{0} Real Real.semiring) (@RingHomInvPair.ids.{0} Real Real.semiring) VP VE
      (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} VP inst) (@AddCommGroup.toAddCommMonoid.{apfNative_u_2} VE inst_2)
      inst_1 inst_3)
  (hq : @APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u_1, apfNative_u_2} VP VE inst inst_1 inst_2 inst_3 C theta)
  (x : VP),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@APFPaper5.K1.ledgerForm.{apfNative_u_1, apfNative_u_2} VP VE inst inst_1 inst_2 inst_3 C theta x x))
    (@Eq.{1} Real (@APFPaper5.K1.ledgerForm.{apfNative_u_1, apfNative_u_2} VP VE inst inst_1 inst_2 inst_3 C theta x x)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @Eq.{apfNative_u_1 + 1} VP x
        (@OfNat.ofNat.{apfNative_u_1} VP (nat_lit 0)
          (@Zero.toOfNat0.{apfNative_u_1} VP
            (@NegZeroClass.toZero.{apfNative_u_1} VP
              (@SubNegZeroMonoid.toNegZeroClass.{apfNative_u_1} VP
                (@SubtractionMonoid.toSubNegZeroMonoid.{apfNative_u_1} VP
                  (@SubtractionCommMonoid.toSubtractionMonoid.{apfNative_u_1} VP
                    (@AddCommGroup.toDivisionAddCommMonoid.{apfNative_u_1} VP inst)))))))) := by
  exact @APFPaper5.K1.ledgerForm_posDef
