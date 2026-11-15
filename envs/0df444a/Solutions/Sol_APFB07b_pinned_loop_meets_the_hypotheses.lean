-- Prove2me | solution 1 for APFB07b.pinned_loop_meets_the_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:14:52.494049+00:00
-- url     : https://prove2.me/submissions/48dc32af-7c59-4725-adde-4546a8f3554f

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB07_pinned_loop_witness
title: A supplied instance in which the hypotheses of the retracing theorem hold together: four moments, the two ends pinned, cost the sum of squares
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Thm_APFB07_realized_history_retraces. FOUNDATION_INPUTS B07a, B07b in declared form.
consumes_inputs: A2 and BW in declared form, on a supplied instance. It certifies nothing physical.
statement: (APFB07b.pinned_loop_meets_the_hypotheses) histories over four moments, admissible when they
 read 1 at moment 0 and -1 at moment 2, with total cost the sum of the squares of the readings. The history
 1, 0, -1, 0 is the unique minimum; the mirror of an admissible history is admissible; and the realized
 history reads differently two steps on from moment 0.
reading: the hypotheses of APFB07b.realized_history_retraces_of_sum_cost and the motion hypothesis are
 jointly satisfiable, so that theorem is not empty.
not_claimed: that any interface is this instance.
-/
import Theorems.Thm_APFB07b_realized_history_retraces_of_sum_cost
import Theorems.Thm_APFB07b_rate_is_held_on_realized_history
import Theorems.Thm_APFB07b_one_way_history_meets_A2_BW
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem APFB07b.pinned_loop_meets_the_hypotheses :
    ∃ (originalAdmissible : Unit → (Fin 4 → ℝ) → Prop) (totalCost : Unit → (Fin 4 → ℝ) → ℝ)
      (realized : Unit → (Fin 4 → ℝ)),
      APFB07a.A2Selection originalAdmissible totalCost realized ∧
        APFB07b.BWUniqueMinimum originalAdmissible totalCost ∧
        (∀ r, totalCost () r = ∑ t, r t * r t) ∧
        (∀ r, originalAdmissible () r → originalAdmissible () (fun t => r (-t))) ∧
        realized () (0 + 1 + 1) ≠ realized () 0 := by
  have cases4 : ∀ t : Fin 4, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by decide
  have d10 : (1 : Fin 4) ≠ 0 := by decide
  have d12 : (1 : Fin 4) ≠ 2 := by decide
  have d20 : (2 : Fin 4) ≠ 0 := by decide
  have d30 : (3 : Fin 4) ≠ 0 := by decide
  have d32 : (3 : Fin 4) ≠ 2 := by decide
  obtain ⟨f, f0, f1, f2, f3⟩ : ∃ f : Fin 4 → ℝ, f 0 = 1 ∧ f 1 = 0 ∧ f 2 = -1 ∧ f 3 = 0 :=
    ⟨fun t => if t = 0 then 1 else if t = 2 then -1 else 0, if_pos rfl,
      (if_neg d10).trans (if_neg d12), (if_neg d20).trans (if_pos rfl),
      (if_neg d30).trans (if_neg d32)⟩
  have hcost : ∀ r : Fin 4 → ℝ, ∑ t, r t * r t = r 0 * r 0 + r 1 * r 1 + r 2 * r 2 + r 3 * r 3 :=
    fun r => Fin.sum_univ_four _
  have hmin : ∀ G : Fin 4 → ℝ, G 0 = 1 → G 2 = -1 →
      (2 : ℝ) ≤ G 0 * G 0 + G 1 * G 1 + G 2 * G 2 + G 3 * G 3 := by
    intro G h0 h2
    rw [h0, h2]
    nlinarith [mul_self_nonneg (G 1), mul_self_nonneg (G 3)]
  have hreal : ∑ t, f t * f t = 2 := by
    rw [hcost f, f0, f1, f2, f3]
    norm_num
  refine ⟨fun _ r => r 0 = 1 ∧ r 2 = -1, fun _ r => ∑ t, r t * r t, fun _ => f, ?_, ?_,
    fun r => rfl, ?_, ?_⟩
  · intro i
    refine ⟨⟨f0, f2⟩, fun G hG => ?_⟩
    show ∑ t, f t * f t ≤ ∑ t, G t * G t
    rw [hreal, hcost G]
    exact hmin G hG.1 hG.2
  · intro i
    refine ⟨f, ⟨⟨f0, f2⟩, fun G hG => ?_⟩, fun H hH => ?_⟩
    · show ∑ t, f t * f t ≤ ∑ t, G t * G t
      rw [hreal, hcost G]
      exact hmin G hG.1 hG.2
    · obtain ⟨⟨h0, h2⟩, hle⟩ := hH
      have t : ∑ u, H u * H u ≤ ∑ u, f u * f u := hle f ⟨f0, f2⟩
      rw [hreal, hcost H, h0, h2] at t
      have s1 : H 1 * H 1 + H 3 * H 3 = 0 := by
        nlinarith [mul_self_nonneg (H 1), mul_self_nonneg (H 3)]
      obtain ⟨z1, z3⟩ := (mul_self_add_mul_self_eq_zero).mp s1
      funext u
      rcases cases4 u with rfl | rfl | rfl | rfl
      · rw [h0, f0]
      · rw [z1, f1]
      · rw [h2, f2]
      · rw [z3, f3]
  · intro r hr
    have e0 : (-0 : Fin 4) = 0 := by decide
    have e2 : (-2 : Fin 4) = 2 := by decide
    exact ⟨by show r (-0) = 1; rw [e0]; exact hr.1, by show r (-2) = -1; rw [e2]; exact hr.2⟩
  · have e : (0 + 1 + 1 : Fin 4) = 2 := by decide
    show f (0 + 1 + 1) ≠ f 0
    rw [e, f2, f0]
    norm_num


theorem solution :
@Exists.{1} (Unit → (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real) → Prop)
  fun (originalAdmissible : Unit → (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real) → Prop) =>
  @Exists.{1} (Unit → (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real) → Real)
    fun (totalCost : Unit → (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real) → Real) =>
    @Exists.{1} (Unit → Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
      fun (realized : Unit → Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real) =>
      And
        (@APFB07a.A2Selection.{0, 0} Unit
          (fun (i : Unit) => Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          originalAdmissible totalCost realized)
        (And
          (@APFB07b.BWUniqueMinimum.{0, 0} Unit
            (fun (i : Unit) => Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            originalAdmissible totalCost)
          (And
            (∀ (r : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real),
              @Eq.{1} Real (totalCost Unit.unit r)
                (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                  Real.instAddCommMonoid
                  (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                  fun (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (r t) (r t)))
            (And
              (∀ (r : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real),
                originalAdmissible Unit.unit r →
                  originalAdmissible Unit.unit
                    fun (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                    r
                      (@Neg.neg.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (Fin.neg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) t))
              (@Ne.{1} Real
                (realized Unit.unit
                  (@HAdd.hAdd.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@instHAdd.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@Fin.instAdd (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                    (@HAdd.hAdd.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@instHAdd.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@Fin.instAdd (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 0)))
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 1))))
                    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
                      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (nat_lit 1)))))
                (realized Unit.unit
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (nat_lit 0)))))))) := by
  exact @APFB07b.pinned_loop_meets_the_hypotheses
