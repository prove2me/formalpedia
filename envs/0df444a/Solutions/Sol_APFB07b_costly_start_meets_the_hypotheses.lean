-- Prove2me | solution 1 for APFB07b.costly_start_meets_the_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:17:53.719499+00:00
-- url     : https://prove2.me/submissions/6c3528dc-fa20-4304-810a-6665ba607a51

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB07_costly_start_witness
title: A supplied instance in which the hypotheses of the costly-start theorem hold together: three moments, the first held at 1, cost the sum of squares
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Thm_APFB07_moves. FOUNDATION_INPUTS B07a, B07b in declared form.
consumes_inputs: A2 and BW in declared form, on a supplied instance. It certifies nothing physical.
statement: (APFB07b.costly_start_meets_the_hypotheses) histories over three moments, admissible exactly when
 they read 1 at moment 0, with total cost the sum of the squares of the readings. A2 and BW hold with realized
 history 1, 0, 0. The record 0 is cheaper than the record 1. Two steps on from moment 0 is a different
 moment, the mirror fixes moment 0, and the mirror and the step fit together as the theorem asks.
reading: the A2, BW, cost and moment hypotheses of APFB07b.rate_is_held_after_a_costly_start are jointly
 satisfiable. The B01 hypotheses of that theorem are not instanced here.
not_claimed: that any interface is this instance.
-/
import Theorems.Thm_APFPaper5_K3_continuity_met_by_self_undoing_turns
import Theorems.Thm_APFB07a_realized_moves_off_a_costly_start
import Theorems.Thm_APFB07b_rate_is_held_after_a_costly_start
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem APFB07b.costly_start_meets_the_hypotheses :
    ∃ (originalAdmissible : Unit → (Fin 3 → ℝ) → Prop) (totalCost : Unit → (Fin 3 → ℝ) → ℝ)
      (realized : Unit → (Fin 3 → ℝ)),
      APFB07a.A2Selection originalAdmissible totalCost realized ∧
        APFB07b.BWUniqueMinimum originalAdmissible totalCost ∧
        (∀ r, totalCost () r = ∑ t, r t * r t) ∧
        (∀ r, originalAdmissible () r ↔ r 0 = 1) ∧
        (0 : ℝ) * 0 < 1 * 1 ∧ (0 + 1 + 1 : Fin 3) ≠ 0 ∧ (-0 : Fin 3) = 0 ∧
        ∀ t : Fin 3, -(t + 1) + 1 = -t := by
  have cases3 : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  have d10 : (1 : Fin 3) ≠ 0 := by decide
  have d20 : (2 : Fin 3) ≠ 0 := by decide
  obtain ⟨f, f0, f1, f2⟩ : ∃ f : Fin 3 → ℝ, f 0 = 1 ∧ f 1 = 0 ∧ f 2 = 0 :=
    ⟨fun t => if t = 0 then 1 else 0, if_pos rfl, if_neg d10, if_neg d20⟩
  have hcost : ∀ r : Fin 3 → ℝ, ∑ t, r t * r t = r 0 * r 0 + r 1 * r 1 + r 2 * r 2 :=
    fun r => Fin.sum_univ_three _
  have hmin : ∀ G : Fin 3 → ℝ, G 0 = 1 → (1 : ℝ) ≤ G 0 * G 0 + G 1 * G 1 + G 2 * G 2 := by
    intro G h0
    rw [h0]
    nlinarith [mul_self_nonneg (G 1), mul_self_nonneg (G 2)]
  have hreal : ∑ t, f t * f t = 1 := by
    rw [hcost f, f0, f1, f2]
    norm_num
  refine ⟨fun _ r => r 0 = 1, fun _ r => ∑ t, r t * r t, fun _ => f, ?_, ?_, fun r => rfl,
    fun r => Iff.rfl, by norm_num, by decide, by decide, by decide⟩
  · intro i
    refine ⟨f0, fun G hG => ?_⟩
    show ∑ t, f t * f t ≤ ∑ t, G t * G t
    rw [hreal, hcost G]
    exact hmin G hG
  · intro i
    refine ⟨f, ⟨f0, fun G hG => ?_⟩, fun H hH => ?_⟩
    · show ∑ t, f t * f t ≤ ∑ t, G t * G t
      rw [hreal, hcost G]
      exact hmin G hG
    · obtain ⟨h0, hle⟩ := hH
      have t : ∑ u, H u * H u ≤ ∑ u, f u * f u := hle f f0
      rw [hreal, hcost H, h0] at t
      have s1 : H 1 * H 1 + H 2 * H 2 = 0 := by
        nlinarith [mul_self_nonneg (H 1), mul_self_nonneg (H 2)]
      obtain ⟨z1, z2⟩ := (mul_self_add_mul_self_eq_zero).mp s1
      funext u
      rcases cases3 u with rfl | rfl | rfl
      · rw [h0, f0]
      · rw [z1, f1]
      · rw [z2, f2]


theorem solution :
@Exists.{1} (Unit → (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real) → Prop)
  fun (originalAdmissible : Unit → (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real) → Prop) =>
  @Exists.{1} (Unit → (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real) → Real)
    fun (totalCost : Unit → (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real) → Real) =>
    @Exists.{1} (Unit → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
      fun (realized : Unit → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real) =>
      And
        (@APFB07a.A2Selection.{0, 0} Unit
          (fun (i : Unit) => Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
          originalAdmissible totalCost realized)
        (And
          (@APFB07b.BWUniqueMinimum.{0, 0} Unit
            (fun (i : Unit) => Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
            originalAdmissible totalCost)
          (And
            (∀ (r : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real),
              @Eq.{1} Real (totalCost Unit.unit r)
                (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Real
                  Real.instAddCommMonoid
                  (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  fun (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (r t) (r t)))
            (And
              (∀ (r : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real),
                Iff (originalAdmissible Unit.unit r)
                  (@Eq.{1} Real
                    (r
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (nat_lit 0))))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                (And
                  (@Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@HAdd.hAdd.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@instHAdd.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@Fin.instAdd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (@HAdd.hAdd.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@instHAdd.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (@Fin.instAdd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (nat_lit 0)))
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 1)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (nat_lit 1))))
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (nat_lit 1))))
                    (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
                      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (nat_lit 0))))
                  (And
                    (@Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@Neg.neg.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (Fin.neg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (nat_lit 0))))
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (nat_lit 0))))
                    (∀ (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
                      @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@HAdd.hAdd.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (@instHAdd.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (@Fin.instAdd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@Neg.neg.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (Fin.neg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (@HAdd.hAdd.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (@instHAdd.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (@Fin.instAdd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              t
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 1)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 1)))))
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 1)
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (nat_lit 1))))
                        (@Neg.neg.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (Fin.neg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) t)))))))) := by
  exact @APFB07b.costly_start_meets_the_hypotheses
