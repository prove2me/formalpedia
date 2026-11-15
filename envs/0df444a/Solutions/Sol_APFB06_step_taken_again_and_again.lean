-- Prove2me | solution 1 for APFB06.step_taken_again_and_again
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:15:26.699547+00:00
-- url     : https://prove2.me/submissions/da9d56d9-828e-4059-9296-cea3250c07f9

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB04_steps_again
title: A step can be taken again while the budget allows and A2 selects it: a step that adds to the bill can be repeated only so many times, a step that can be repeated without end adds nothing, and at the same interface the selected protocol is admitted again at every state that still holds the family
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's statement of 2026-11-13 16:27 HST ("The step - any step - can be taken again if the
 budget alows and it is selected by a2"). FOUNDATION_INPUTS B04 ("Each physical context has finite available
 capacity"), B07a. Thm_APFPaper5_K3_held_states_and_undo (kept_along_the_hold).
consumes_inputs: none as a declared predicate. The capacity enters as a real number C, the bill of n repeats
 of a step as n times the step's bill, and A2 through the fact that the realized protocol depends only on
 the interface. Supplied bindings throughout.
statement: (repeats_bounded_by_budget) if n repeats of a step that bills b > 0 are in budget, n is at most
 C / b.
 (costly_step_stops) so past some number of repeats the budget does not allow it.
 (free_step_repeats) a step that bills nothing is in budget however often it is repeated.
 (endless_step_is_free) a step that is in budget however often it is repeated bills nothing.
 (APFB06.step_taken_again) hinst says: at a raw state whose object holds the family, the protocol A2 selects
 for the family is admitted if the budget allows. Then at the state after a step, if the family is still
 held and the budget allows, the selected protocol is admitted again.
 (APFB06.step_taken_again_and_again) and so at every state along the repeated step, as long as each step
 keeps the family and the budget allows at each state.
reading: "can be taken again" is not a separate assumption. It is A2 at the same interface, limited by B04.
 A hold, which draws nothing, can go on; a step that draws can be repeated only until the capacity is spent.
not_claimed: that the bill of a repeated step is the step's bill times the number of repeats (additivity is
 supplied); that a hold bills nothing (the reading that drawing nothing costs nothing is not typed); hinst;
 that a step keeps the family (the hold sentence).
-/
import Definitions.Def_APF_B06_DeclaredInput
import Theorems.Thm_APFPaper5_K3_undo_is_a_repeat
import Theorems.Thm_APFPaper5_K3_kept_along_the_hold
import Theorems.Thm_APFPaper5_K3_every_state_comes_to_return
import Theorems.Thm_APFPaper5_K3_occupant_settles
import Theorems.Thm_APFPaper5_K3_finite_of_separating_family
import Theorems.Thm_APFB01_every_object_comes_to_return
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper5.K3

theorem repeats_bounded_by_budget (b C : ℝ) (hb : 0 < b) (bill : ℕ → ℝ)
    (hadd : ∀ n : ℕ, bill n = n * b) (n : ℕ) (hn : bill n ≤ C) : (n : ℝ) ≤ C / b := by
  rw [hadd] at hn
  exact (le_div_iff₀ hb).mpr hn

theorem costly_step_stops (b C : ℝ) (hb : 0 < b) (bill : ℕ → ℝ)
    (hadd : ∀ n : ℕ, bill n = n * b) : ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ bill n ≤ C := by
  obtain ⟨N, hN⟩ := exists_nat_gt (C / b)
  refine ⟨N, fun n hn h => ?_⟩
  have h1 := repeats_bounded_by_budget b C hb bill hadd n h
  have h2 : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
  linarith

theorem free_step_repeats (C : ℝ) (hC : 0 ≤ C) (bill : ℕ → ℝ)
    (hadd : ∀ n : ℕ, bill n = n * 0) (n : ℕ) : bill n ≤ C := by
  rw [hadd, mul_zero]
  exact hC

theorem endless_step_is_free (b C : ℝ) (hb0 : 0 ≤ b) (bill : ℕ → ℝ)
    (hadd : ∀ n : ℕ, bill n = n * b) (hall : ∀ n : ℕ, bill n ≤ C) : b = 0 := by
  by_contra hne
  have hb : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hne)
  obtain ⟨N, hN⟩ := costly_step_stops b C hb bill hadd
  exact hN (N + 1) (Nat.lt_succ_self N) (hall (N + 1))

end APFPaper5.K3

theorem APFB06.step_taken_again {Raw FullProcess : Type*} (Cont : Raw → FullProcess → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (protocols : Set FullProcess)
    (realized : Finset (APFB06.Task Cont Dset) → {p // p ∈ protocols})
    (budgetAllows : Finset (APFB06.Task Cont Dset) → Raw → Prop)
    (hinst : ∀ (S : Finset (APFB06.Task Cont Dset)) (x : Raw),
      (∀ d ∈ S, d.val (APFB01.physicalClass Cont x) = true) → budgetAllows S x →
        Cont x (realized S).val)
    (after : Raw → FullProcess → Raw) (S : Finset (APFB06.Task Cont Dset)) (x : Raw)
    (u : FullProcess)
    (hkeep : ∀ d ∈ S, d.val (APFB01.physicalClass Cont (after x u)) = true)
    (hbudget : budgetAllows S (after x u)) : Cont (after x u) (realized S).val :=
  hinst S (after x u) hkeep hbudget

theorem APFB06.step_taken_again_and_again {Raw FullProcess : Type*}
    (Cont : Raw → FullProcess → Prop) (Dset : Set (APFB01.PhysicalState Cont → Bool))
    (protocols : Set FullProcess)
    (realized : Finset (APFB06.Task Cont Dset) → {p // p ∈ protocols})
    (budgetAllows : Finset (APFB06.Task Cont Dset) → Raw → Prop)
    (hinst : ∀ (S : Finset (APFB06.Task Cont Dset)) (x : Raw),
      (∀ d ∈ S, d.val (APFB01.physicalClass Cont x) = true) → budgetAllows S x →
        Cont x (realized S).val)
    (after : Raw → FullProcess → Raw) (S : Finset (APFB06.Task Cont Dset))
    (hkeepstep : ∀ y : Raw, (∀ d ∈ S, d.val (APFB01.physicalClass Cont y) = true) →
      ∀ d ∈ S, d.val (APFB01.physicalClass Cont (after y (realized S).val)) = true)
    (x : Raw) (hx : ∀ d ∈ S, d.val (APFB01.physicalClass Cont x) = true)
    (hbudget : ∀ n : ℕ, budgetAllows S ((fun y => after y (realized S).val)^[n] x)) (n : ℕ) :
    Cont ((fun y => after y (realized S).val)^[n] x) (realized S).val :=
  hinst S _ (APFPaper5.K3.kept_along_the_hold (fun y => after y (realized S).val)
    (fun y => ∀ d ∈ S, d.val (APFB01.physicalClass Cont y) = true) hkeepstep x hx n) (hbudget n)


universe apfNative_u_1 apfNative_u_2
theorem solution :
∀ {Raw : Type apfNative_u_1} {FullProcess : Type apfNative_u_2} (Cont : Raw → FullProcess → Prop)
  (Dset : Set.{apfNative_u_1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
  (protocols : Set.{apfNative_u_2} FullProcess)
  (realized :
    Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) →
      @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
        @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
          (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
  (budgetAllows :
    Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) → Raw → Prop)
  (hinst :
    ∀ (S : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)) (x : Raw),
      (∀ (d : @APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset),
          @Membership.mem.{apfNative_u_1, apfNative_u_1}
              (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
              (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1}
                (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
                (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
                (@Finset.instSetLike.{apfNative_u_1}
                  (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)))
              S d →
            @Eq.{1} Bool
              (@Subtype.val.{apfNative_u_1 + 1}
                (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool)
                (fun (d : @APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool) =>
                  @Membership.mem.{apfNative_u_1, apfNative_u_1}
                    (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool)
                    (Set.{apfNative_u_1}
                      (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                    (@Set.instMembership.{apfNative_u_1}
                      (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                    Dset d)
                d (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont x))
              Bool.true) →
        budgetAllows S x →
          Cont x
            (@Subtype.val.{apfNative_u_2 + 1} FullProcess
              (fun (p : FullProcess) =>
                @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                  (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
              (realized S)))
  (after : Raw → FullProcess → Raw)
  (S : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
  (hkeepstep :
    ∀ (y : Raw),
      (∀ (d : @APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset),
          @Membership.mem.{apfNative_u_1, apfNative_u_1}
              (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
              (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1}
                (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
                (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
                (@Finset.instSetLike.{apfNative_u_1}
                  (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)))
              S d →
            @Eq.{1} Bool
              (@Subtype.val.{apfNative_u_1 + 1}
                (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool)
                (fun (d : @APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool) =>
                  @Membership.mem.{apfNative_u_1, apfNative_u_1}
                    (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool)
                    (Set.{apfNative_u_1}
                      (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                    (@Set.instMembership.{apfNative_u_1}
                      (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                    Dset d)
                d (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont y))
              Bool.true) →
        ∀ (d : @APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset),
          @Membership.mem.{apfNative_u_1, apfNative_u_1}
              (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
              (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1}
                (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
                (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
                (@Finset.instSetLike.{apfNative_u_1}
                  (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)))
              S d →
            @Eq.{1} Bool
              (@Subtype.val.{apfNative_u_1 + 1}
                (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool)
                (fun (d : @APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool) =>
                  @Membership.mem.{apfNative_u_1, apfNative_u_1}
                    (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool)
                    (Set.{apfNative_u_1}
                      (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                    (@Set.instMembership.{apfNative_u_1}
                      (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                    Dset d)
                d
                (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
                  (after y
                    (@Subtype.val.{apfNative_u_2 + 1} FullProcess
                      (fun (p : FullProcess) =>
                        @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                          (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
                      (realized S)))))
              Bool.true)
  (x : Raw)
  (hx :
    ∀ (d : @APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset),
      @Membership.mem.{apfNative_u_1, apfNative_u_1}
          (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
          (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
          (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1}
            (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
            (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
            (@Finset.instSetLike.{apfNative_u_1}
              (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)))
          S d →
        @Eq.{1} Bool
          (@Subtype.val.{apfNative_u_1 + 1}
            (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool)
            (fun (d : @APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool) =>
              @Membership.mem.{apfNative_u_1, apfNative_u_1}
                (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool)
                (Set.{apfNative_u_1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                (@Set.instMembership.{apfNative_u_1}
                  (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                Dset d)
            d (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont x))
          Bool.true)
  (hbudget :
    ∀ (n : Nat),
      budgetAllows S
        (@Nat.iterate.{apfNative_u_1 + 1} Raw
          (fun (y : Raw) =>
            after y
              (@Subtype.val.{apfNative_u_2 + 1} FullProcess
                (fun (p : FullProcess) =>
                  @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                    (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
                (realized S)))
          n x))
  (n : Nat),
  Cont
    (@Nat.iterate.{apfNative_u_1 + 1} Raw
      (fun (y : Raw) =>
        after y
          (@Subtype.val.{apfNative_u_2 + 1} FullProcess
            (fun (p : FullProcess) =>
              @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
            (realized S)))
      n x)
    (@Subtype.val.{apfNative_u_2 + 1} FullProcess
      (fun (p : FullProcess) =>
        @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
          (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
      (realized S)) := by
  exact @APFB06.step_taken_again_and_again
