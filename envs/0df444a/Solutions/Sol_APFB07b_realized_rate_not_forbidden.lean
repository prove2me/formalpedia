-- Prove2me | solution 1 for APFB07b.realized_rate_not_forbidden
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:06:51.951383+00:00
-- url     : https://prove2.me/submissions/0f0cf597-d9a2-4690-b5ae-337bfb75c3c2

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB07_realized_is_its_own_reverse
title: Under A2 and BW, a symmetry of an interface that keeps admissibility and total cost fixes the realized configuration; so a realized held state at an interface that does not tell the two senses apart has no rate
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B07a (A2, "Realization is the minimum-cost admissible configuration") and B07b (BW,
 with the author's clarification of 2026-10-05, "Unique minimum"), in their declared Lean forms
 APFB07a.A2Selection and APFB07b.BWUniqueMinimum, copied unchanged from the repository definitions.
consumes_inputs: A2 and BW in their declared forms. The formal fidelity of A2 is NOT CERTIFIED. The bindings
 of Interface, Configuration, originalAdmissible, totalCost and realized are source vocabulary; a freely
 supplied instance does not certify the physical statement. The last theorem is such an instance: it takes
 the configurations to be the held states of the supplied model.
statement: (APFB07b.minimum_of_equal_cost) an admissible configuration with the cost of a minimum is a
 minimum.
 (APFB07b.realized_fixed_by_cost_symmetry) if a map of the configurations at an interface keeps
 admissibility and total cost, it fixes the realized configuration.
 (rateFlip_fixes_iff_no_rate) a held state is its own reverse exactly when both its rates are zero.
 (APFB07b.realized_held_state_has_no_rate) if the configurations at every interface are held states, and
 reversing the rates keeps admissibility and total cost, the realized held state has both rates zero.
 (APFB07b.realized_has_no_rate_of_present_records) in particular if admissibility and total cost at every
 interface read only the present records.
 (APFB07b.realized_rate_not_forbidden) a supplied instance of the two declared forms in which the realized
 held state has a rate: one admissible configuration. It shows only that the two forms do not forbid one
 where admissibility tells the senses apart.
reading: two of the eight pull against a realized rate. A realized held state can carry one only at an
 interface whose admissibility or cost tells the two senses of turning apart.
not_claimed: that configurations are held states; that reversal keeps admissibility and cost at any
 interface; any K.
-/
import Definitions.Def_APF_B07a_DeclaredInput
import Definitions.Def_APF_B07b_DeclaredInput
import Theorems.Thm_APFPaper5_K3_rateFlip_keeps_plainNow
import Theorems.Thm_APFPaper5_K3_same_present_records_different_later
import Theorems.Thm_APFPaper5_K3_rateFree_present_records_fix_state
import Theorems.Thm_APFPaper5_K3_mix_has_no_reverse
import Theorems.Thm_APFB01_rate_is_held_on_the_carrier
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem APFB07b.minimum_of_equal_cost {Configuration : Type*}
    (originalAdmissible : Configuration → Prop) (totalCost : Configuration → ℝ)
    (G H : Configuration) (hG : APFB07b.IsMinimum originalAdmissible totalCost G)
    (hH : originalAdmissible H) (hc : totalCost H = totalCost G) :
    APFB07b.IsMinimum originalAdmissible totalCost H :=
  ⟨hH, fun K hK => by rw [hc]; exact hG.2 K hK⟩

theorem APFB07b.realized_fixed_by_cost_symmetry {Interface : Type*}
    {Configuration : Interface → Type*}
    (originalAdmissible : (i : Interface) → Configuration i → Prop)
    (totalCost : (i : Interface) → Configuration i → ℝ)
    (realized : (i : Interface) → Configuration i)
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost) (i : Interface)
    (theta : Configuration i → Configuration i)
    (hadm : ∀ G, originalAdmissible i G → originalAdmissible i (theta G))
    (hcost : ∀ G, totalCost i (theta G) = totalCost i G) :
    theta (realized i) = realized i := by
  obtain ⟨G0, _, huniq⟩ := hBW i
  have hr : APFB07b.IsMinimum (originalAdmissible i) (totalCost i) (realized i) := hA2 i
  have ht : APFB07b.IsMinimum (originalAdmissible i) (totalCost i) (theta (realized i)) :=
    APFB07b.minimum_of_equal_cost _ _ _ _ hr (hadm _ hr.1) (hcost _)
  rw [huniq _ ht, huniq _ hr]

namespace APFPaper5.K3

theorem rateFlip_fixes_iff_no_rate (h : Held2) : rateFlip h = h ↔ h.a2 = 0 ∧ h.b2 = 0 := by
  constructor
  · intro e
    have e2 := congrArg Held2.a2 e
    have e4 := congrArg Held2.b2 e
    dsimp only [rateFlip] at e2 e4
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h2, h4⟩
    apply Held2.ext
    · rfl
    · dsimp only [rateFlip]
      linarith
    · rfl
    · dsimp only [rateFlip]
      linarith

end APFPaper5.K3

open APFPaper5.K3 in
theorem APFB07b.realized_held_state_has_no_rate {Interface : Type*}
    (originalAdmissible : Interface → Held2 → Prop) (totalCost : Interface → Held2 → ℝ)
    (realized : Interface → Held2)
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost)
    (hadm : ∀ i h, originalAdmissible i h → originalAdmissible i (rateFlip h))
    (hcost : ∀ i h, totalCost i (rateFlip h) = totalCost i h) (i : Interface) :
    (realized i).a2 = 0 ∧ (realized i).b2 = 0 :=
  (rateFlip_fixes_iff_no_rate (realized i)).mp
    (APFB07b.realized_fixed_by_cost_symmetry originalAdmissible totalCost realized hA2 hBW i
      rateFlip (hadm i) (hcost i))

open APFPaper5.K3 in
theorem APFB07b.realized_has_no_rate_of_present_records {Interface : Type*}
    (originalAdmissible : Interface → Held2 → Prop) (totalCost : Interface → Held2 → ℝ)
    (realized : Interface → Held2)
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost)
    (adm : Interface → ℝ × ℝ × ℝ → Prop) (cost : Interface → ℝ × ℝ × ℝ → ℝ)
    (hadm : ∀ i h, originalAdmissible i h ↔ adm i (plainNow h))
    (hcost : ∀ i h, totalCost i h = cost i (plainNow h)) (i : Interface) :
    (realized i).a2 = 0 ∧ (realized i).b2 = 0 :=
  APFB07b.realized_held_state_has_no_rate originalAdmissible totalCost realized hA2 hBW
    (fun i h hh => by rw [hadm, rateFlip_keeps_plainNow]; exact (hadm i h).mp hh)
    (fun i h => by rw [hcost, hcost, rateFlip_keeps_plainNow]) i

open APFPaper5.K3 in
theorem APFB07b.realized_rate_not_forbidden :
    ∃ (originalAdmissible : Unit → Held2 → Prop) (totalCost : Unit → Held2 → ℝ)
      (realized : Unit → Held2),
      APFB07a.A2Selection originalAdmissible totalCost realized ∧
        APFB07b.BWUniqueMinimum originalAdmissible totalCost ∧ (realized ()).b2 ≠ 0 := by
  refine ⟨fun _ h => h = ⟨1, 0, 0, 1⟩, fun _ _ => 0, fun _ => ⟨1, 0, 0, 1⟩, ?_, ?_, ?_⟩
  · intro i
    exact ⟨rfl, fun G _ => le_refl _⟩
  · intro i
    exact ⟨⟨1, 0, 0, 1⟩, ⟨rfl, fun H _ => le_refl _⟩, fun H hH => hH.1⟩
  · show (1 : ℝ) ≠ 0
    exact one_ne_zero


theorem solution :
@Exists.{1} (Unit → APFPaper5.K3.Held2 → Prop) fun (originalAdmissible : Unit → APFPaper5.K3.Held2 → Prop) =>
  @Exists.{1} (Unit → APFPaper5.K3.Held2 → Real) fun (totalCost : Unit → APFPaper5.K3.Held2 → Real) =>
    @Exists.{1} (Unit → APFPaper5.K3.Held2) fun (realized : Unit → APFPaper5.K3.Held2) =>
      And
        (@APFB07a.A2Selection.{0, 0} Unit (fun (i : Unit) => APFPaper5.K3.Held2) originalAdmissible totalCost realized)
        (And (@APFB07b.BWUniqueMinimum.{0, 0} Unit (fun (i : Unit) => APFPaper5.K3.Held2) originalAdmissible totalCost)
          (@Ne.{1} Real (APFPaper5.K3.Held2.b2 (realized Unit.unit))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) := by
  exact @APFB07b.realized_rate_not_forbidden
