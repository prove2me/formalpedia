-- Prove2me | solution 1 for APFB06.amendedB06_extract_E
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-12T15:26:32.560246+00:00
-- url     : https://prove2.me/submissions/5b33a325-36f2-4ccb-bcb5-c562c8707b55

/-
APF Foundation Ledger — theorem node (Batch 3). First theorems consuming the declared input B06.
name: APFB06.amendedB06_extract_E
title: The amended occupancy input supplies one occupied family, one joint protocol and one input from which it is available
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1872-1884 (occupancy: explicit operational commitment) and FOUNDATION_INPUTS.json
  revision 2026-10-04.1, B06 current wording. Restates the archive theorems
  APFOperationalOccupancy.amendedB06_extract_E, APFOperationalOccupancy.amendedB06_forget_to_original and
  APFUpstreamOccupant.original_joint_nonempty_of_bound over the live B06 node, whose data are flat parameters.
statement: Three statements.
  (1) amendedB06_extract_E: if the amended B06 predicate holds, there are an actual alignment o, a protocol p in the
      supplied joint class of o's whole carried family, and a raw input x with p in the continuation profile of x;
      the carried family is nonempty. This is the existential content of the input, unpacked.
  (2) amendedB06_held_family_bound: the amended predicate yields the original held-family bound, the infimal
      calibrated bill of the carried family over the supplied joint class being at most the context capacity.
  (3) joint_class_nonempty_of_cost_bound: for any supplied joint class, a finite bound on that extended-real infimum
      forces the class to be nonempty, since the infimum of an empty set of extended reals is infinite.
  The continuation profile Cont is an arbitrary parameter throughout: nothing is assumed about how it is defined, and
  no bound on the bill of p against capacity is asserted or used. Inputs consumed: B06 only, in (1) and (2);
  (3) consumes no input.
-/
import Definitions.Def_APF_B06_DeclaredInput

set_option autoImplicit false

namespace APFB06


theorem amendedB06_held_family_bound
    {Context : Type*} {Raw FullProcess Resource : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (J : (g : Context) → Finset (Task (Cont g) (D g)) → Set {p // p ∈ protocols g})
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g)))
    (h : AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint) :
    ∃ o : Sigma fun g => OriginalAlignment (Cont g) (D g),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧
      originalCost (J o.1) (wholeResource o.1) (calibration o.1) o.2.carried ≤ (C o.1 : ENNReal) := by
  obtain ⟨o, ho, hne, hcost, _⟩ := h
  exact ⟨o, ho, hne, hcost⟩

theorem joint_class_nonempty_of_cost_bound
    {D P R : Type*} (J : Finset D → Set P)
    (wholeResource : P → R) (calibration : R → NNReal) (S : Finset D) (C : NNReal)
    (h : originalCost J wholeResource calibration S ≤ (C : ENNReal)) :
    (J S).Nonempty := by
  rcases Set.eq_empty_or_nonempty (J S) with hne | hne
  · have hempty :
        {c : ENNReal | ∃ p ∈ J S, (calibration (wholeResource p) : ENNReal) = c} = ∅ := by
      ext c
      constructor
      · rintro ⟨p, hp, _⟩
        rw [hne] at hp
        exact ((Set.mem_empty_iff_false p).mp hp).elim
      · intro hc
        exact ((Set.mem_empty_iff_false c).mp hc).elim
    have h2 : sInf (∅ : Set ENNReal) ≤ (C : ENNReal) := by
      have h1 := h
      unfold originalCost at h1
      rwa [hempty] at h1
    rw [sInf_empty] at h2
    exact absurd (top_le_iff.mp h2) ENNReal.coe_ne_top
  · exact hne

end APFB06

open APFB06 in
theorem solution
    {Context : Type*} {Raw FullProcess Resource : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (J : (g : Context) → Finset (Task (Cont g) (D g)) → Set {p // p ∈ protocols g})
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g)))
    (h : AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint) :
    ∃ (o : Sigma fun g => OriginalAlignment (Cont g) (D g))
      (p : {p // p ∈ protocols o.1}) (x : Raw o.1),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧ p ∈ J o.1 o.2.carried ∧ Cont o.1 x p.val := by
  obtain ⟨o, ho, hne, _hcost, p, hp, x, hx⟩ := h
  exact ⟨o, p, x, ho, hne, hp, hx⟩
