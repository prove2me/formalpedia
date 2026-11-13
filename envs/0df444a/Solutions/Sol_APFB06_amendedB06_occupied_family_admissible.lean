-- Prove2me | solution 1 for APFB06.amendedB06_occupied_family_admissible
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-12T16:47:41.498393+00:00
-- url     : https://prove2.me/submissions/62ea5fb9-9813-45d9-81e4-19d90bda972a

import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFPaper1_FamilyCost
set_option autoImplicit false
open APFB06 APFPaper1.Source
namespace APFPaper1.Source

section helpers
variable {D P R Record : Type*}
variable (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)

theorem familyCost_nonneg (S : Finset D) :
    0 ≤ familyCost wholeResource calibration maintained sufficient usesToRealize S := by
  unfold familyCost
  apply Real.sInf_nonneg
  rintro c ⟨p, _, rfl⟩
  exact NNReal.coe_nonneg _
end helpers
end APFPaper1.Source

namespace APFB06
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

namespace APFB06

open APFPaper1.Source

theorem occupied_family_feasible
    {D P R Record : Type*} (J : Finset D → Set P)
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) (C : NNReal)
    (hJ : ∀ p ∈ J S, ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma)
    (h : originalCost J wholeResource calibration S ≤ (C : ENNReal)) :
    familyFeasible maintained sufficient usesToRealize S := by
  obtain ⟨p, hp⟩ := joint_class_nonempty_of_cost_bound J wholeResource calibration S C h
  exact ⟨p, hJ p hp⟩

theorem familyCost_le_bill_of_joint
    {D P R Record : Type*} (J : Finset D → Set P)
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D)
    (hJ : ∀ p ∈ J S, ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma)
    (p : P) (hp : p ∈ J S) :
    0 ≤ familyCost wholeResource calibration maintained sufficient usesToRealize S ∧
    familyCost wholeResource calibration maintained sufficient usesToRealize S ≤
      (calibration (wholeResource p) : ℝ) := by
  refine ⟨familyCost_nonneg wholeResource calibration maintained sufficient usesToRealize S, ?_⟩
  unfold familyCost
  apply csInf_le
  · exact ⟨0, by rintro x ⟨r, _, rfl⟩; exact NNReal.coe_nonneg _⟩
  · exact ⟨p, hJ p hp, rfl⟩

theorem familyCost_le_capacity_of_joint_bound
    {D P R Record : Type*} (J : Finset D → Set P)
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) (C : NNReal)
    (hJ : ∀ p ∈ J S, ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma)
    (h : originalCost J wholeResource calibration S ≤ (C : ENNReal)) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S ≤ (C : ℝ) := by
  obtain ⟨K, hK⟩ : ∃ K : NNReal,
      (K : ℝ) = familyCost wholeResource calibration maintained sufficient usesToRealize S :=
    ⟨⟨_, familyCost_nonneg wholeResource calibration maintained sufficient usesToRealize S⟩, rfl⟩
  have hle : (K : ENNReal) ≤ originalCost J wholeResource calibration S := by
    unfold originalCost
    apply le_sInf
    rintro c ⟨p, hp, rfl⟩
    have h2 := (familyCost_le_bill_of_joint J wholeResource calibration maintained sufficient
      usesToRealize S hJ p hp).2
    rw [← hK] at h2
    exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp h2)
  have hKC : K ≤ C := ENNReal.coe_le_coe.mp (hle.trans h)
  rw [← hK]
  exact NNReal.coe_le_coe.mpr hKC

end APFB06
open APFB06 in
theorem solution
    {Context : Type*} {Raw FullProcess Resource Record : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (J : (g : Context) → Finset (Task (Cont g) (D g)) → Set {p // p ∈ protocols g})
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g)))
    (maintained : (g : Context) → {p // p ∈ protocols g} → Set (Record g))
    (sufficient : (g : Context) → {p // p ∈ protocols g} → Set (Record g) →
      Task (Cont g) (D g) → Prop)
    (usesToRealize : (g : Context) → {p // p ∈ protocols g} →
      Task (Cont g) (D g) → Set (Record g) → Prop)
    (hJ : ∀ (g : Context) (S : Finset (Task (Cont g) (D g))) (p : {p // p ∈ protocols g}),
      p ∈ J g S → ∀ d ∈ S, ∃ sigma : Set (Record g),
        sigma ⊆ maintained g p ∧ sufficient g p sigma d ∧ usesToRealize g p d sigma)
    (h : AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint) :
    ∃ (o : Sigma fun g => OriginalAlignment (Cont g) (D g))
      (p : {p // p ∈ protocols o.1}) (x : Raw o.1),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧ p ∈ J o.1 o.2.carried ∧ Cont o.1 x p.val ∧
      familyAdmissible (wholeResource o.1) (calibration o.1) (maintained o.1) (sufficient o.1)
        (usesToRealize o.1) (C o.1 : ℝ) o.2.carried ∧
      familyCost (wholeResource o.1) (calibration o.1) (maintained o.1) (sufficient o.1)
        (usesToRealize o.1) o.2.carried ≤ (calibration o.1 (wholeResource o.1 p) : ℝ) := by
  obtain ⟨o, ho, hne, hcost, p, hp, x, hx⟩ := h
  refine ⟨o, p, x, ho, hne, hp, hx, ⟨⟨p, hJ o.1 o.2.carried p hp⟩, ?_⟩, ?_⟩
  · exact familyCost_le_capacity_of_joint_bound (J o.1) (wholeResource o.1) (calibration o.1)
      (maintained o.1) (sufficient o.1) (usesToRealize o.1) o.2.carried (C o.1)
      (hJ o.1 o.2.carried) hcost
  · exact (familyCost_le_bill_of_joint (J o.1) (wholeResource o.1) (calibration o.1)
      (maintained o.1) (sufficient o.1) (usesToRealize o.1) o.2.carried
      (hJ o.1 o.2.carried) p hp).2
