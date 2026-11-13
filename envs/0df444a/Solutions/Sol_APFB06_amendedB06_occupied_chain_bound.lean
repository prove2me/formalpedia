-- Prove2me | solution 1 for APFB06.amendedB06_occupied_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-12T16:49:22.947082+00:00
-- url     : https://prove2.me/submissions/b8d60206-7e95-49cc-8c62-46b79674b14f

import Theorems.Thm_APFB05_support_novel_chain_capacity_bound
import Theorems.Thm_APFB06_amendedB06_occupied_family_admissible
import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
set_option autoImplicit false
open APFB06 APFPaper1.Source
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
    [∀ g, DecidableEq (Task (Cont g) (D g))]
    (tested : (g : Context) → Task (Cont g) (D g) → Prop)
    (epsilon : Context → ℝ)
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested (fun g => (C g : ℝ)) epsilon)
    (hJ : ∀ (g : Context) (S : Finset (Task (Cont g) (D g))) (p : {p // p ∈ protocols g}),
      p ∈ J g S → ∀ d ∈ S, ∃ sigma : Set (Record g),
        sigma ⊆ maintained g p ∧ sufficient g p sigma d ∧ usesToRealize g p d sigma)
    (h : AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint) :
    ∃ (o : Sigma fun g => OriginalAlignment (Cont g) (D g))
      (p : {p // p ∈ protocols o.1}) (x : Raw o.1),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧ p ∈ J o.1 o.2.carried ∧ Cont o.1 x p.val ∧
      ∀ (n : ℕ) (S : ℕ → Finset (Task (Cont o.1) (D o.1))) (d : ℕ → Task (Cont o.1) (D o.1)),
        (∀ i < n, S (i + 1) = insert (d i) (S i)) →
        (∀ i < n, tested o.1 (d i)) →
        (∀ i < n, supportNovel (wholeResource o.1) (calibration o.1) (maintained o.1)
          (sufficient o.1) (usesToRealize o.1) (S i) (d i)) →
        S n = o.2.carried →
        (n : ℝ) * epsilon o.1 ≤ (calibration o.1 (wholeResource o.1 p) : ℝ) ∧
          (n : ℝ) ≤ (C o.1 : ℝ) / epsilon o.1 := by
  obtain ⟨o, p, x, ho, hne, hp, hx, hadm, hbill⟩ :=
    amendedB06_occupied_family_admissible Cont D protocols J wholeResource calibration C
      actualJoint maintained sufficient usesToRealize hJ h
  refine ⟨o, p, x, ho, hne, hp, hx, ?_⟩
  intro n S d hstep htested hnovel hSn
  have hadm' : familyAdmissible (wholeResource o.1) (calibration o.1) (maintained o.1)
      (sufficient o.1) (usesToRealize o.1) (C o.1 : ℝ) (S n) := by
    rw [hSn]
    exact hadm
  obtain ⟨h1, h2⟩ := APFB05.support_novel_chain_capacity_bound wholeResource calibration
    maintained sufficient usesToRealize tested (fun g => (C g : ℝ)) epsilon hB05 o.1 n S d
    hstep htested hnovel hadm'
  refine ⟨?_, h2⟩
  rw [hSn] at h1
  exact h1.trans hbill
