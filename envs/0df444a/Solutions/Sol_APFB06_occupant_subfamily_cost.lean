-- Prove2me | solution 1 for APFB06.occupant_subfamily_cost
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:18:07.404278+00:00
-- url     : https://prove2.me/submissions/979ac7dc-1b3d-46f1-8d92-f54e53bc8a58

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFB06_occupant_subfamily_cost
title: The occupant gives every part of its held family a finite joint cost
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author's remark of 2026-11-12, "it exists because the occupant exists". FOUNDATION_INPUTS B06
 current wording; live node Def_APF_B06_DeclaredInput.
consumes_inputs: B06 (AmendedB06_20260914).
named_hypothesis: hJ, that a protocol in the joint class of a family is in the joint class of each of its
 subfamilies. B06 states no law on the joint class J; this one is assumed here and nowhere else.
statement: under B06 and hJ there is an actual occupied alignment with nonempty carried family such that
 every subfamily of the carried family, in particular every pair of its members, has original joint cost
 at most the context capacity, hence not infinite.
not_claimed: that this cost is a score, a pair number or a probability; any statement about its value.
-/
import Definitions.Def_APF_B06_DeclaredInput
import Mathlib.Data.ENNReal.Basic

set_option autoImplicit false

theorem APFB06.occupant_subfamily_cost
    {Context : Type*} {Raw FullProcess Resource : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (J : (g : Context) → Finset (APFB06.Task (Cont g) (D g)) → Set {p // p ∈ protocols g})
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => APFB06.OriginalAlignment (Cont g) (D g)))
    (hB06 : APFB06.AmendedB06_20260914 Cont D protocols J wholeResource calibration C actualJoint)
    (hJ : ∀ (g : Context) (S S' : Finset (APFB06.Task (Cont g) (D g))),
      S' ⊆ S → J g S ⊆ J g S') :
    ∃ o : Sigma fun g => APFB06.OriginalAlignment (Cont g) (D g),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧
      ∀ S' : Finset (APFB06.Task (Cont o.1) (D o.1)), S' ⊆ o.2.carried →
        APFB06.originalCost (J o.1) (wholeResource o.1) (calibration o.1) S' ≤ (C o.1 : ENNReal) ∧
        APFB06.originalCost (J o.1) (wholeResource o.1) (calibration o.1) S' ≠ ⊤ := by
  obtain ⟨o, ho, hne, hcost, _⟩ := hB06
  refine ⟨o, ho, hne, fun S' hS' => ?_⟩
  have hmono : APFB06.originalCost (J o.1) (wholeResource o.1) (calibration o.1) S' ≤
      APFB06.originalCost (J o.1) (wholeResource o.1) (calibration o.1) o.2.carried := by
    unfold APFB06.originalCost
    apply sInf_le_sInf
    rintro c ⟨p, hp, rfl⟩
    exact ⟨p, hJ o.1 _ _ hS' hp, rfl⟩
  have h := le_trans hmono hcost
  exact ⟨h, ne_top_of_le_ne_top ENNReal.coe_ne_top h⟩


universe u_1 u_2 u_3 u_4
theorem solution :
∀ {Context : Type u_1} {Raw : Context → Type u_2} {FullProcess : Context → Type u_3} {Resource : Context → Type u_4}
  (Cont : (g : Context) → Raw g → FullProcess g → Prop)
  (D : (g : Context) → Set.{u_2} (APFB01.PhysicalState.{u_2, u_3} (Cont g) → Bool))
  (protocols : (g : Context) → Set.{u_3} (FullProcess g))
  (J :
    (g : Context) →
      Finset.{u_2} (APFB06.Task.{u_2, u_3} (Cont g) (D g)) →
        Set.{u_3} (Subtype.{u_3 + 1} fun p => Membership.mem.{u_3, u_3} (protocols g) p))
  (wholeResource : (g : Context) → (Subtype.{u_3 + 1} fun p => Membership.mem.{u_3, u_3} (protocols g) p) → Resource g)
  (calibration : (g : Context) → Resource g → NNReal) (C : Context → NNReal)
  (actualJoint : Set.{max u_2 u_1} ((g : Context) × APFB06.OriginalAlignment.{u_2, u_3} (Cont g) (D g))),
  APFB06.AmendedB06_20260914.{u_1, u_2, u_3, u_4} Cont D protocols J wholeResource calibration C actualJoint →
    (∀ (g : Context) (S S' : Finset.{u_2} (APFB06.Task.{u_2, u_3} (Cont g) (D g))), S' ⊆ S → J g S ⊆ J g S') →
      ∃ o,
        Membership.mem.{max u_1 u_2, max u_1 u_2} actualJoint o ∧
          Finset.Nonempty.{u_2} (APFB06.OriginalAlignment.carried.{u_2, u_3} (Sigma.snd.{u_1, u_2} o)) ∧
            ∀ S' ⊆ APFB06.OriginalAlignment.carried.{u_2, u_3} (Sigma.snd.{u_1, u_2} o),
              LE.le.{0}
                  (APFB06.originalCost.{u_2, u_3, u_4} (J (Sigma.fst.{u_1, u_2} o))
                    (wholeResource (Sigma.fst.{u_1, u_2} o)) (calibration (Sigma.fst.{u_1, u_2} o)) S')
                  ↑(C (Sigma.fst.{u_1, u_2} o)) ∧
                Ne.{1}
                  (APFB06.originalCost.{u_2, u_3, u_4} (J (Sigma.fst.{u_1, u_2} o))
                    (wholeResource (Sigma.fst.{u_1, u_2} o)) (calibration (Sigma.fst.{u_1, u_2} o)) S')
                  Top.top.{0} := by
  exact @APFB06.occupant_subfamily_cost
