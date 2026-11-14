-- Prove2me | solution 1 for APFB06.originalCost_extensionalJoint_eq_familyCost
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:00:05.330048+00:00
-- url     : https://prove2.me/submissions/994d1b7d-5ebc-4de6-ab03-846929fb6ba0

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-13; not
 gated, not reviewed, not released, not built on the build box)
name: APFB06_extensional_joint_class
title: At the extensional joint class, B06's cost clause is ledger admissibility and the subfamily clause is a theorem
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFB06_ExtensionalJoint (PROPOSED); Def_APF_B06_DeclaredInput; Def_APFPaper1_FamilyCost;
 Thm_APFB06_occupant_subfamily_cost. Paper 1 Supplement v9.28:7101, 2777-2782, 1787-1790 (an empty protocol
 class has infimum +infinity and supplies no finite task).
consumes_inputs: B06 (AmendedB06_20260914) in the last two statements, read AT the extensional joint class.
 The first five statements are ordinary mathematics on the definitions.
named_hypotheses: none. The standing condition is the proposal itself: that B06's joint class is the
 extensional one.
statement: (1) a protocol that serves a family serves each subfamily, so the class of a family is contained
 in the class of each subfamily: the hypothesis hJ of APFB06.occupant_subfamily_cost. (2) a family is
 feasible exactly when its class is nonempty. (3) B06's cost of a family, the infimum in [0, infinity] of
 the bills over the class, is at most a finite capacity exactly when the family is ledger-admissible at that
 capacity (feasible, and real family cost at most the capacity). (4) for a feasible family the two costs are
 the same number. (5, 6) under B06 at the extensional class: the conclusion of occupant_subfamily_cost with
 no hypothesis on the class; and the occupied family and every subfamily of it are ledger-admissible, with
 one protocol that serves the whole family and is available at some raw input.
not_claimed: that B06's joint class is the extensional one; anything about where a serving protocol ends or
 what a mark reads there (the endpoint bridge of APFB06.occupant_jointly_held is NOT obtained: serving is a
 statement about records, not about runs); any law on the record data; support novelty; HeldRelationExists.
-/
import Definitions.Def_APFB06_ExtensionalJoint
import Theorems.Thm_APFB06_occupant_subfamily_cost
import Mathlib.Data.ENNReal.Basic

set_option autoImplicit false
open APFPaper1.Source

namespace APFB06

/-- (1) The same-protocol subfamily clause. -/
theorem extensionalJoint_anti {D P Record : Type*} (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S S' : Finset D) (h : S' ⊆ S) :
    extensionalJoint maintained sufficient usesToRealize S ⊆
      extensionalJoint maintained sufficient usesToRealize S' :=
  fun _ hp d hd => hp d (h hd)

/-- (2) Feasibility is nonemptiness of the class. -/
theorem familyFeasible_iff_extensionalJoint_nonempty {D P Record : Type*}
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) :
    familyFeasible maintained sufficient usesToRealize S ↔
      (extensionalJoint maintained sufficient usesToRealize S).Nonempty :=
  Iff.rfl

theorem familyFeasible_iff_servingBills_nonempty {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S : Finset D) :
    familyFeasible maintained sufficient usesToRealize S ↔
      (servingBills wholeResource calibration maintained sufficient usesToRealize S).Nonempty :=
  ⟨fun ⟨p, hp⟩ => ⟨_, p, hp, rfl⟩, fun ⟨_, p, hp, _⟩ => ⟨p, hp⟩⟩

/-- B06's cost at the extensional class is the infimum, in `[0, ∞]`, of the serving bills. -/
theorem originalCost_extensionalJoint_eq_sInf {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S : Finset D) :
    originalCost (extensionalJoint maintained sufficient usesToRealize) wholeResource calibration S =
      sInf ((fun t : NNReal => (t : ENNReal)) ''
        servingBills wholeResource calibration maintained sufficient usesToRealize S) := by
  unfold originalCost
  congr 1
  ext c
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨calibration (wholeResource p), ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

/-- The ledger's family cost is the real infimum of the same bills. -/
theorem familyCost_eq_sInf {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S : Finset D) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S =
      sInf ((fun t : NNReal => (t : ℝ)) ''
        servingBills wholeResource calibration maintained sufficient usesToRealize S) := by
  unfold familyCost
  congr 1
  ext c
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨calibration (wholeResource p), ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

/-- (4) For a feasible family, B06's cost at the extensional class is the ledger's family cost. -/
theorem originalCost_extensionalJoint_eq_familyCost {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S : Finset D) (hf : familyFeasible maintained sufficient usesToRealize S) :
    originalCost (extensionalJoint maintained sufficient usesToRealize) wholeResource calibration S =
      ENNReal.ofReal (familyCost wholeResource calibration maintained sufficient usesToRealize S) := by
  have hT := (familyFeasible_iff_servingBills_nonempty wholeResource calibration maintained
    sufficient usesToRealize S).mp hf
  rw [originalCost_extensionalJoint_eq_sInf, familyCost_eq_sInf, sInf_image,
    ← ENNReal.coe_sInf hT, ← NNReal.coe_sInf, ENNReal.ofReal_coe_nnreal]

/-- (3) B06's cost clause at the extensional class is ledger admissibility. -/
theorem originalCost_extensionalJoint_le_iff {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S : Finset D) (C : NNReal) :
    originalCost (extensionalJoint maintained sufficient usesToRealize) wholeResource calibration S ≤
        (C : ENNReal) ↔
      familyAdmissible wholeResource calibration maintained sufficient usesToRealize (C : ℝ) S := by
  have hfeas := familyFeasible_iff_servingBills_nonempty wholeResource calibration maintained
    sufficient usesToRealize S
  rcases (servingBills wholeResource calibration maintained sufficient usesToRealize S).eq_empty_or_nonempty
    with hT | hT
  · constructor
    · intro h
      rw [originalCost_extensionalJoint_eq_sInf, hT, Set.image_empty, sInf_empty] at h
      exact absurd (top_le_iff.mp h) ENNReal.coe_ne_top
    · rintro ⟨hf, _⟩
      have hne := hfeas.mp hf
      rw [hT] at hne
      exact absurd hne Set.not_nonempty_empty
  · unfold familyAdmissible
    rw [originalCost_extensionalJoint_eq_sInf, familyCost_eq_sInf, sInf_image,
      ← ENNReal.coe_sInf hT, ← NNReal.coe_sInf, ENNReal.coe_le_coe, NNReal.coe_le_coe]
    exact ⟨fun h => ⟨hfeas.mpr hT, h⟩, fun h => h.2⟩

/-- (5) `APFB06.occupant_subfamily_cost` with its hypothesis on the joint class proved. -/
theorem occupant_subfamily_cost_extensional
    {Context : Type*} {Raw FullProcess Resource : Context → Type*} {Record : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (maintained : (g : Context) → {p // p ∈ protocols g} → Set (Record g))
    (sufficient : (g : Context) → {p // p ∈ protocols g} → Set (Record g) →
      Task (Cont g) (D g) → Prop)
    (usesToRealize : (g : Context) → {p // p ∈ protocols g} → Task (Cont g) (D g) →
      Set (Record g) → Prop)
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g)))
    (hB06 : AmendedB06_20260914 Cont D protocols
      (fun g => extensionalJoint (maintained g) (sufficient g) (usesToRealize g))
      wholeResource calibration C actualJoint) :
    ∃ o : Sigma fun g => OriginalAlignment (Cont g) (D g),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧
      ∀ S' : Finset (Task (Cont o.1) (D o.1)), S' ⊆ o.2.carried →
        originalCost (extensionalJoint (maintained o.1) (sufficient o.1) (usesToRealize o.1))
            (wholeResource o.1) (calibration o.1) S' ≤ (C o.1 : ENNReal) ∧
        originalCost (extensionalJoint (maintained o.1) (sufficient o.1) (usesToRealize o.1))
            (wholeResource o.1) (calibration o.1) S' ≠ ⊤ :=
  occupant_subfamily_cost Cont D protocols
    (fun g => extensionalJoint (maintained g) (sufficient g) (usesToRealize g))
    wholeResource calibration C actualJoint hB06
    (fun g S S' h => extensionalJoint_anti (maintained g) (sufficient g) (usesToRealize g) S S' h)

/-- (6) From B06's declared form to the ledger vocabulary: the occupied family and each of its subfamilies
are ledger-admissible, and one protocol serves the whole family and is available at some raw input. -/
theorem occupant_family_admissible
    {Context : Type*} {Raw FullProcess Resource : Context → Type*} {Record : Context → Type*}
    (Cont : (g : Context) → Raw g → FullProcess g → Prop)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont g) → Bool))
    (protocols : (g : Context) → Set (FullProcess g))
    (maintained : (g : Context) → {p // p ∈ protocols g} → Set (Record g))
    (sufficient : (g : Context) → {p // p ∈ protocols g} → Set (Record g) →
      Task (Cont g) (D g) → Prop)
    (usesToRealize : (g : Context) → {p // p ∈ protocols g} → Task (Cont g) (D g) →
      Set (Record g) → Prop)
    (wholeResource : (g : Context) → {p // p ∈ protocols g} → Resource g)
    (calibration : (g : Context) → Resource g → NNReal)
    (C : Context → NNReal)
    (actualJoint : Set (Sigma fun g => OriginalAlignment (Cont g) (D g)))
    (hB06 : AmendedB06_20260914 Cont D protocols
      (fun g => extensionalJoint (maintained g) (sufficient g) (usesToRealize g))
      wholeResource calibration C actualJoint) :
    ∃ o : Sigma fun g => OriginalAlignment (Cont g) (D g),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧
      (∀ S' : Finset (Task (Cont o.1) (D o.1)), S' ⊆ o.2.carried →
        familyAdmissible (wholeResource o.1) (calibration o.1) (maintained o.1) (sufficient o.1)
          (usesToRealize o.1) (C o.1 : ℝ) S') ∧
      ∃ p : {p // p ∈ protocols o.1},
        Serves (maintained o.1) (sufficient o.1) (usesToRealize o.1) p o.2.carried ∧
        ∃ x : Raw o.1, Cont o.1 x p.val := by
  obtain ⟨o, ho, hne, hcost, p, hp, x, hx⟩ := hB06
  refine ⟨o, ho, hne, fun S' hS' => ?_, p, hp, x, hx⟩
  have hmono :
      originalCost (extensionalJoint (maintained o.1) (sufficient o.1) (usesToRealize o.1))
          (wholeResource o.1) (calibration o.1) S' ≤
        originalCost (extensionalJoint (maintained o.1) (sufficient o.1) (usesToRealize o.1))
          (wholeResource o.1) (calibration o.1) o.2.carried := by
    unfold originalCost
    apply sInf_le_sInf
    rintro c ⟨q, hq, rfl⟩
    exact ⟨q, extensionalJoint_anti _ _ _ _ _ hS' hq, rfl⟩
  exact (originalCost_extensionalJoint_le_iff _ _ _ _ _ S' (C o.1)).mp (le_trans hmono hcost)

end APFB06

#print axioms APFB06.extensionalJoint_anti
#print axioms APFB06.originalCost_extensionalJoint_eq_familyCost
#print axioms APFB06.originalCost_extensionalJoint_le_iff
#print axioms APFB06.occupant_subfamily_cost_extensional
#print axioms APFB06.occupant_family_admissible


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set.{apfNative_u_4} Record)
  (sufficient : P → Set.{apfNative_u_4} Record → D → Prop) (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop)
  (S : Finset.{apfNative_u_1} D)
  (hf :
    @APFPaper1.Source.familyFeasible.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
      usesToRealize S),
  @Eq.{1} ENNReal
    (@APFB06.originalCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P R
      (@APFB06.extensionalJoint.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
        usesToRealize)
      wholeResource calibration S)
    (ENNReal.ofReal
      (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
        wholeResource calibration maintained sufficient usesToRealize S)) := by
  exact @APFB06.originalCost_extensionalJoint_eq_familyCost
