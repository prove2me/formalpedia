-- Prove2me | solution 1 for APFB06.occupant_family_admissible
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:58:37.853029+00:00
-- url     : https://prove2.me/submissions/c535871d-da10-4ba9-a563-2c1bedd7da8f

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


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5
theorem solution :
∀ {Context : Type apfNative_u_1} {Raw : Context → Type apfNative_u_2} {FullProcess : Context → Type apfNative_u_3}
  {Resource : Context → Type apfNative_u_4} {Record : Context → Type apfNative_u_5}
  (Cont : (g : Context) → Raw g → FullProcess g → Prop)
  (D :
    (g : Context) →
      Set.{apfNative_u_2}
        (@APFB01.PhysicalState.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) → Bool))
  (protocols : (g : Context) → Set.{apfNative_u_3} (FullProcess g))
  (maintained :
    (g : Context) →
      (@Subtype.{apfNative_u_3 + 1} (FullProcess g) fun (p : FullProcess g) =>
          @Membership.mem.{apfNative_u_3, apfNative_u_3} (FullProcess g) (Set.{apfNative_u_3} (FullProcess g))
            (@Set.instMembership.{apfNative_u_3} (FullProcess g)) (protocols g) p) →
        Set.{apfNative_u_5} (Record g))
  (sufficient :
    (g : Context) →
      (@Subtype.{apfNative_u_3 + 1} (FullProcess g) fun (p : FullProcess g) =>
          @Membership.mem.{apfNative_u_3, apfNative_u_3} (FullProcess g) (Set.{apfNative_u_3} (FullProcess g))
            (@Set.instMembership.{apfNative_u_3} (FullProcess g)) (protocols g) p) →
        Set.{apfNative_u_5} (Record g) →
          @APFB06.Task.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g) → Prop)
  (usesToRealize :
    (g : Context) →
      (@Subtype.{apfNative_u_3 + 1} (FullProcess g) fun (p : FullProcess g) =>
          @Membership.mem.{apfNative_u_3, apfNative_u_3} (FullProcess g) (Set.{apfNative_u_3} (FullProcess g))
            (@Set.instMembership.{apfNative_u_3} (FullProcess g)) (protocols g) p) →
        @APFB06.Task.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g) →
          Set.{apfNative_u_5} (Record g) → Prop)
  (wholeResource :
    (g : Context) →
      (@Subtype.{apfNative_u_3 + 1} (FullProcess g) fun (p : FullProcess g) =>
          @Membership.mem.{apfNative_u_3, apfNative_u_3} (FullProcess g) (Set.{apfNative_u_3} (FullProcess g))
            (@Set.instMembership.{apfNative_u_3} (FullProcess g)) (protocols g) p) →
        Resource g)
  (calibration : (g : Context) → Resource g → NNReal) (C : Context → NNReal)
  (actualJoint :
    Set.{max apfNative_u_2 apfNative_u_1}
      (@Sigma.{apfNative_u_1, apfNative_u_2} Context fun (g : Context) =>
        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g)))
  (hB06 :
    @APFB06.AmendedB06_20260914.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Raw FullProcess
      Resource Cont D protocols
      (fun (g : Context) =>
        @APFB06.extensionalJoint.{apfNative_u_2, apfNative_u_3, apfNative_u_5}
          (@APFB06.Task.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
          (@Subtype.{apfNative_u_3 + 1} (FullProcess g) fun (p : FullProcess g) =>
            @Membership.mem.{apfNative_u_3, apfNative_u_3} (FullProcess g) (Set.{apfNative_u_3} (FullProcess g))
              (@Set.instMembership.{apfNative_u_3} (FullProcess g)) (protocols g) p)
          (Record g) (maintained g) (sufficient g) (usesToRealize g))
      wholeResource calibration C actualJoint),
  @Exists.{max (apfNative_u_1 + 1) (apfNative_u_2 + 1)}
    (@Sigma.{apfNative_u_1, apfNative_u_2} Context fun (g : Context) =>
      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
    fun
      (o :
        @Sigma.{apfNative_u_1, apfNative_u_2} Context fun (g : Context) =>
          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g)) =>
    And
      (@Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
        (@Sigma.{apfNative_u_1, apfNative_u_2} Context fun (g : Context) =>
          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
        (Set.{max apfNative_u_2 apfNative_u_1}
          (@Sigma.{apfNative_u_1, apfNative_u_2} Context fun (g : Context) =>
            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g)))
        (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
          (@Sigma.{apfNative_u_1, apfNative_u_2} Context fun (g : Context) =>
            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g)))
        actualJoint o)
      (And
        (@Finset.Nonempty.{apfNative_u_2}
          (@APFB06.Task.{apfNative_u_2, apfNative_u_3}
            (Raw
              (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                o))
            (FullProcess
              (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                o))
            (Cont
              (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                o))
            (D
              (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                o)))
          (@APFB06.OriginalAlignment.carried.{apfNative_u_2, apfNative_u_3}
            (Raw
              (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                o))
            (FullProcess
              (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                o))
            (Cont
              (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                o))
            (D
              (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                o))
            (@Sigma.snd.{apfNative_u_1, apfNative_u_2} Context
              (fun (g : Context) =>
                @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
              o)))
        (And
          (∀
            (S' :
              Finset.{apfNative_u_2}
                (@APFB06.Task.{apfNative_u_2, apfNative_u_3}
                  (Raw
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (Cont
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (D
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o)))),
            @LE.le.{apfNative_u_2}
                (Finset.{apfNative_u_2}
                  (@APFB06.Task.{apfNative_u_2, apfNative_u_3}
                    (Raw
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))
                    (FullProcess
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))
                    (Cont
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))
                    (D
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))))
                (@Preorder.toLE.{apfNative_u_2}
                  (Finset.{apfNative_u_2}
                    (@APFB06.Task.{apfNative_u_2, apfNative_u_3}
                      (Raw
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o))
                      (FullProcess
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o))
                      (Cont
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o))
                      (D
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o))))
                  (@PartialOrder.toPreorder.{apfNative_u_2}
                    (Finset.{apfNative_u_2}
                      (@APFB06.Task.{apfNative_u_2, apfNative_u_3}
                        (Raw
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                                (D g))
                            o))
                        (FullProcess
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                                (D g))
                            o))
                        (Cont
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                                (D g))
                            o))
                        (D
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                                (D g))
                            o))))
                    (@Finset.instPartialOrder.{apfNative_u_2}
                      (@APFB06.Task.{apfNative_u_2, apfNative_u_3}
                        (Raw
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                                (D g))
                            o))
                        (FullProcess
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                                (D g))
                            o))
                        (Cont
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                                (D g))
                            o))
                        (D
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                                (D g))
                            o))))))
                S'
                (@APFB06.OriginalAlignment.carried.{apfNative_u_2, apfNative_u_3}
                  (Raw
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (Cont
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (D
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (@Sigma.snd.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o)) →
              @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5}
                (@APFB06.Task.{apfNative_u_2, apfNative_u_3}
                  (Raw
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (Cont
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (D
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o)))
                (@Subtype.{apfNative_u_3 + 1}
                  (FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  fun
                    (p :
                      FullProcess
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o)) =>
                  @Membership.mem.{apfNative_u_3, apfNative_u_3}
                    (FullProcess
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))
                    (Set.{apfNative_u_3}
                      (FullProcess
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o)))
                    (@Set.instMembership.{apfNative_u_3}
                      (FullProcess
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o)))
                    (protocols
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))
                    p)
                (Resource
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (Record
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (wholeResource
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (calibration
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (maintained
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (sufficient
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (usesToRealize
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (NNReal.toReal
                  (C
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o)))
                S')
          (@Exists.{apfNative_u_3 + 1}
            (@Subtype.{apfNative_u_3 + 1}
              (FullProcess
                (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                  (fun (g : Context) =>
                    @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                  o))
              fun
                (p :
                  FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o)) =>
              @Membership.mem.{apfNative_u_3, apfNative_u_3}
                (FullProcess
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (Set.{apfNative_u_3}
                  (FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o)))
                (@Set.instMembership.{apfNative_u_3}
                  (FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o)))
                (protocols
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                p)
            fun
              (p :
                @Subtype.{apfNative_u_3 + 1}
                  (FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  fun
                    (p :
                      FullProcess
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o)) =>
                  @Membership.mem.{apfNative_u_3, apfNative_u_3}
                    (FullProcess
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))
                    (Set.{apfNative_u_3}
                      (FullProcess
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o)))
                    (@Set.instMembership.{apfNative_u_3}
                      (FullProcess
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o)))
                    (protocols
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))
                    p) =>
            And
              (@APFB06.Serves.{apfNative_u_2, apfNative_u_3, apfNative_u_5}
                (@APFB06.Task.{apfNative_u_2, apfNative_u_3}
                  (Raw
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (Cont
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (D
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o)))
                (@Subtype.{apfNative_u_3 + 1}
                  (FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  fun
                    (p :
                      FullProcess
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o)) =>
                  @Membership.mem.{apfNative_u_3, apfNative_u_3}
                    (FullProcess
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))
                    (Set.{apfNative_u_3}
                      (FullProcess
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o)))
                    (@Set.instMembership.{apfNative_u_3}
                      (FullProcess
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                              (D g))
                          o)))
                    (protocols
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))
                    p)
                (Record
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (maintained
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (sufficient
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                (usesToRealize
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                p
                (@APFB06.OriginalAlignment.carried.{apfNative_u_2, apfNative_u_3}
                  (Raw
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (FullProcess
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (Cont
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (D
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                      o))
                  (@Sigma.snd.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o)))
              (@Exists.{apfNative_u_2 + 1}
                (Raw
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o))
                fun
                  (x :
                    Raw
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o)) =>
                Cont
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g) (D g))
                    o)
                  x
                  (@Subtype.val.{apfNative_u_3 + 1}
                    (FullProcess
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                            (D g))
                        o))
                    (fun
                        (p :
                          FullProcess
                            (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                              (fun (g : Context) =>
                                @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g)
                                  (Cont g) (D g))
                              o)) =>
                      @Membership.mem.{apfNative_u_3, apfNative_u_3}
                        (FullProcess
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                                (D g))
                            o))
                        (Set.{apfNative_u_3}
                          (FullProcess
                            (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                              (fun (g : Context) =>
                                @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g)
                                  (Cont g) (D g))
                              o)))
                        (@Set.instMembership.{apfNative_u_3}
                          (FullProcess
                            (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                              (fun (g : Context) =>
                                @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g)
                                  (Cont g) (D g))
                              o)))
                        (protocols
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_2} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_2, apfNative_u_3} (Raw g) (FullProcess g) (Cont g)
                                (D g))
                            o))
                        p)
                    p))))) := by
  exact @APFB06.occupant_family_admissible
