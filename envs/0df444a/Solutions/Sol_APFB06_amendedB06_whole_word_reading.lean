-- Prove2me | solution 1 for APFB06.amendedB06_whole_word_reading
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:03:33.173199+00:00
-- url     : https://prove2.me/submissions/374b00f3-1620-4b8b-8c2f-c9650f2606f0

/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFB06.amendedB06_whole_word_reading
title: What the occupancy input asserts when its continuation class is the whole-word budgeted class
inputs_revision: 2026-10-04.1 (the reading recorded here needs the author's fidelity-correction line in
  FOUNDATION_INPUTS before this node can name a revision; see FOUNDATION_INPUTS_fidelity_line_DRAFT)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1873-1883 (occupancy, explicit operational commitment). Author ruling of
  2026-11-12, item 4.
consumes: B06 only (live declared-input node 67b0b53b, encoding AmendedB06_20260914, unchanged).
statement: Instantiate B06 with processes := words, Cont := the whole-word budgeted class, and the whole
  resource of a protocol := the resource of that same word. Then B06 yields an actual occupied alignment with
  a nonempty carried family, a protocol p in its joint class, and a raw input x such that the calibrated whole
  resource of p is at most the capacity of the context and p executes from x.
status of the content: the bill bound (T) and the execution are read off B06's own clause "p in Cont(x)" by
  unfolding the definition of Cont. They are content of the input under this reading. Nothing is derived.
named identification, carried by the instantiation and needing source review: the whole resource B06 assigns
  to a protocol is the resource the continuation class tests for the same word ("the same complete original
  process in both memberships ... whole-resource account", Supplement 1883).
second statement (held_family_bound_of_joint_bill): for any joint class J, a protocol in J S with calibrated
  bill at most C gives originalCost J S ≤ C. So under the reading above, B06's held-family bound clause follows
  from its operational clause; the two clauses are no longer independent.
prop_field_traces: APFB06.OriginalAlignment.active, traced on the live B06 node; this module adds no structure
  and no field.
-/
import Definitions.Def_APFPaper1_ContinuationWords
import Definitions.Def_APF_B06_DeclaredInput

set_option autoImplicit false
open APFPaper1.Continuation

/-- B06 read through the whole-word budgeted continuation class. -/
theorem APFB06.amendedB06_whole_word_reading
    {Context : Type*} {Frag : Context → Context → Type*} {Raw R : Context → Type*}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont step resource calibration C g) → Bool))
    (protocols : (g : Context) → Set (WordFrom Frag g))
    (J : (g : Context) → Finset (APFB06.Task (Cont step resource calibration C g) (D g)) →
      Set {p // p ∈ protocols g})
    (actualJoint :
      Set (Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g)))
    (hB06 : APFB06.AmendedB06_20260914 (Cont step resource calibration C) D protocols J
      (fun g p => resource g p.val) calibration C actualJoint) :
    ∃ o : Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g),
      o ∈ actualJoint ∧ o.2.carried.Nonempty ∧
      ∃ p : {p // p ∈ protocols o.1}, p ∈ J o.1 o.2.carried ∧
        calibration o.1 (resource o.1 p.val) ≤ C o.1 ∧
        ∃ x : Raw o.1, ∃ y : Raw p.val.1, Executes step p.val.2 x y := by
  obtain ⟨o, ho, hne, _hcost, p, hp, x, hx⟩ := hB06
  exact ⟨o, ho, hne, p, hp, hx.2, x, hx.1⟩

/-- A protocol in the joint class with calibrated bill at most `C` bounds the infimal joint cost by `C`. -/
theorem APFB06.held_family_bound_of_joint_bill
    {D P R : Type*} (J : Finset D → Set P) (wholeResource : P → R) (calibration : R → NNReal)
    (S : Finset D) (C : NNReal) (p : P) (hp : p ∈ J S)
    (hbill : calibration (wholeResource p) ≤ C) :
    APFB06.originalCost J wholeResource calibration S ≤ (C : ENNReal) :=
  le_trans (sInf_le ⟨p, hp, rfl⟩) (ENNReal.coe_le_coe.mpr hbill)


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {Context : Type apfNative_u_1} {Frag : Context → Context → Type apfNative_u_2} {Raw : Context → Type apfNative_u_3}
  {R : Context → Type apfNative_u_4} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (D :
    (g : Context) →
      Set.{apfNative_u_3}
        (@APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag Raw
              R step resource calibration C g) →
          Bool))
  (protocols :
    (g : Context) →
      Set.{max apfNative_u_2 apfNative_u_1}
        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g))
  (J :
    (g : Context) →
      Finset.{apfNative_u_3}
          (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag Raw
              R step resource calibration C g)
            (D g)) →
        Set.{max apfNative_u_1 apfNative_u_2}
          (@Subtype.{(max apfNative_u_1 apfNative_u_2) + 1}
            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
            fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g) =>
            @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
              (Set.{max apfNative_u_2 apfNative_u_1}
                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g))
              (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g))
              (protocols g) p))
  (actualJoint :
    Set.{max apfNative_u_3 apfNative_u_1}
      (@Sigma.{apfNative_u_1, apfNative_u_3} Context fun (g : Context) =>
        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag Raw R
            step resource calibration C g)
          (D g)))
  (hB06 :
    @APFB06.AmendedB06_20260914.{apfNative_u_1, apfNative_u_3, max apfNative_u_2 apfNative_u_1, apfNative_u_4} Context
      Raw (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag) R
      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag Raw R step
        resource calibration C)
      D protocols J
      (fun (g : Context)
          (p :
            @Subtype.{(max apfNative_u_2 apfNative_u_1) + 1}
              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
              fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g) =>
              @Membership.mem.{max apfNative_u_2 apfNative_u_1, max apfNative_u_2 apfNative_u_1}
                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                (Set.{max apfNative_u_2 apfNative_u_1}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g))
                (@Set.instMembership.{max apfNative_u_2 apfNative_u_1}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g))
                (protocols g) p) =>
        resource g
          (@Subtype.val.{max (apfNative_u_1 + 1) (apfNative_u_2 + 1)}
            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
            (fun (p : @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g) =>
              @Membership.mem.{max apfNative_u_2 apfNative_u_1, max apfNative_u_2 apfNative_u_1}
                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                (Set.{max apfNative_u_2 apfNative_u_1}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g))
                (@Set.instMembership.{max apfNative_u_2 apfNative_u_1}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g))
                (protocols g) p)
            p))
      calibration C actualJoint),
  @Exists.{max (apfNative_u_1 + 1) (apfNative_u_3 + 1)}
    (@Sigma.{apfNative_u_1, apfNative_u_3} Context fun (g : Context) =>
      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag Raw R
          step resource calibration C g)
        (D g))
    fun
      (o :
        @Sigma.{apfNative_u_1, apfNative_u_3} Context fun (g : Context) =>
          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag Raw
              R step resource calibration C g)
            (D g)) =>
    And
      (@Membership.mem.{max apfNative_u_1 apfNative_u_3, max apfNative_u_1 apfNative_u_3}
        (@Sigma.{apfNative_u_1, apfNative_u_3} Context fun (g : Context) =>
          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag Raw
              R step resource calibration C g)
            (D g))
        (Set.{max apfNative_u_3 apfNative_u_1}
          (@Sigma.{apfNative_u_1, apfNative_u_3} Context fun (g : Context) =>
            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag
                Raw R step resource calibration C g)
              (D g)))
        (@Set.instMembership.{max apfNative_u_1 apfNative_u_3}
          (@Sigma.{apfNative_u_1, apfNative_u_3} Context fun (g : Context) =>
            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag
                Raw R step resource calibration C g)
              (D g)))
        actualJoint o)
      (And
        (@Finset.Nonempty.{apfNative_u_3}
          (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
            (Raw
              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                      Frag Raw R step resource calibration C g)
                    (D g))
                o))
            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                      Frag Raw R step resource calibration C g)
                    (D g))
                o))
            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag Raw
              R step resource calibration C
              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                      Frag Raw R step resource calibration C g)
                    (D g))
                o))
            (D
              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                      Frag Raw R step resource calibration C g)
                    (D g))
                o)))
          (@APFB06.OriginalAlignment.carried.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
            (Raw
              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                      Frag Raw R step resource calibration C g)
                    (D g))
                o))
            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                      Frag Raw R step resource calibration C g)
                    (D g))
                o))
            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag Raw
              R step resource calibration C
              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                      Frag Raw R step resource calibration C g)
                    (D g))
                o))
            (D
              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                      Frag Raw R step resource calibration C g)
                    (D g))
                o))
            (@Sigma.snd.{apfNative_u_1, apfNative_u_3} Context
              (fun (g : Context) =>
                @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                    Frag Raw R step resource calibration C g)
                  (D g))
              o)))
        (@Exists.{max (apfNative_u_1 + 1) (apfNative_u_2 + 1)}
          (@Subtype.{(max apfNative_u_1 apfNative_u_2) + 1}
            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                (fun (g : Context) =>
                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                      Frag Raw R step resource calibration C g)
                    (D g))
                o))
            fun
              (p :
                @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C g)
                        (D g))
                    o)) =>
            @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                  (fun (g : Context) =>
                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                        Frag Raw R step resource calibration C g)
                      (D g))
                  o))
              (Set.{max apfNative_u_2 apfNative_u_1}
                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C g)
                        (D g))
                    o)))
              (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C g)
                        (D g))
                    o)))
              (protocols
                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                  (fun (g : Context) =>
                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                        Frag Raw R step resource calibration C g)
                      (D g))
                  o))
              p)
          fun
            (p :
              @Subtype.{(max apfNative_u_1 apfNative_u_2) + 1}
                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C g)
                        (D g))
                    o))
                fun
                  (p :
                    @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o)) =>
                @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o))
                  (Set.{max apfNative_u_2 apfNative_u_1}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o)))
                  (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o)))
                  (protocols
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o))
                  p) =>
          And
            (@Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
              (@Subtype.{(max apfNative_u_1 apfNative_u_2) + 1}
                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C g)
                        (D g))
                    o))
                fun
                  (p :
                    @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o)) =>
                @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o))
                  (Set.{max apfNative_u_2 apfNative_u_1}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o)))
                  (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o)))
                  (protocols
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o))
                  p)
              (Set.{max apfNative_u_1 apfNative_u_2}
                (@Subtype.{(max apfNative_u_1 apfNative_u_2) + 1}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o))
                  fun
                    (p :
                      @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o)) =>
                  @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o))
                    (Set.{max apfNative_u_2 apfNative_u_1}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o)))
                    (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o)))
                    (protocols
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o))
                    p))
              (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                (@Subtype.{(max apfNative_u_1 apfNative_u_2) + 1}
                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o))
                  fun
                    (p :
                      @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o)) =>
                  @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o))
                    (Set.{max apfNative_u_2 apfNative_u_1}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o)))
                    (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o)))
                    (protocols
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o))
                    p))
              (J
                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                  (fun (g : Context) =>
                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                        Frag Raw R step resource calibration C g)
                      (D g))
                  o)
                (@APFB06.OriginalAlignment.carried.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                  (Raw
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o))
                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o))
                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                    Frag Raw R step resource calibration C
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o))
                  (D
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o))
                  (@Sigma.snd.{apfNative_u_1, apfNative_u_3} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C g)
                        (D g))
                    o)))
              p)
            (And
              (@LE.le.{0} NNReal
                (@Preorder.toLE.{0} NNReal (@PartialOrder.toPreorder.{0} NNReal NNReal.instPartialOrder))
                (calibration
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C g)
                        (D g))
                    o)
                  (resource
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o)
                    (@Subtype.val.{max (apfNative_u_1 + 1) (apfNative_u_2 + 1)}
                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o))
                      (fun
                          (p :
                            @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o)) =>
                        @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                            (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                              (fun (g : Context) =>
                                @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C g)
                                  (D g))
                              o))
                          (Set.{max apfNative_u_2 apfNative_u_1}
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o)))
                          (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o)))
                          (protocols
                            (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                              (fun (g : Context) =>
                                @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C g)
                                  (D g))
                              o))
                          p)
                      p)))
                (C
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C g)
                        (D g))
                    o)))
              (@Exists.{apfNative_u_3 + 1}
                (Raw
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C g)
                        (D g))
                    o))
                fun
                  (x :
                    Raw
                      (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                        (fun (g : Context) =>
                          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C g)
                            (D g))
                        o)) =>
                @Exists.{apfNative_u_3 + 1}
                  (Raw
                    (@Sigma.fst.{apfNative_u_1, max apfNative_u_1 apfNative_u_2} Context
                      (fun (h : Context) =>
                        @APFPaper1.Continuation.Word.{apfNative_u_1, apfNative_u_2} Context Frag
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o)
                          h)
                      (@Subtype.val.{max (apfNative_u_1 + 1) (apfNative_u_2 + 1)}
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o))
                        (fun
                            (p :
                              @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                  (fun (g : Context) =>
                                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                            apfNative_u_4}
                                        Context Frag Raw R step resource calibration C g)
                                      (D g))
                                  o)) =>
                          @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
                            (Set.{max apfNative_u_2 apfNative_u_1}
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                  (fun (g : Context) =>
                                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                            apfNative_u_4}
                                        Context Frag Raw R step resource calibration C g)
                                      (D g))
                                  o)))
                            (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                  (fun (g : Context) =>
                                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                            apfNative_u_4}
                                        Context Frag Raw R step resource calibration C g)
                                      (D g))
                                  o)))
                            (protocols
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
                            p)
                        p)))
                  fun
                    (y :
                      Raw
                        (@Sigma.fst.{apfNative_u_1, max apfNative_u_1 apfNative_u_2} Context
                          (fun (h : Context) =>
                            @APFPaper1.Continuation.Word.{apfNative_u_1, apfNative_u_2} Context Frag
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o)
                              h)
                          (@Subtype.val.{max (apfNative_u_1 + 1) (apfNative_u_2 + 1)}
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
                            (fun
                                (p :
                                  @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                      (fun (g : Context) =>
                                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                          (Raw g)
                                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                            g)
                                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                                apfNative_u_4}
                                            Context Frag Raw R step resource calibration C g)
                                          (D g))
                                      o)) =>
                              @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                    (fun (g : Context) =>
                                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                              apfNative_u_4}
                                          Context Frag Raw R step resource calibration C g)
                                        (D g))
                                    o))
                                (Set.{max apfNative_u_2 apfNative_u_1}
                                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                      (fun (g : Context) =>
                                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                          (Raw g)
                                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                            g)
                                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                                apfNative_u_4}
                                            Context Frag Raw R step resource calibration C g)
                                          (D g))
                                      o)))
                                (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                      (fun (g : Context) =>
                                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                          (Raw g)
                                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                            g)
                                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                                apfNative_u_4}
                                            Context Frag Raw R step resource calibration C g)
                                          (D g))
                                      o)))
                                (protocols
                                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                    (fun (g : Context) =>
                                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                              apfNative_u_4}
                                          Context Frag Raw R step resource calibration C g)
                                        (D g))
                                    o))
                                p)
                            p))) =>
                  @APFPaper1.Continuation.Executes.{apfNative_u_1, apfNative_u_2, apfNative_u_3} Context Frag Raw step
                    (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                      (fun (g : Context) =>
                        @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                          (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C g)
                          (D g))
                      o)
                    (@Sigma.fst.{apfNative_u_1, max apfNative_u_1 apfNative_u_2} Context
                      (fun (h : Context) =>
                        @APFPaper1.Continuation.Word.{apfNative_u_1, apfNative_u_2} Context Frag
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o)
                          h)
                      (@Subtype.val.{max (apfNative_u_1 + 1) (apfNative_u_2 + 1)}
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o))
                        (fun
                            (p :
                              @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                  (fun (g : Context) =>
                                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                            apfNative_u_4}
                                        Context Frag Raw R step resource calibration C g)
                                      (D g))
                                  o)) =>
                          @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
                            (Set.{max apfNative_u_2 apfNative_u_1}
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                  (fun (g : Context) =>
                                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                            apfNative_u_4}
                                        Context Frag Raw R step resource calibration C g)
                                      (D g))
                                  o)))
                            (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                  (fun (g : Context) =>
                                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                            apfNative_u_4}
                                        Context Frag Raw R step resource calibration C g)
                                      (D g))
                                  o)))
                            (protocols
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
                            p)
                        p))
                    (@Sigma.snd.{apfNative_u_1, max apfNative_u_1 apfNative_u_2} Context
                      (fun (h : Context) =>
                        @APFPaper1.Continuation.Word.{apfNative_u_1, apfNative_u_2} Context Frag
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o)
                          h)
                      (@Subtype.val.{max (apfNative_u_1 + 1) (apfNative_u_2 + 1)}
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o))
                        (fun
                            (p :
                              @APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                  (fun (g : Context) =>
                                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                            apfNative_u_4}
                                        Context Frag Raw R step resource calibration C g)
                                      (D g))
                                  o)) =>
                          @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
                            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
                            (Set.{max apfNative_u_2 apfNative_u_1}
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                  (fun (g : Context) =>
                                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                            apfNative_u_4}
                                        Context Frag Raw R step resource calibration C g)
                                      (D g))
                                  o)))
                            (@Set.instMembership.{max apfNative_u_1 apfNative_u_2}
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag
                                (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                  (fun (g : Context) =>
                                    @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                      (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                            apfNative_u_4}
                                        Context Frag Raw R step resource calibration C g)
                                      (D g))
                                  o)))
                            (protocols
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
                            p)
                        p))
                    x y)))) := by
  exact @APFB06.amendedB06_whole_word_reading
