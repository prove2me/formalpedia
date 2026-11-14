-- Prove2me | solution 1 for APFB06.occupant_jointly_held
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:15:45.570252+00:00
-- url     : https://prove2.me/submissions/ae63f0d8-f42c-4c2b-8566-cc60985f66b8

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFB06_occupant_regulation
title: The occupant is an actual disturbance at which two of its marks are held by one budgeted response
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B06 current wording; Thm_APFB06_amendedB06_whole_word_reading (B06 read through the
 whole-word budgeted continuation class, author ruling of 2026-11-12); Def_APFPaper1_Regulation.
consumes_inputs: B06 (AmendedB06_20260914).
named_hypothesis: hbridge, that a protocol in the occupant's joint class, on any run from the occupant's
 raw input, ends where the two marks m1 and m2 read true. B06 binds the joint class to the source by
 correspondence and states no such law in Lean; it is assumed here and nowhere else.
statement: under B06 and hbridge there are a context and a raw input at which m1 and m2 are jointly holdable.
not_claimed: that any disturbance is irreducibly joint for the pair. B06 as encoded asserts a family that IS
 held together; it does not assert a disturbance that defeats the pair and neither member. So B06 gives the
 count ratio a positive numerator on any list containing the occupant's input, and says nothing about
 whether the ratio is below one.
-/
import Definitions.Def_APFPaper1_Regulation
import Theorems.Thm_APFB06_amendedB06_whole_word_reading

set_option autoImplicit false
open APFPaper1.Continuation

theorem APFB06.occupant_jointly_held
    {Context : Type*} {Frag : Context → Context → Type*} {Raw R : Context → Type*} {M : Type*}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont step resource calibration C g) → Bool))
    (protocols : (g : Context) → Set (WordFrom Frag g))
    (J : (g : Context) → Finset (APFB06.Task (Cont step resource calibration C g) (D g)) →
      Set {p // p ∈ protocols g})
    (actualJoint :
      Set (Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g)))
    (reads : (h : Context) → Raw h → M → Bool) (m1 m2 : M)
    (hB06 : APFB06.AmendedB06_20260914 (Cont step resource calibration C) D protocols J
      (fun g p => resource g p.val) calibration C actualJoint)
    (hbridge : ∀ o : Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g),
      o ∈ actualJoint → ∀ p : {p // p ∈ protocols o.1}, p ∈ J o.1 o.2.carried →
        ∀ (x : Raw o.1) (y : Raw p.val.1), Executes step p.val.2 x y →
          reads p.val.1 y m1 = true ∧ reads p.val.1 y m2 = true) :
    ∃ (g : Context) (x : Raw g),
      APFPaper1.Regulation.JointlyHoldable step resource calibration C reads g x m1 m2 := by
  obtain ⟨o, ho, _, p, hp, hbill, x, y, hy⟩ :=
    APFB06.amendedB06_whole_word_reading step resource calibration C D protocols J actualJoint hB06
  obtain ⟨h1, h2⟩ := hbridge o ho p hp x y hy
  exact ⟨o.1, x, p.val, hbill, y, hy, h1, h2⟩


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5
theorem solution :
∀ {Context : Type apfNative_u_1} {Frag : Context → Context → Type apfNative_u_2} {Raw : Context → Type apfNative_u_3}
  {R : Context → Type apfNative_u_4} {M : Type apfNative_u_5} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
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
  (reads : (h : Context) → Raw h → M → Bool) (m1 m2 : M)
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
      calibration C actualJoint)
  (hbridge :
    ∀
      (o :
        @Sigma.{apfNative_u_1, apfNative_u_3} Context fun (g : Context) =>
          @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
            (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag Raw
              R step resource calibration C g)
            (D g)),
      @Membership.mem.{max apfNative_u_1 apfNative_u_3, max apfNative_u_1 apfNative_u_3}
          (@Sigma.{apfNative_u_1, apfNative_u_3} Context fun (g : Context) =>
            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag
                Raw R step resource calibration C g)
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
          actualJoint o →
        ∀
          (p :
            @Subtype.{(max apfNative_u_1 apfNative_u_2) + 1}
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
                p),
          @Membership.mem.{max apfNative_u_1 apfNative_u_2, max apfNative_u_1 apfNative_u_2}
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
              p →
            ∀
              (x :
                Raw
                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                    (fun (g : Context) =>
                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C g)
                        (D g))
                    o))
              (y :
                Raw
                  (@Sigma.fst.{apfNative_u_1, max apfNative_u_1 apfNative_u_2} Context
                    (fun (h : Context) =>
                      @APFPaper1.Continuation.Word.{apfNative_u_1, apfNative_u_2} Context Frag
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
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
                      p))),
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
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
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
                      p))
                  (@Sigma.snd.{apfNative_u_1, max apfNative_u_1 apfNative_u_2} Context
                    (fun (h : Context) =>
                      @APFPaper1.Continuation.Word.{apfNative_u_1, apfNative_u_2} Context Frag
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
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
                      p))
                  x y →
                And
                  (@Eq.{1} Bool
                    (reads
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
                      y m1)
                    Bool.true)
                  (@Eq.{1} Bool
                    (reads
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
                      y m2)
                    Bool.true)),
  @Exists.{apfNative_u_1 + 1} Context fun (g : Context) =>
    @Exists.{apfNative_u_3 + 1} (Raw g) fun (x : Raw g) =>
      @APFPaper1.Regulation.JointlyHoldable.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5}
        Context Frag Raw R M step resource calibration C reads g x m1 m2 := by
  exact @APFB06.occupant_jointly_held
