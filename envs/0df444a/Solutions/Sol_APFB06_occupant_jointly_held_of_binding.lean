-- Prove2me | solution 1 for APFB06.occupant_jointly_held_of_binding
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:58:36.939076+00:00
-- url     : https://prove2.me/submissions/a9439c9a-bab9-4baa-bff3-aed6543ec64b

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, phone session 2026-11-13; not gated, not reviewed,
 not released, not built on the build box).
name: APFB06_alignment_marks_held
title: The distinctions an alignment carries are jointly held at its carrier by the empty response
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1833-1848 (structural alignment: d(a) = 1 for every carried d), 1229 (C1, the
 trivial continuation belongs to Cont(x) for every x), 1850 (holding an instantiated alignment costs nothing);
 Def_APF_B06_DeclaredInput (OriginalAlignment.active); Def_APFPaper1_Regulation.
consumes_inputs: none in `alignment_marks_jointly_held`; B06 (AmendedB06_20260914) in the corollary, and only
 for the existence of an actual joint alignment.
named_hypotheses: hnull, the empty word of the alignment's context is within that context's budget (the
 whole-word form of Supplement clause C1; implied by the zero-bill hypothesis `hnull` of the existing ledger
 theorem APFPaper1.Continuation.cont_identity). hread1/hread2 (hbind in the corollary), the two marks read, in the
 alignment's context, as two of its carried distinctions on the B01 quotient: an identification of the marks,
 not a law about any protocol.
statement: for any alignment and any two of its carried distinctions there is a raw representative of the
 carrier at which the two marks are jointly holdable, the response being the empty word.
not_claimed: anything about the joint protocol class J or about where a J protocol ends; that the raw input
 supplied by B06's availability clause represents the carrier (Supplement 1883: it need not); any
 irreducibly joint disturbance; any value of a joint fraction below one.
-/
import Definitions.Def_APFPaper1_Regulation
import Definitions.Def_APF_B06_DeclaredInput

set_option autoImplicit false
open APFPaper1.Continuation

theorem APFB06.alignment_marks_jointly_held
    {Context : Type*} {Frag : Context → Context → Type*} {Raw : Context → Type*} {R : Context → Type*} {M : Type*}
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (D : (g : Context) → Set (APFB01.PhysicalState (Cont step resource calibration C g) → Bool))
    (reads : (h : Context) → Raw h → M → Bool) (m1 m2 : M)
    (g : Context) (a : APFB06.OriginalAlignment (Cont step resource calibration C g) (D g))
    (d1 d2 : APFB06.Task (Cont step resource calibration C g) (D g))
    (hd1 : d1 ∈ a.carried) (hd2 : d2 ∈ a.carried)
    (hnull : calibration g (resource g (nullWord g)) ≤ C g)
    (hread1 : ∀ y : Raw g,
      reads g y m1 = d1.val (APFB01.physicalClass (Cont step resource calibration C g) y))
    (hread2 : ∀ y : Raw g,
      reads g y m2 = d2.val (APFB01.physicalClass (Cont step resource calibration C g) y)) :
    ∃ x : Raw g, APFB01.physicalClass (Cont step resource calibration C g) x = a.carrier ∧
      APFPaper1.Regulation.JointlyHoldable step resource calibration C reads g x m1 m2 := by
  obtain ⟨x, hx⟩ := Quot.exists_rep a.carrier
  have hc : APFB01.physicalClass (Cont step resource calibration C g) x = a.carrier := hx
  have h1 : reads g x m1 = true := by
    rw [hread1 x, hc]; exact a.active d1 hd1
  have h2 : reads g x m2 = true := by
    rw [hread2 x, hc]; exact a.active d2 hd2
  exact ⟨x, hc, nullWord g, hnull, x, rfl, h1, h2⟩

/-- Under B06 there is an actual joint alignment, so two marks that read as carried distinctions of every
actual joint alignment are jointly holdable at some raw input. No endpoint bridge is used. -/
theorem APFB06.occupant_jointly_held_of_binding
    {Context : Type*} {Frag : Context → Context → Type*} {Raw : Context → Type*} {R : Context → Type*} {M : Type*}
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
    (hnull : ∀ g : Context, calibration g (resource g (nullWord g)) ≤ C g)
    (hbind : ∀ o : Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g),
      o ∈ actualJoint → ∃ d1 ∈ o.2.carried, ∃ d2 ∈ o.2.carried,
        (∀ y : Raw o.1,
          reads o.1 y m1 = d1.val (APFB01.physicalClass (Cont step resource calibration C o.1) y)) ∧
        (∀ y : Raw o.1,
          reads o.1 y m2 = d2.val (APFB01.physicalClass (Cont step resource calibration C o.1) y))) :
    ∃ (g : Context) (x : Raw g),
      APFPaper1.Regulation.JointlyHoldable step resource calibration C reads g x m1 m2 := by
  obtain ⟨o, ho, _⟩ := hB06
  obtain ⟨d1, hd1, d2, hd2, hr1, hr2⟩ := hbind o ho
  obtain ⟨x, _, hx⟩ := APFB06.alignment_marks_jointly_held step resource calibration C D reads m1 m2
    o.1 o.2 d1 d2 hd1 hd2 (hnull o.1) hr1 hr2
  exact ⟨o.1, x, hx⟩

/-- `hbridge` weakened to what the proof of `APFB06.occupant_jointly_held` uses: at an input where a protocol
of the joint class is available, SOME run of it ends where both marks read true. Implied by `hbridge`
(which asks it of every run from every raw input). The whole-word reading theorem is not needed. -/
theorem APFB06.occupant_jointly_held_of_some_run
    {Context : Type*} {Frag : Context → Context → Type*} {Raw : Context → Type*} {R : Context → Type*}
    {M : Type*}
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
    (hrun : ∀ o : Sigma fun g => APFB06.OriginalAlignment (Cont step resource calibration C g) (D g),
      o ∈ actualJoint → ∀ p : {p // p ∈ protocols o.1}, p ∈ J o.1 o.2.carried →
      ∀ x : Raw o.1, Cont step resource calibration C o.1 x p.val →
        ∃ y : Raw p.val.1, Executes step p.val.2 x y ∧
          reads p.val.1 y m1 = true ∧ reads p.val.1 y m2 = true) :
    ∃ (g : Context) (x : Raw g),
      APFPaper1.Regulation.JointlyHoldable step resource calibration C reads g x m1 m2 := by
  obtain ⟨o, ho, _, _, p, hp, x, hx⟩ := hB06
  obtain ⟨y, hy, h1, h2⟩ := hrun o ho p hp x hx
  exact ⟨o.1, x, p.val, hx.2, y, hy, h1, h2⟩

#print axioms APFB06.alignment_marks_jointly_held
#print axioms APFB06.occupant_jointly_held_of_binding
#print axioms APFB06.occupant_jointly_held_of_some_run


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
  (hnull :
    ∀ (g : Context),
      @LE.le.{0} NNReal (@Preorder.toLE.{0} NNReal (@PartialOrder.toPreorder.{0} NNReal NNReal.instPartialOrder))
        (calibration g (resource g (@APFPaper1.Continuation.nullWord.{apfNative_u_1, apfNative_u_2} Context Frag g)))
        (C g))
  (hbind :
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
        @Exists.{apfNative_u_3 + 1}
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
          fun
            (d1 :
              @APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag
                  Raw R step resource calibration C
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
                    o))) =>
          And
            (@Membership.mem.{apfNative_u_3, apfNative_u_3}
              (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag
                  Raw R step resource calibration C
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
                    o)))
              (Finset.{apfNative_u_3}
                (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                      o))))
              (@SetLike.instMembership.{apfNative_u_3, apfNative_u_3}
                (Finset.{apfNative_u_3}
                  (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                        o))))
                (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                      o)))
                (@Finset.instSetLike.{apfNative_u_3}
                  (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                        o)))))
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
                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag
                  Raw R step resource calibration C
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
                      (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context
                        Frag Raw R step resource calibration C g)
                      (D g))
                  o))
              d1)
            (@Exists.{apfNative_u_3 + 1}
              (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Context Frag
                  Raw R step resource calibration C
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
                    o)))
              fun
                (d2 :
                  @APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                        o))) =>
              And
                (@Membership.mem.{apfNative_u_3, apfNative_u_3}
                  (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                        o)))
                  (Finset.{apfNative_u_3}
                    (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                          o))))
                  (@SetLike.instMembership.{apfNative_u_3, apfNative_u_3}
                    (Finset.{apfNative_u_3}
                      (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                        (Raw
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o))
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
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o))
                        (D
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o))))
                    (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
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
                          o)))
                    (@Finset.instSetLike.{apfNative_u_3}
                      (@APFB06.Task.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                        (Raw
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o))
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
                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                          Context Frag Raw R step resource calibration C
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o))
                        (D
                          (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                            (fun (g : Context) =>
                              @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C g)
                                (D g))
                            o)))))
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
                      o))
                  d2)
                (And
                  (∀
                    (y :
                      Raw
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o)),
                    @Eq.{1} Bool
                      (reads
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o)
                        y m1)
                      (@Subtype.val.{apfNative_u_3 + 1}
                        (@APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                            (Raw
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
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
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o)) →
                          Bool)
                        (fun
                            (d :
                              @APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                  (Raw
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
                                      o))
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
                                      o))
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C
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
                                      o)) →
                                Bool) =>
                          @Membership.mem.{apfNative_u_3, apfNative_u_3}
                            (@APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                (Raw
                                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                    (fun (g : Context) =>
                                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                              apfNative_u_4}
                                          Context Frag Raw R step resource calibration C g)
                                        (D g))
                                    o))
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
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C
                                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                    (fun (g : Context) =>
                                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                              apfNative_u_4}
                                          Context Frag Raw R step resource calibration C g)
                                        (D g))
                                    o)) →
                              Bool)
                            (Set.{apfNative_u_3}
                              (@APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                  (Raw
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
                                      o))
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
                                      o))
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C
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
                                      o)) →
                                Bool))
                            (@Set.instMembership.{apfNative_u_3}
                              (@APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                  (Raw
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
                                      o))
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
                                      o))
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C
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
                                      o)) →
                                Bool))
                            (D
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
                            d)
                        d1
                        (@APFB01.physicalClass.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                          (Raw
                            (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                              (fun (g : Context) =>
                                @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C g)
                                  (D g))
                              o))
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
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C
                            (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                              (fun (g : Context) =>
                                @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C g)
                                  (D g))
                              o))
                          y)))
                  (∀
                    (y :
                      Raw
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o)),
                    @Eq.{1} Bool
                      (reads
                        (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                          (fun (g : Context) =>
                            @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                              (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                              (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                                Context Frag Raw R step resource calibration C g)
                              (D g))
                          o)
                        y m2)
                      (@Subtype.val.{apfNative_u_3 + 1}
                        (@APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                            (Raw
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
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
                            (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                              Context Frag Raw R step resource calibration C
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o)) →
                          Bool)
                        (fun
                            (d :
                              @APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                  (Raw
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
                                      o))
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
                                      o))
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C
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
                                      o)) →
                                Bool) =>
                          @Membership.mem.{apfNative_u_3, apfNative_u_3}
                            (@APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                (Raw
                                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                    (fun (g : Context) =>
                                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                              apfNative_u_4}
                                          Context Frag Raw R step resource calibration C g)
                                        (D g))
                                    o))
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
                                (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                      apfNative_u_4}
                                  Context Frag Raw R step resource calibration C
                                  (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                    (fun (g : Context) =>
                                      @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                        (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                        (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                              apfNative_u_4}
                                          Context Frag Raw R step resource calibration C g)
                                        (D g))
                                    o)) →
                              Bool)
                            (Set.{apfNative_u_3}
                              (@APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                  (Raw
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
                                      o))
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
                                      o))
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C
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
                                      o)) →
                                Bool))
                            (@Set.instMembership.{apfNative_u_3}
                              (@APFB01.PhysicalState.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                                  (Raw
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
                                      o))
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
                                      o))
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C
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
                                      o)) →
                                Bool))
                            (D
                              (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                                (fun (g : Context) =>
                                  @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                    (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                    (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                          apfNative_u_4}
                                      Context Frag Raw R step resource calibration C g)
                                    (D g))
                                o))
                            d)
                        d2
                        (@APFB01.physicalClass.{apfNative_u_3, max apfNative_u_1 apfNative_u_2}
                          (Raw
                            (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                              (fun (g : Context) =>
                                @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C g)
                                  (D g))
                              o))
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
                          (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
                            Context Frag Raw R step resource calibration C
                            (@Sigma.fst.{apfNative_u_1, apfNative_u_3} Context
                              (fun (g : Context) =>
                                @APFB06.OriginalAlignment.{apfNative_u_3, max apfNative_u_1 apfNative_u_2} (Raw g)
                                  (@APFPaper1.Continuation.WordFrom.{apfNative_u_1, apfNative_u_2} Context Frag g)
                                  (@APFPaper1.Continuation.Cont.{apfNative_u_1, apfNative_u_2, apfNative_u_3,
                                        apfNative_u_4}
                                    Context Frag Raw R step resource calibration C g)
                                  (D g))
                              o))
                          y)))))),
  @Exists.{apfNative_u_1 + 1} Context fun (g : Context) =>
    @Exists.{apfNative_u_3 + 1} (Raw g) fun (x : Raw g) =>
      @APFPaper1.Regulation.JointlyHoldable.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5}
        Context Frag Raw R M step resource calibration C reads g x m1 m2 := by
  exact @APFB06.occupant_jointly_held_of_binding
