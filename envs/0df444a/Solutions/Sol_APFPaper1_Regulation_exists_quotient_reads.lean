-- Prove2me | solution 1 for APFPaper1.Regulation.exists_quotient_reads
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:08:42.898077+00:00
-- url     : https://prove2.me/submissions/7d6422da-3905-46cf-a9c2-374ae82d814e

/-
DRAFT (Claude seat, phone session 2026-11-13; not gated, not reviewed, not released, not built on the build box).
name: APFPaper1_regulation_reads_on_quotient
title: Regulation marks whose readings descend are distinctions on the B01 quotient, context by context
purpose: the re-pointing of `reads` to the B01 quotient that Def_APFPaper1_Regulation records as owed
 (check 13), done as a bridge and not as a re-registration: the Regulation definitions and the theorems
 stated over a supplied `reads` are left as they are.
named_hypothesis: hdesc, in every context the truth of each mark's reading descends to the physical
 quotient of that context. This is what B01 gives for a reading that is one of that context's original
 readout propositions (APFB01.exists_distinction_of_declaredInput); that identification is a source
 correspondence and is not proved here.
statement: there is one Boolean function per context and mark on the physical quotient of that context
 that every raw reading factors through, and Saves / SavesBoth can be read on it. Also: the empty word
 belongs to Cont g x exactly when it is within the budget of g (Supplement clause C1 in this encoding).
not_claimed: that the quotient function of a context is one of that context's tested distinctions (D g);
 any relation between the functions of two different contexts. The ledger has no transport between
 contexts, so "the same mark in another context" is whatever the supplied `reads` says it is.
-/
import Definitions.Def_APFPaper1_Regulation
import Theorems.Thm_APFB01_descends_iff_respects
import Theorems.Thm_APFB01_read_eq_of_descends
import Theorems.Thm_APFB01_exists_distinction_of_declaredInput

set_option autoImplicit false
open APFPaper1.Continuation

namespace APFPaper1.Regulation

universe uC uF uX uR uM
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}

theorem exists_quotient_reads
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (reads : (h : Context) → Raw h → M → Bool)
    (hdesc : ∀ (h : Context) (m : M),
      APFB01.Descends (Cont step resource calibration C h) (fun y : Raw h => reads h y m = true)) :
    ∃ d : (h : Context) → M → APFB01.PhysicalState (Cont step resource calibration C h) → Bool,
      ∀ (h : Context) (y : Raw h) (m : M),
        reads h y m = d h m (APFB01.physicalClass (Cont step resource calibration C h) y) :=
  ⟨fun h m => Quot.lift (fun y => reads h y m)
      (fun y z hyz => APFB01.read_eq_of_descends (Cont step resource calibration C h)
        (fun y => reads h y m) (hdesc h m) y z hyz),
    fun _ _ _ => rfl⟩

theorem saves_iff_quotient
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (reads : (h : Context) → Raw h → M → Bool)
    (d : (h : Context) → M → APFB01.PhysicalState (Cont step resource calibration C h) → Bool)
    (hd : ∀ (h : Context) (y : Raw h) (m : M),
      reads h y m = d h m (APFB01.physicalClass (Cont step resource calibration C h) y))
    (g : Context) (x : Raw g) (w : WordFrom Frag g) (m : M) :
    Saves step resource calibration C reads g x w m ↔
      calibration g (resource g w) ≤ C g ∧ ∃ y : Raw w.1, Executes step w.2 x y ∧
        d w.1 m (APFB01.physicalClass (Cont step resource calibration C w.1) y) = true := by
  constructor
  · rintro ⟨hb, y, hy, hr⟩
    exact ⟨hb, y, hy, by rw [← hd]; exact hr⟩
  · rintro ⟨hb, y, hy, hr⟩
    exact ⟨hb, y, hy, by rw [hd]; exact hr⟩

theorem savesBoth_iff_quotient
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (reads : (h : Context) → Raw h → M → Bool)
    (d : (h : Context) → M → APFB01.PhysicalState (Cont step resource calibration C h) → Bool)
    (hd : ∀ (h : Context) (y : Raw h) (m : M),
      reads h y m = d h m (APFB01.physicalClass (Cont step resource calibration C h) y))
    (g : Context) (x : Raw g) (w : WordFrom Frag g) (m1 m2 : M) :
    SavesBoth step resource calibration C reads g x w m1 m2 ↔
      calibration g (resource g w) ≤ C g ∧ ∃ y : Raw w.1, Executes step w.2 x y ∧
        d w.1 m1 (APFB01.physicalClass (Cont step resource calibration C w.1) y) = true ∧
        d w.1 m2 (APFB01.physicalClass (Cont step resource calibration C w.1) y) = true := by
  constructor
  · rintro ⟨hb, y, hy, h1, h2⟩
    exact ⟨hb, y, hy, by rw [← hd]; exact h1, by rw [← hd]; exact h2⟩
  · rintro ⟨hb, y, hy, h1, h2⟩
    exact ⟨hb, y, hy, by rw [hd]; exact h1, by rw [hd]; exact h2⟩

/-- Supplement clause C1 in this encoding: the empty word is a continuation of `x` exactly when it is
within the budget of its context. A remark sharpening the existing ledger theorem
`APFPaper1.Continuation.cont_identity` (zero bill suffices); not proposed as a separate node. -/
theorem cont_nullWord_iff
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) :
    Cont step resource calibration C g x (nullWord g) ↔
      calibration g (resource g (nullWord g)) ≤ C g :=
  ⟨fun h => h.2, fun h => ⟨⟨x, rfl⟩, h⟩⟩

end APFPaper1.Regulation

#print axioms APFPaper1.Regulation.exists_quotient_reads
#print axioms APFPaper1.Regulation.saves_iff_quotient
#print axioms APFPaper1.Regulation.savesBoth_iff_quotient
#print axioms APFPaper1.Regulation.cont_nullWord_iff


universe apfNative_uC apfNative_uF apfNative_uX apfNative_uR apfNative_uM
theorem solution :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uX}
  {R : Context → Type apfNative_uR} {M : Type apfNative_uM} (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → @APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (reads : (h : Context) → Raw h → M → Bool)
  (hdesc :
    ∀ (h : Context) (m : M),
      @APFB01.Descends.{apfNative_uX, max apfNative_uC apfNative_uF} (Raw h)
        (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag h)
        (@APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R step
          resource calibration C h)
        fun (y : Raw h) => @Eq.{1} Bool (reads h y m) Bool.true),
  @Exists.{max (max (apfNative_uC + 1) (apfNative_uM + 1)) (apfNative_uX + 1)}
    ((h : Context) →
      M →
        @APFB01.PhysicalState.{apfNative_uX, max apfNative_uC apfNative_uF} (Raw h)
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag h)
            (@APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R
              step resource calibration C h) →
          Bool)
    fun
      (d :
        (h : Context) →
          M →
            @APFB01.PhysicalState.{apfNative_uX, max apfNative_uC apfNative_uF} (Raw h)
                (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag h)
                (@APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw
                  R step resource calibration C h) →
              Bool) =>
    ∀ (h : Context) (y : Raw h) (m : M),
      @Eq.{1} Bool (reads h y m)
        (d h m
          (@APFB01.physicalClass.{apfNative_uX, max apfNative_uC apfNative_uF} (Raw h)
            (@APFPaper1.Continuation.WordFrom.{apfNative_uC, apfNative_uF} Context Frag h)
            (@APFPaper1.Continuation.Cont.{apfNative_uC, apfNative_uF, apfNative_uX, apfNative_uR} Context Frag Raw R
              step resource calibration C h)
            y)) := by
  exact @APFPaper1.Regulation.exists_quotient_reads
