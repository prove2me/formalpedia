-- Prove2me | solution 1 for APFPaper1.Continuation.cont_prefix
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:37:44.742205+00:00
-- url     : https://prove2.me/submissions/9538a1a2-a108-478b-bef3-27d36aa3f0cd

/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFPaper1.Continuation.cont_prefix
title: An initial segment of a continuation is a continuation when its calibrated resource does not exceed that of the whole (C3, conditional)
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1230 (C3), 2209-2214 (monotone calibration), 3301 (fragment-monotone budgets: hypothesized, not derived).
consumes: no declared input. Named hypothesis: PrefixMonotone, or pointwise the bill comparison hbill. This hypothesis is NOT an adopted input.
statement: C3 in pointwise form and under PrefixMonotone; the hereditary class is contained in the whole-word class; the two coincide under PrefixMonotone; the whole-word class is closed under initial segments exactly when it coincides with the hereditary class.
label: CONDITIONAL. Not by definition. Author ruling 2026-11-12, item 1. The hypothesis cannot be dropped: Reference/Ref_APFPaper1_Cont_prefix_countermodel.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

/-- C3, pointwise form. An initial segment `v` of a word `w` in `Cont g x` is in `Cont g x` provided the
calibrated resource of `v` is at most that of `w`. Without the bill comparison the conclusion can fail
(see Reference/Ref_APFPaper1_Cont_prefix_countermodel). -/
theorem cont_prefix_of_bill_le (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (v w : WordFrom Frag g) (hpre : IsPrefix v w)
    (hw : Cont step resource calibration C g x w)
    (hbill : calibration g (resource g v) ≤ calibration g (resource g w)) :
    Cont step resource calibration C g x v :=
  ⟨isPrefix_executes step v w hpre x hw.1, le_trans hbill hw.2⟩

/-- C3 under prefix-monotone calibrated resource (named hypothesis `hmono`). -/
theorem cont_prefix (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (hmono : PrefixMonotone resource calibration)
    (g : Context) (x : Raw g) (v w : WordFrom Frag g) (hpre : IsPrefix v w)
    (hw : Cont step resource calibration C g x w) :
    Cont step resource calibration C g x v :=
  cont_prefix_of_bill_le step resource calibration C g x v w hpre hw (hmono g v w hpre)

/-! ### 5. Hereditary and whole-word classes -/

/-- The hereditary class is contained in the whole-word class. No hypothesis. -/
theorem cont_of_contHereditary (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (w : WordFrom Frag g)
    (hw : ContHereditary step resource calibration C g x w) :
    Cont step resource calibration C g x w :=
  ⟨hw.1, hw.2 w (isPrefix_refl w)⟩

/-- Under prefix-monotone calibrated resource the two classes coincide. -/
theorem contHereditary_iff_cont (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (hmono : PrefixMonotone resource calibration)
    (g : Context) (x : Raw g) (w : WordFrom Frag g) :
    ContHereditary step resource calibration C g x w ↔ Cont step resource calibration C g x w :=
  ⟨cont_of_contHereditary step resource calibration C g x w,
    fun hw => ⟨hw.1, fun v hv => le_trans (hmono g v w hv) hw.2⟩⟩

/-- Exact characterisation. The whole-word class is closed under initial segments (C3 holds for it) if and
only if it coincides with the hereditary class. So under the whole-word reading, C3 says exactly that every
initial segment of a member has calibrated resource at most the capacity; prefix-monotone resource is sufficient for
that and is not claimed necessary. -/
theorem prefix_closed_iff_hereditary (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) :
    (∀ (g : Context) (x : Raw g) (v w : WordFrom Frag g), IsPrefix v w →
        Cont step resource calibration C g x w → Cont step resource calibration C g x v) ↔
    (∀ (g : Context) (x : Raw g) (w : WordFrom Frag g),
        Cont step resource calibration C g x w ↔ ContHereditary step resource calibration C g x w) := by
  constructor
  · intro hC3 g x w
    exact ⟨fun hw => ⟨hw.1, fun v hv => (hC3 g x v w hv hw).2⟩,
      cont_of_contHereditary step resource calibration C g x w⟩
  · intro hEq g x v w hpre hw
    exact ⟨isPrefix_executes step v w hpre x hw.1, ((hEq g x w).mp hw).2 v hpre⟩

/-- Prefix-monotone calibrated resource from two ingredients: a monotone calibration, which is the Supplement's
definition of a context calibration (2209-2214, source vocabulary), and a resource preorder in which an initial
segment never carries more load than the whole word. The second ingredient was not found in the Supplement
passages read; it is the exact missing implication behind C3. -/
theorem prefixMonotone_of_resource_mono [∀ g, Preorder (R g)]
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (hcal : ∀ (g : Context) (a b : R g), a ≤ b → calibration g a ≤ calibration g b)
    (hres : ∀ (g : Context) (v w : WordFrom Frag g), IsPrefix v w → resource g v ≤ resource g w) :
    PrefixMonotone resource calibration :=
  fun g v w hpre => hcal g _ _ (hres g v w hpre)

end APFPaper1.Continuation


universe uC uF uX uR
theorem solution :
∀ {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX} {R : Context → Type uR}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → APFPaper1.Continuation.WordFrom.{uC, uF} Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal),
  APFPaper1.Continuation.PrefixMonotone.{uC, uF, uR} resource calibration →
    ∀ (g : Context) (x : Raw g) (v w : APFPaper1.Continuation.WordFrom.{uC, uF} Frag g),
      APFPaper1.Continuation.IsPrefix.{uC, uF} v w →
        APFPaper1.Continuation.Cont.{uC, uF, uX, uR} step resource calibration C g x w →
          APFPaper1.Continuation.Cont.{uC, uF, uX, uR} step resource calibration C g x v := by
  exact @APFPaper1.Continuation.cont_prefix
