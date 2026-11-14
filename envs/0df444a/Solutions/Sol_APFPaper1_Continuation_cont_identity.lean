-- Prove2me | solution 1 for APFPaper1.Continuation.cont_identity
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:36:20.784256+00:00
-- url     : https://prove2.me/submissions/3106ca40-10ad-40e8-9466-aa00543a9b28

/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFPaper1.Continuation.cont_identity
title: The empty word is a continuation from every raw possibility and reaches that possibility only (C1)
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1228 (C1), 1240 (reach remark), 2889-2891 (zero bill of the empty protocol).
consumes: no declared input. Named hypothesis: the empty word of the context has zero calibrated bill.
statement: Under the zero-bill hypothesis the empty word of g is in Cont g x for every x, and it executes from x to z exactly when x = z.
label: theorem with one named hypothesis (hnull). Capacity is nonnegative by type.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

/-- C1 with its reach. If the empty word of `g` has zero calibrated bill (the Supplement's convention,
2889-2891, here a named hypothesis), then it belongs to `Cont g x` for every `x`, and it reaches `x` and
nothing else. -/
theorem cont_identity (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g)
    (hnull : calibration g (resource g (nullWord g)) = 0) :
    Cont step resource calibration C g x (nullWord g) ∧
      ∀ z : Raw g, Executes step (Word.nil g) x z ↔ x = z := by
  refine ⟨⟨⟨x, rfl⟩, ?_⟩, fun z => Iff.rfl⟩
  rw [hnull]
  exact zero_le

end APFPaper1.Continuation


universe uC uF uX uR
theorem solution :
∀ {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX} {R : Context → Type uR}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → APFPaper1.Continuation.WordFrom.{uC, uF} Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (g : Context) (x : Raw g),
  Eq.{1} (calibration g (resource g (APFPaper1.Continuation.nullWord.{uC, uF} g))) 0 →
    APFPaper1.Continuation.Cont.{uC, uF, uX, uR} step resource calibration C g x
        (APFPaper1.Continuation.nullWord.{uC, uF} g) ∧
      ∀ (z : Raw g),
        APFPaper1.Continuation.Executes.{uC, uF, uX} step (APFPaper1.Continuation.Word.nil.{uC, uF} g) x z ↔
          Eq.{uX + 1} x z := by
  exact @APFPaper1.Continuation.cont_identity
