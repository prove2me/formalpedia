-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_04_def_4_4_complex_number
-- name    : ProbabilityTheory_chapter_04_def_4_4_complex_number
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:59:37.309271+00:00
-- url     : https://prove2.me/theorems/9fbd9f21-f3bb-4647-818f-55f99bfa8793
-- title:
--   Chapter ?, generated supplement: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter ?, source module `generated supplement`: `complexRealPart`, `complexImagPart`, `complexToPair`, `pairToComplex`, `complexEquivRealProd`, and 9 others. The mathematical interpretation of this bundle needs review.
-- source:
--   Supplemental source module in importer v37; upstream repository https://github.com/wkshum/ProbabilityTheory/tree/e6387d4fd8005d627d2aec40d10f039ddb4e4b40

import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic

def complexRealPart (z : ℂ) : ℝ := z.re

def complexImagPart (z : ℂ) : ℝ := z.im

def complexToPair (z : ℂ) : ℝ × ℝ := (z.re, z.im)

def pairToComplex (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

noncomputable def complexEquivRealProd : ℂ ≃ ℝ × ℝ :=
  Complex.equivRealProd

noncomputable def complexHomeomorphRealProd : Homeomorph ℂ (ℝ × ℝ) :=
  Complex.equivRealProdCLM.toHomeomorph

noncomputable def complexMeasurableEquivRealProd : ℂ ≃ᵐ (ℝ × ℝ) :=
  complexHomeomorphRealProd.toMeasurableEquiv

def complexOpenRectangle (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

theorem pairToComplex_complexToPair (z : ℂ) : pairToComplex (complexToPair z) = z := by
  apply Complex.ext <;> simp [pairToComplex, complexToPair]

theorem complexToPair_pairToComplex (p : ℝ × ℝ) : complexToPair (pairToComplex p) = p := by
  cases p
  simp [pairToComplex, complexToPair]

theorem measurable_complexToPair : Measurable complexToPair := by
  change Measurable (fun z : ℂ => (z.re, z.im))
  exact Complex.continuous_re.measurable.prodMk Complex.continuous_im.measurable

theorem measurable_pairToComplex : Measurable pairToComplex := by
  have h : Measurable (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
    fun_prop
  change Measurable (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
  exact h

theorem isOpen_complexOpenRectangle (a b c d : ℝ) : IsOpen (complexOpenRectangle a b c d) := by
  change IsOpen ({z : ℂ | a < z.re} ∩ ({z : ℂ | z.re < b} ∩
    ({z : ℂ | c < z.im} ∩ {z : ℂ | z.im < d})))
  exact
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))

theorem measurableSet_complexOpenRectangle (a b c d : ℝ) :
    MeasurableSet (complexOpenRectangle a b c d) :=
  (isOpen_complexOpenRectangle a b c d).measurableSet


