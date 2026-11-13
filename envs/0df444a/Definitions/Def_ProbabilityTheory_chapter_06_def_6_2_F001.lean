-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
-- name    : ProbabilityTheory_chapter_06_def_6_2_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T20:03:44.789002+00:00
-- url     : https://prove2.me/theorems/e4c848cc-ee02-4a52-97a1-3a8f58b04608
-- title:
--   Chapter 6, def_6_2: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `def_6_2`: `def62_eq_some_iff`, `textbookERealAddDefined`, `textbookERealAdd`, `textbookIntegralAdd`, `simpleFunctionIntegralAddCompatible`, and 21 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_2.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]




def textbookERealAddDefined (x y : EReal) : Prop :=
  ¬ ((x = ⊤ ∧ y = ⊥) ∨ (x = ⊥ ∧ y = ⊤))

noncomputable def textbookERealAdd (x y : EReal) : Option EReal := by
  classical
  exact
    if h : textbookERealAddDefined x y then
      some (x + y)
    else
      none

noncomputable def textbookIntegralAdd (u v : Option EReal) : Option EReal := by
  classical
  exact
    match u, v with
    | some x, some y => textbookERealAdd x y
    | _, _ => none

def simpleFunctionIntegralAddCompatible (μ : Measure Ω)
    (X Y : SimpleFunc Ω EReal) : Prop :=
  ∀ p ∈ (X.pair Y).range,
    (p.1 + p.2) * (μ (X.pair Y ⁻¹' {p}) : EReal) =
      p.1 * (μ (X.pair Y ⁻¹' {p}) : EReal) +
        p.2 * (μ (X.pair Y ⁻¹' {p}) : EReal)

noncomputable def simpleFunctionIntegralAdd (μ : Measure Ω)
    (X Y : SimpleFunc Ω EReal) : Option EReal := by
  classical
  exact
    if h : simpleFunctionIntegralAddCompatible μ X Y then
      def_6_2 μ (X + Y)
    else
      none

noncomputable def textbookERealFinSum : (n : ℕ) → (Fin n → EReal) → Option EReal
  | 0, _ => some 0
  | n + 1, f => textbookIntegralAdd (some (f 0)) (textbookERealFinSum n fun i => f i.succ)










noncomputable def simpleFunctionIntegralFinChain (μ : Measure Ω) :
    (n : ℕ) → (Fin n → SimpleFunc Ω EReal) → Option EReal
  | 0, _ => some 0
  | n + 1, F =>
      match simpleFunctionIntegralFinChain μ n (fun i => F i.succ) with
      | some _ => simpleFunctionIntegralAdd μ (F 0) (∑ i : Fin n, F i.succ)
      | none => none







noncomputable def indicatorRepresentationSummand
    (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) :
    Fin n → SimpleFunc Ω EReal :=
  fun i => (SimpleFunc.const Ω (b i)).restrict (B i)

noncomputable def indicatorRepresentationSimpleFunction
    (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : SimpleFunc Ω EReal :=
  ∑ i : Fin n, indicatorRepresentationSummand (Ω := Ω) n b B i

noncomputable def indicatorRepresentationWeightedSum
    (μ : Measure Ω) (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : Option EReal :=
  textbookERealFinSum n fun i => b i * (μ (B i) : EReal)

noncomputable def indicatorRepresentationIntegral
    (μ : Measure Ω) (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : Option EReal :=
  simpleFunctionIntegralFinChain μ n (indicatorRepresentationSummand (Ω := Ω) n b B)

noncomputable def indicatorRepresentationIntegralChain
    (μ : Measure Ω) (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : Option EReal :=
  indicatorRepresentationIntegral (Ω := Ω) μ n b B


