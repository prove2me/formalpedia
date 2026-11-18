-- Prove2me | Definitions.Def_Kyprianou_Ch09_LevyInterface
-- name    : Kyprianou_Ch09_LevyInterface
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:16:44.424595+00:00
-- url     : https://prove2.me/theorems/2a106971-90f2-4969-b3d2-72dbf435e5c0
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner LevyInterface
-- statement:
--   Underlying Lévy-process interface declarations and stochastic path assumptions. This source Definition module provides the actual declarations: SourceLevy, pathSup, pathInf, discountedGain, strictLowerPassageEvent, weakUpperPassageEvent, reflectedDrawdown, McKeanDiscountDomain, Exercise91DiscountDomain. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_levy_foundations_isLevyProcess
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch09.B1

/-- Source's actual Lévy process, with independent stationary increments
and almost-everywhere càdlàg paths. Published reference retained exactly. -/
def SourceLevy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  LevyFoundations.IsLevyProcess X P

/-- Finite physical-horizon running supremum of a Lévy sample path. -/
noncomputable def pathSup {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  sSup ((fun s : ℝ≥0 => X s ω) '' Set.Icc 0 t)

/-- Finite physical-horizon running infimum of a Lévy sample path. -/
noncomputable def pathInf {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  sInf ((fun s : ℝ≥0 => X s ω) '' Set.Icc 0 t)

/-- Source gain uses the real-valued payoff of the actual process. -/
noncomputable def discountedGain {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (G : ℝ → ℝ) (q : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-q * (t : ℝ)) * G (X t ω)

/-- Strict first lower passage event; its time and infinity convention
remain separately open before full stopping-time formalisation. -/
def strictLowerPassageEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : Set ℝ≥0 :=
  {t | 0 < t ∧ X t ω < a}

/-- Weak first upper passage event, including time zero. -/
def weakUpperPassageEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : Set ℝ≥0 :=
  {t | a ≤ X t ω}

/-- Original reflected drawdown process, including time-zero maximum. -/
noncomputable def reflectedDrawdown {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max x (pathSup X t ω) - X t ω

/-- Chapter 9, Theorem 9.2: the q=0 put assumption has positive drift
and therefore a finite global downward running infimum. -/
def McKeanDiscountDomain {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (q : ℝ) : Prop :=
  0 < q ∨ (q = 0 ∧ ∀ᵐ ω ∂P,
    Filter.Tendsto (fun t : ℝ≥0 => X t ω) Filter.atTop Filter.atTop)

/-- The different Exercise 9.1 q=0 assumption requires negative drift
for the upward-supremum stopping reward. -/
def Exercise91DiscountDomain {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (q : ℝ) : Prop :=
  0 < q ∨ (q = 0 ∧ ∀ᵐ ω ∂P,
    Filter.Tendsto (fun t : ℝ≥0 => X t ω) Filter.atTop Filter.atBot)

end Kyprianou.Ch09.B1


