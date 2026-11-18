-- Prove2me | Definitions.Def_Kyprianou_Ch09_GamePayoff
-- name    : Kyprianou_Ch09_GamePayoff
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:16:27.789207+00:00
-- url     : https://prove2.me/theorems/96da1d04-e979-480d-a6ff-90aafd39b26e
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner GamePayoff
-- statement:
--   Game payoff and stopping priority definitions. This source Definition module provides the actual declarations: ExtendedTime, ExtendedStoppingTime, FiniteStoppingTime, terminalAwareReward, gamePayoff. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch09.B1

/-- A finite or infinite stopping time on the nonnegative time axis. -/
abbrev ExtendedTime := WithTop ℝ≥0

/-- Filtration stopping-time predicate, including the possible infinity
required by the stochastic game in Section 9.6. -/
def ExtendedStoppingTime {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ExtendedTime) : Prop :=
  ∀ t : ℝ≥0,
    @MeasurableSet Ω (F t) {ω | τ ω ≤ (t : ExtendedTime)}

/-- A finite stopping time is represented separately, as required by
the Russian-option maximisation in Section 9.5. -/
def FiniteStoppingTime {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) : Prop :=
  ∀ t : ℝ≥0,
    @MeasurableSet Ω (F t) {ω | τ ω ≤ t}

/-- Discounted payoff for a finite stop; at infinity use a separate
specified terminal limit rather than forcing zero when q=0. -/
noncomputable def terminalAwareReward
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (G : ℝ → ℝ) (q : ℝ)
    (τ : ExtendedTime) (ω : Ω) (terminal : Ω → ℝ) : ℝ :=
  match τ with
  | ⊤ => terminal ω
  | (t : ℝ≥0) => Real.exp (-q * (t : ℝ)) * G (X t ω)

/-- The game uses gain-first precedence at simultaneous stopping:
G is paid on τ≤σ; H only for σ<τ. -/
noncomputable def gamePayoff
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (G H : ℝ → ℝ) (q : ℝ)
    (τ σ : Ω → ExtendedTime)
    (terminalG terminalH : Ω → ℝ) (ω : Ω) : ℝ :=
  if τ ω ≤ σ ω then
    terminalAwareReward X G q (τ ω) ω terminalG
  else
    terminalAwareReward X H q (σ ω) ω terminalH

/-- Verified game tie precedence is independent of jump arrival semantics. -/
theorem gamePayoff_tie
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (G H : ℝ → ℝ) (q : ℝ)
    (τ : Ω → ExtendedTime)
    (terminalG terminalH : Ω → ℝ) (ω : Ω) :
    gamePayoff X G H q τ τ terminalG terminalH ω =
      terminalAwareReward X G q (τ ω) ω terminalG := by
  simp [gamePayoff]

/-- Finite immediate stopping produces the gain G(X_0) even when the
opponent also stops immediately. -/
theorem gamePayoff_zero_tie
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (G H : ℝ → ℝ) (q : ℝ)
    (terminalG terminalH : Ω → ℝ) (ω : Ω) :
    gamePayoff X G H q (fun _ => (0 : ExtendedTime))
      (fun _ => (0 : ExtendedTime)) terminalG terminalH ω =
      G (X 0 ω) := by
  simp [gamePayoff, terminalAwareReward]

end Kyprianou.Ch09.B1


