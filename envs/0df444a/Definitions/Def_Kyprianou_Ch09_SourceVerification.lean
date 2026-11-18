-- Prove2me | Definitions.Def_Kyprianou_Ch09_SourceVerification
-- name    : Kyprianou_Ch09_SourceVerification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:18:35.975184+00:00
-- url     : https://prove2.me/theorems/d3d25347-2dc1-4006-9a6e-524ef19e95eb
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner SourceVerification
-- statement:
--   Verification and saddle-point propositions, with terminal and stopping-time conventions. This source Definition module provides the actual declarations: DiscountedRightContinuous, stoppedDiscountedValue, GamePayoffDomain, genericGameValue, verificationLemma, gameSaddleVerification. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceCore
import Definitions.Def_Kyprianou_Ch09_SourceValues
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09.B1

/-- Actual right-continuous sample paths for a discounted candidate value. -/
def DiscountedRightContinuous {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
    ContinuousWithinAt
      (fun s : ℝ≥0 => Real.exp (-q * (s : ℝ)) * v (x + X s ω))
      (Set.Ici t) t

/-- The process stopped at a potentially infinite stopping time is
evaluated at the source's finite t∧τ, without treating ∞ as zero. -/
noncomputable def stoppedDiscountedValue {Ω : Type}
    (X : ℝ≥0 → Ω → ℝ) (v : ℝ → ℝ)
    (q x : ℝ) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if τ ω ≤ (t : WithTop ℝ≥0) then
    match τ ω with
    | ⊤ => Real.exp (-q * (t : ℝ)) * v (x + X t ω)
    | (s : ℝ≥0) => Real.exp (-q * (s : ℝ)) * v (x + X s ω)
  else Real.exp (-q * (t : ℝ)) * v (x + X t ω)

/-- Source gambling constraints for continuous positive lower/upper payoffs. -/
def GamePayoffDomain (G H : ℝ → ℝ) : Prop :=
  Continuous G ∧ Continuous H ∧
  (∀ x, 0 ≤ G x ∧ G x < H x)

/-- Generic lower Dynkin-game value for the actual G/H payoff at all
finite and infinite admissible stopping times. -/
noncomputable def genericGameValue {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (G H : ℝ → ℝ) (q x : ℝ)
    (terminalG terminalH : Ω → ℝ) : ℝ :=
  sSup {a : ℝ | ∃ τ : Ω → WithTop ℝ≥0, AdmissibleStop F τ ∧
    a = sInf {b : ℝ | ∃ σ : Ω → WithTop ℝ≥0, AdmissibleStop F σ ∧
      b = ∫ ω, gameGain X G H q x terminalG terminalH τ σ ω ∂P}}

end Kyprianou.Ch09.B1

namespace Kyprianou.Ch09

/-- Theorem 9.1, complete source verification proposition. The martingale
and candidate-attainment premises are exactly its mathematical hypotheses,
rather than an assumed optimality conclusion. -/
noncomputable def verificationLemma : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (q : ℝ) (G : ℝ → ℝ)
    (vstar : ℝ → ℝ)
    (τstar : ℝ → Ω → WithTop ℝ≥0)
    (terminal : ℝ → Ω → ℝ)
    (hModel : B1.SourceModel P X F)
    (hq : 0 ≤ q) (hG : Measurable G)
    (hGpos : ∀ z, 0 ≤ G z)
    (hTerminal : ∀ x, ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 =>
        Real.exp (-q * (t : ℝ)) * G (x + X t ω))
        atTop (nhds (terminal x ω)))
    (hCandidate : ∀ x, B1.AdmissibleStop F (τstar x) ∧
      vstar x = ∫ ω, B1.stoppedGain X G q x
        (terminal x) (τstar x) ω ∂P)
    (hLower : ∀ x, G x ≤ vstar x)
    (hRC : B1.DiscountedRightContinuous P X q vstar)
    (hSuper : ∀ x : ℝ,
      Supermartingale
        (fun (t : ℝ≥0) ω => Real.exp (-q * (t : ℝ)) * vstar (x + X t ω)) F P),
    ∀ x : ℝ,
      B1.optionValue P F X G q x (terminal x) = vstar x

/-- Theorem 9.13 source game-verification lemma with all six clauses and
the τ≤σ payoff precedence, allowing both stopping times to be infinite. -/
noncomputable def gameSaddleVerification : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (G H vstar : ℝ → ℝ)
    (τstar σstar : ℝ → Ω → WithTop ℝ≥0)
    (terminalG terminalH : ℝ → Ω → ℝ)
    (hModel : B1.SourceModel P X F)
    (hq : 0 ≤ q) (hGH : B1.GamePayoffDomain G H)
    (hTerminalG : ∀ x, ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 =>
        Real.exp (-q * (t : ℝ)) * G (x + X t ω))
        atTop (nhds (terminalG x ω)))
    (hUpperIntegral : ∀ x : ℝ,
      Integrable (fun ω => sSup {z : ℝ | ∃ t : ℝ≥0,
        z = Real.exp (-q * (t : ℝ)) * H (x + X t ω)}) P)
    (hτ : ∀ x, B1.AdmissibleStop F (τstar x))
    (hσ : ∀ x, B1.AdmissibleStop F (σstar x))
    (hLower : ∀ x, G x ≤ vstar x)
    (hUpper : ∀ x, vstar x ≤ H x)
    (hMeetG : ∀ x, ∀ᵐ ω ∂P,
      (τstar x ω ≠ ⊤) →
      (∀ t : ℝ≥0, τstar x ω = (t : WithTop ℝ≥0) →
        vstar (x + X t ω) = G (x + X t ω)))
    (hMeetH : ∀ x, ∀ᵐ ω ∂P,
      (σstar x ω ≠ ⊤) →
      (∀ t : ℝ≥0, σstar x ω = (t : WithTop ℝ≥0) →
        vstar (x + X t ω) = H (x + X t ω)))
    (hSub : ∀ x : ℝ,
      Submartingale
        (B1.stoppedDiscountedValue X vstar q x (τstar x)) F P)
    (hSuper : ∀ x : ℝ,
      Supermartingale
        (B1.stoppedDiscountedValue X vstar q x (σstar x)) F P)
    (hRCtau : ∀ x : ℝ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 =>
          B1.stoppedDiscountedValue X vstar q x (τstar x) s ω)
        (Set.Ici t) t)
    (hRCsigma : ∀ x : ℝ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 =>
          B1.stoppedDiscountedValue X vstar q x (σstar x) s ω)
        (Set.Ici t) t),
    ∀ x : ℝ,
      B1.genericGameValue P F X G H q x (terminalG x) (terminalH x) =
        vstar x ∧
      (∀ τ σ : Ω → WithTop ℝ≥0,
        B1.AdmissibleStop F τ → B1.AdmissibleStop F σ →
        (∫ ω, B1.gameGain X G H q x
          (terminalG x) (terminalH x) τ (σstar x) ω ∂P) ≤
        (∫ ω, B1.gameGain X G H q x
          (terminalG x) (terminalH x) (τstar x) (σstar x) ω ∂P) ∧
        (∫ ω, B1.gameGain X G H q x
          (terminalG x) (terminalH x) (τstar x) (σstar x) ω ∂P) ≤
        (∫ ω, B1.gameGain X G H q x
          (terminalG x) (terminalH x) (τstar x) σ ω ∂P))

end Kyprianou.Ch09


