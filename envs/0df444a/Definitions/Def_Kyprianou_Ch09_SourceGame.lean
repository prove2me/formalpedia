-- Prove2me | Definitions.Def_Kyprianou_Ch09_SourceGame
-- name    : Kyprianou_Ch09_SourceGame
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:21:13.01055+00:00
-- url     : https://prove2.me/theorems/c7900c76-598a-45d8-b29c-57577446060b
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner SourceGame
-- statement:
--   Two-player stopping-game propositions and penalty regime conditions. This source Definition module provides the actual declarations: firstStrictAbove, penalisedPutGame, PutGameSaddle, putGameCandidate, putLowPenaltyValue, gameTwoPenaltyRegimes, gameStrictLowerComparison. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceCore
import Definitions.Def_Kyprianou_Ch09_SourceValues
import Definitions.Def_Kyprianou_Ch09_CriticalPenalty
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09.B1

/-- Source upper cancellation barrier is a strict first upcrossing of log K. -/
noncomputable def firstStrictAbove {Ω : Type}
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ s : ℝ≥0,
    0 < s ∧ a < X s ω ∧ t = (s : WithTop ℝ≥0)}

/-- Source's genuine penalised put game has terminal G=0 and terminal
H=δ for positive drift q=0. -/
noncomputable def penalisedPutGame {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (K δ x : ℝ) : ℝ :=
  putGameValue P F X K δ x (fun _ => 0) (fun _ => δ)

/-- Candidate verification of a saddle, including τ≤σ tie precedence. -/
def PutGameSaddle {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (K δ x : ℝ)
    (τstar σstar : Ω → WithTop ℝ≥0) : Prop :=
  AdmissibleStop F τstar ∧ AdmissibleStop F σstar ∧
    (∀ τ : Ω → WithTop ℝ≥0, AdmissibleStop F τ →
      (∫ ω, gameGain X (putGain K) (fun z => putGain K z + δ)
        0 x (fun _ => 0) (fun _ => δ) τ σstar ω ∂P) ≤
      (∫ ω, gameGain X (putGain K) (fun z => putGain K z + δ)
        0 x (fun _ => 0) (fun _ => δ) τstar σstar ω ∂P)) ∧
    (∀ σ : Ω → WithTop ℝ≥0, AdmissibleStop F σ →
      (∫ ω, gameGain X (putGain K) (fun z => putGain K z + δ)
        0 x (fun _ => 0) (fun _ => δ) τstar σstar ω ∂P) ≤
      (∫ ω, gameGain X (putGain K) (fun z => putGain K z + δ)
        0 x (fun _ => 0) (fun _ => δ) τstar σ ω ∂P))

/-- The integral candidate is defined for every log-price, including
a negative integration interval when it arises. -/
noncomputable def putGameCandidate (K psiOne z x : ℝ)
    (W : ℝ → ℝ) : ℝ :=
  K - Real.exp x +
    psiOne * Real.exp x *
      ∫ y in (0 : ℝ)..(x - z), Real.exp (-y) * W y

/-- Low-penalty value is explicitly piecewise at the real log-price log K. -/
noncomputable def putLowPenaltyValue (K psiOne z δ x : ℝ)
    (W : ℝ → ℝ) : ℝ :=
  if x < Real.log K then putGameCandidate K psiOne z x W else δ

end Kyprianou.Ch09.B1

namespace Kyprianou.Ch09

/-- Theorem 9.14: complete corrected two-regime Dynkin game. The same
critical penalty uses log(ψ(1)/ψ′(0+)) in both branches; δ=δcrit is high.
The lower boundary in the low regime is x*<z*<log K, never (0,K).
Nonzero finite-mean negative jumps remain in the source hypotheses. -/
noncomputable def gameTwoPenaltyRegimes : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ)
    (d : ℝ) (S : ℝ≥0 → Ω → ℝ) (jumpMeasure : Measure ℝ)
    (K δ : ℝ) (W : ℝ → ℝ)
    (hX : B1.SourceModel P X F)
    (hBV : B1.IsBVNegativeLevy P X ψ d S jumpMeasure)
    (hJump : jumpMeasure ≠ 0)
    (hMean : Integrable (fun ω => S 1 ω) P)
    (hDrift : 0 < (∫ ω, S 1 ω ∂P) ∧
      (∫ ω, S 1 ω ∂P) < d)
    (hPsi : 0 < ψ 1) (hK : 0 < K) (hδ : 0 < δ)
    (hW : B1.IsScale ψ 0 W),
    let ψprime := d - (∫ ω, S 1 ω ∂P)
    let zMcKean := B1.gameLowerBarrier K ψprime (ψ 1)
    let critical := B1.gameCriticalPenalty K ψprime (ψ 1) W
    (0 ≤ critical) ∧
    (critical ≤ δ →
      ∀ x : ℝ,
        B1.penalisedPutGame P F X K δ x =
          B1.putGameCandidate K (ψ 1) zMcKean x W ∧
        B1.PutGameSaddle P F X K δ x
          (fun ω => B1.firstStrictBelow
            (fun t ξ => x + X t ξ) zMcKean ω)
          (fun _ => ⊤)) ∧
    (0 < δ ∧ δ < critical →
      ∃! z : ℝ,
        zMcKean < z ∧ z < Real.log K ∧
        B1.gamePenaltyAt K (ψ 1) z W = δ ∧
        (∀ x : ℝ,
          B1.penalisedPutGame P F X K δ x =
            B1.putLowPenaltyValue K (ψ 1) z δ x W ∧
          B1.PutGameSaddle P F X K δ x
            (fun ω => B1.firstStrictBelow
              (fun t ξ => x + X t ξ) z ω)
            (fun ω => B1.firstStrictAbove
              (fun t ξ => x + X t ξ) (Real.log K) ω)))

/-- Lemma 9.15: strict lower comparison in the entire low-penalty region.
This is the genuine value candidate from 9.14(b), without assuming δ<v. -/
noncomputable def gameStrictLowerComparison : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ)
    (d : ℝ) (S : ℝ≥0 → Ω → ℝ) (jumpMeasure : Measure ℝ)
    (K δ : ℝ) (W : ℝ → ℝ)
    (hX : B1.SourceModel P X F)
    (hBV : B1.IsBVNegativeLevy P X ψ d S jumpMeasure)
    (hJump : jumpMeasure ≠ 0)
    (hMean : Integrable (fun ω => S 1 ω) P)
    (hDrift : 0 < (∫ ω, S 1 ω ∂P) ∧
      (∫ ω, S 1 ω ∂P) < d)
    (hPsi : 0 < ψ 1) (hK : 0 < K) (hδ : 0 < δ)
    (hW : B1.IsScale ψ 0 W),
    let ψprime := d - (∫ ω, S 1 ω ∂P)
    let zMcKean := B1.gameLowerBarrier K ψprime (ψ 1)
    let critical := B1.gameCriticalPenalty K ψprime (ψ 1) W
    δ < critical →
      ∀ z : ℝ, zMcKean < z → z < Real.log K →
        B1.gamePenaltyAt K (ψ 1) z W = δ →
        ∀ x : ℝ, x < Real.log K →
          δ < B1.putLowPenaltyValue K (ψ 1) z δ x W

end Kyprianou.Ch09


