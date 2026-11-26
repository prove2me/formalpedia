-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutRun
-- name    : FirstPassageLinearTransport_TimeoutRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:16:31.788447+00:00
-- url     : https://prove2.me/theorems/43a3a75b-d53b-495f-bb85-7bcf804a1246
-- title:
--   Timeout Run
-- statement:
--   Definitions and structural lemmas for Timeout Run, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos

set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable section
structure TimeoutHighRunData where
  rHi : ℚ
  tau : ℝ
  D : ℝ
  pHi : StageSetup (rHi : ℝ) tau
  D_pos : 0 < D
  tau_lt_a0 : tau < a0
def ShrinkingBarrierRunData.toTimeoutHigh
    (P : ShrinkingBarrierRunData) : TimeoutHighRunData where
  rHi := P.rHi
  tau := P.tau
  D := P.D
  pHi := P.pHi
  D_pos := P.D_pos
  tau_lt_a0 := P.tau_lt_a0
def timeoutHighTolerance
    (P : TimeoutHighRunData) (M m : ℕ) : ℝ :=
  if m = 0 then P.tau
  else min P.tau
    (P.D * Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)))
theorem timeoutHighTolerance_pos
    (P : TimeoutHighRunData) (M m : ℕ) :
    0 < timeoutHighTolerance P M m := by
  unfold timeoutHighTolerance
  split_ifs with hm
  · exact P.pHi.eta_pos
  · apply lt_min P.pHi.eta_pos
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hlog : 0 < Real.log ((M : ℝ) + 2) := by
      apply Real.log_pos
      have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    exact mul_pos P.D_pos (Real.sqrt_pos.2 (div_pos hlog hm0))
theorem timeoutHighTolerance_le_tau
    (P : TimeoutHighRunData) (M m : ℕ) :
    timeoutHighTolerance P M m ≤ P.tau := by
  unfold timeoutHighTolerance
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _
def timeoutHighSetup
    (P : TimeoutHighRunData) (M m : ℕ) :
    StageSetup (P.rHi : ℝ) (timeoutHighTolerance P M m) :=
  P.pHi.lowerTolerance (timeoutHighTolerance P M m)
    (timeoutHighTolerance_pos P M m)
    (timeoutHighTolerance_le_tau P M m)
structure LowTimeoutPassage (K₀ : ℝ) (L m x : ℕ) where
  duration : ℕ
  duration_le : duration ≤ m
  firstPassage :
    IsFirstPassage (2 ^ timeoutTargetRank K₀ L m) x duration
inductive TimeoutRecertificationRun
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (L M S n : ℕ) : ℕ → ℕ → Prop
  | first
      (hSM : S ≤ M) (hM0 : P.pHi.M0 ≤ M)
      (hnShell : n ∈ dyadicShell M)
      (hnGood : n ∈ initialWindowGood (timeoutHighTolerance P M M)) :
      TimeoutRecertificationRun P K₀ L M S n
        (stageLength (timeoutHighSetup P M M) n)
        (rationalTargetRank P.rHi M)
  | nextHi {elapsed qPrev m : ℕ}
      (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed qPrev)
      (hSm : S ≤ m) (hm0 : P.pHi.M0 ≤ m)
      (hmPrev : qPrev = m + 1)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hsourceGood : orbit elapsed n ∈
        initialWindowGood (timeoutHighTolerance P M m))
      (hgap : rationalTargetRank P.rHi m < qPrev) :
      TimeoutRecertificationRun P K₀ L M S n
        (elapsed + stageLength (timeoutHighSetup P M m) (orbit elapsed n))
        (rationalTargetRank P.rHi m)
  | nextLo {elapsed qPrev m : ℕ}
      (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed qPrev)
      (hmS : m < S) (hLm : L ≤ m)
      (hmPrevLo : m ≤ qPrev) (hmPrevHi : qPrev ≤ m + 1)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hpass : LowTimeoutPassage K₀ L m (orbit elapsed n))
      (hqpos : 0 < timeoutTargetRank K₀ L m)
      (hqparent : timeoutTargetRank K₀ L m < m)
      (hgap : timeoutTargetRank K₀ L m < qPrev) :
      TimeoutRecertificationRun P K₀ L M S n
        (elapsed + hpass.duration) (timeoutTargetRank K₀ L m)
end
end FirstPassageLinearTransport


