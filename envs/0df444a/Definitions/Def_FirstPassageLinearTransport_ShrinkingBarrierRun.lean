-- Prove2me | Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
-- name    : FirstPassageLinearTransport_ShrinkingBarrierRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:10:57.025907+00:00
-- url     : https://prove2.me/theorems/2454dcd9-cbd6-58ca-8c1d-60caee4aac52
-- title:
--   Shrinking Barrier Run
-- statement:
--   Definitions and structural lemmas for Shrinking Barrier Run, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos

set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
structure ShrinkingBarrierRunData where
  rHi : ℚ
  rLo : ℚ
  rStar : ℚ
  tau : ℝ
  etaLo : ℝ
  D : ℝ
  pHi : StageSetup (rHi : ℝ) tau
  pLo : StageSetup (rLo : ℝ) etaLo
  D_pos : 0 < D
  tau_lt_a0 : tau < a0
  etaLo_lt_a0 : etaLo < a0
  rStar_eq : rStar = min rHi rLo
  rStar_pos : 0 < rStar
def shrinkingHighTolerance
    (P : ShrinkingBarrierRunData) (M m : ℕ) : ℝ :=
  if m = 0 then P.tau
  else min P.tau
    (P.D * Real.sqrt (Real.log ((M : ℝ) + 2) / (m : ℝ)))
theorem shrinkingHighTolerance_pos
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    0 < shrinkingHighTolerance P M m := by
  unfold shrinkingHighTolerance
  split_ifs with hm
  · exact P.pHi.eta_pos
  · apply lt_min P.pHi.eta_pos
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hlog : 0 < Real.log ((M : ℝ) + 2) := by
      apply Real.log_pos
      have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith
    exact mul_pos P.D_pos (Real.sqrt_pos.2 (div_pos hlog hm0))
theorem shrinkingHighTolerance_le_tau
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    shrinkingHighTolerance P M m ≤ P.tau := by
  unfold shrinkingHighTolerance
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _
def shrinkingHighSetup
    (P : ShrinkingBarrierRunData) (M m : ℕ) :
    StageSetup (P.rHi : ℝ) (shrinkingHighTolerance P M m) :=
  P.pHi.lowerTolerance (shrinkingHighTolerance P M m)
    (shrinkingHighTolerance_pos P M m)
    (shrinkingHighTolerance_le_tau P M m)
inductive ShrinkingRecertificationRun
    (P : ShrinkingBarrierRunData) (M S n : ℕ) : ℕ → ℕ → Prop
  | first
      (hSM : S ≤ M) (hM0 : P.pHi.M0 ≤ M)
      (hnShell : n ∈ dyadicShell M)
      (hnGood : n ∈ initialWindowGood (shrinkingHighTolerance P M M)) :
      ShrinkingRecertificationRun P M S n
        (stageLength (shrinkingHighSetup P M M) n)
        (rationalTargetRank P.rHi M)
  | nextHi {elapsed qPrev m : ℕ}
      (hrun : ShrinkingRecertificationRun P M S n elapsed qPrev)
      (hSm : S ≤ m) (hm0 : P.pHi.M0 ≤ m)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hsourceGood : orbit elapsed n ∈
        initialWindowGood (shrinkingHighTolerance P M m))
      (hgap : rationalTargetRank P.rHi m < qPrev) :
      ShrinkingRecertificationRun P M S n
        (elapsed + stageLength (shrinkingHighSetup P M m) (orbit elapsed n))
        (rationalTargetRank P.rHi m)
  | nextLo {elapsed qPrev m : ℕ}
      (hrun : ShrinkingRecertificationRun P M S n elapsed qPrev)
      (hmS : m < S) (hm0 : P.pLo.M0 ≤ m)
      (hsourceShell : orbit elapsed n ∈ dyadicShell m)
      (hsourceGood : orbit elapsed n ∈ initialWindowGood P.etaLo)
      (hgap : rationalTargetRank P.rLo m < qPrev) :
      ShrinkingRecertificationRun P M S n
        (elapsed + stageLength P.pLo (orbit elapsed n))
        (rationalTargetRank P.rLo m)
end
end FirstPassageLinearTransport


