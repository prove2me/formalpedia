-- Prove2me | Definitions.Def_QAlgorithms_Defs_OnlineThresholdSearch
-- name    : QAlgorithms_Defs_OnlineThresholdSearch
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:34.012197+00:00
-- url     : https://prove2.me/theorems/d1bfab0f-fc47-437b-8259-b027d6b7d460
-- title:
--   OnlineThresholdSearch
-- statement:
--   OnlineThresholdSearch
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\OnlineThresholdSearch.lean

import Definitions.Def_QAlgorithms_Defs_QuantumInstruments
noncomputable section

open scoped Matrix

namespace QAlgorithms.ThresholdSearch

variable {n m d k b w M K N c out : ℕ}

/-- A valid online effect/threshold pair, 2011.10908 p.3. -/
structure TestPair (d : ℕ) where
  effect : Matrix (Fin d) (Fin d) ℂ
  valid : IsEffect effect
  threshold : Set.Icc (0 : ℝ) 1

/-- Online protocol (2011.10908 pp.3,19–22): n copies are obtained once;
the stage rule receives only the prefix seen so far. The finite auxiliary
register may carry persistent classical memory and quantum work. -/
structure OnlineProtocol (d m n : ℕ) where
  aux : ℕ
  initial : Matrix (Fin aux) (Fin aux) ℂ
  initial_density : IsDensityMatrix initial
  stage : (t : Fin m) → (Fin (t.val + 1) → TestPair d) →
    CopyMeasurements.QuantumInstrument ((Fin n → Fin d) × Fin aux) Bool

/-- Retained subnormalized pass state after t tests, 2011.10908 p.22.
Invalid stages beyond m are identities. true selects; false passes. -/
def passState {d m n : ℕ} (P : OnlineProtocol d m n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (stream : Fin m → TestPair d) :
    ℕ → Matrix ((Fin n → Fin d) × Fin P.aux) ((Fin n → Fin d) × Fin P.aux) ℂ
  | 0 => Matrix.kronecker (piKron n rho) P.initial
  | t + 1 => if h : t < m then
      CopyMeasurements.instrumentBranch
        (P.stage ⟨t, h⟩ (fun i => stream ⟨i, by omega⟩)) false
        (passState P rho stream t)
    else passState P rho stream t

/-- Terminal law of the first-selection process, 2011.10908 pp.20,22.
No division by the probability of passing occurs. -/
def terminalLaw {d m n : ℕ} (P : OnlineProtocol d m n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (stream : Fin m → TestPair d) :
    Option (Fin m) → ℝ
  | none => (passState P rho stream m).trace.re
  | some t => (CopyMeasurements.instrumentBranch
      (P.stage t (fun i => stream ⟨i, by have := t.isLt; omega⟩)) true
      (passState P rho stream t)).trace.re

/-- Exact overlap-permitting terminal claims, 2011.10908 pp.3,20:
select means a strict lower threshold, none means all weak upper thresholds. -/
def IsCorrect {d m n : ℕ} (P : OnlineProtocol d m n) (eps delta : ℝ) : Prop := by
  classical
  exact ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
    ∀ stream : Fin m → TestPair d,
      (open Classical in
        ∑ o : Option (Fin m), if (match o with
          | none => ∀ i, effectProb (stream i).effect rho ≤ (stream i).threshold.val
          | some i => (stream i).threshold.val - eps < effectProb (stream i).effect rho)
        then terminalLaw P rho stream o else 0) ≥ 1 - delta

/-- Sanity check for the modeled source objects (arxiv-2011.10908v4, PDF pp.3,9,19,20,21,22). -/
example {d m n : ℕ} (P : OnlineProtocol d m n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (stream : Fin m → TestPair d) :
    passState P rho stream 0 = Matrix.kronecker (piKron n rho) P.initial := rfl

/-- Sanity check for the modeled source objects (arxiv-2011.10908v4, PDF pp.3,9,19,20,21,22). -/
example {d n : ℕ} (P : OnlineProtocol d 0 n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (stream : Fin 0 → TestPair d) :
    terminalLaw P rho stream none = (Matrix.kronecker (piKron n rho) P.initial).trace.re := rfl

end QAlgorithms.ThresholdSearch


