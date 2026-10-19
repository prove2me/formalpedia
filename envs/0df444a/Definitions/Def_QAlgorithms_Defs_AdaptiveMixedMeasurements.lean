-- Prove2me | Definitions.Def_QAlgorithms_Defs_AdaptiveMixedMeasurements
-- name    : QAlgorithms_Defs_AdaptiveMixedMeasurements
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:34.290922+00:00
-- url     : https://prove2.me/theorems/0cba07b8-ed84-4a01-9d65-9f00c9fdb601
-- title:
--   AdaptiveMixedMeasurements
-- statement:
--   AdaptiveMixedMeasurements
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\AdaptiveMixedMeasurements.lean

import Definitions.Def_QAlgorithms_Defs_QuantumInstruments
noncomputable section

open scoped Matrix

namespace QAlgorithms.CopyMeasurements

variable {n m d k b w M K N c out : ℕ}

/-- Explicit finite adaptive physical procedure, 1711.01053 pp.12–16.
The input register persists across every branch; internal outcomes may be hidden
by returning the same output. The tree is chosen before the unknown state. -/
inductive AdaptiveMeasurementProcedure (I A : Type) [Fintype I] [DecidableEq I] where
  | output (a : A)
  | measure (o : ℕ) (M : QuantumInstrument I (Fin o))
      (next : Fin o → AdaptiveMeasurementProcedure I A)

/-- Unconditional terminal probability computed by Kraus/Lüders composition,
1711.01053 pp.12–16. No branch is postselected or renormalized. -/
def procedureLaw {I A : Type} [Fintype I] [DecidableEq I] [DecidableEq A] :
    AdaptiveMeasurementProcedure I A → Matrix I I ℂ → A → ℝ
  | .output a, X, b => if a = b then X.trace.re else 0
  | .measure _ M next, X, b => ∑ o, procedureLaw (next o) (instrumentBranch M o X) b

/-- Dual effects computed from the same physical procedure (1711.01053 p.13).
These are the induced POVM; completeness is a separate mathematical consequence. -/
def procedureEffect {I A : Type} [Fintype I] [DecidableEq I] [DecidableEq A] :
    AdaptiveMeasurementProcedure I A → A → Matrix I I ℂ
  | .output a, b => if a = b then 1 else 0
  | .measure _ M next, b => ∑ o, ∑ j, (M.kraus o j)ᴴ * procedureEffect (next o) b * M.kraus o j

/-- Sanity check for the modeled source objects (arxiv-1711.01053v2, PDF pp.2,12,13,16). -/
example {I A : Type} [Fintype I] [DecidableEq I] [DecidableEq A]
    (a : A) (X : Matrix I I ℂ) :
    procedureLaw (.output a : AdaptiveMeasurementProcedure I A) X a = X.trace.re := by
  simp [procedureLaw]

/-- Sanity check for the modeled source objects (arxiv-1711.01053v2, PDF pp.2,12,13,16). -/
example {I A : Type} [Fintype I] [DecidableEq I] [DecidableEq A]
    (a : A) (X : Matrix I I ℂ) :
    procedureLaw (.measure 1
      { multiplicity := fun _ => 1, kraus := fun _ _ => 1, complete := by simp }
      (fun _ => .output a) : AdaptiveMeasurementProcedure I A) X a = X.trace.re := by
  simp [procedureLaw, instrumentBranch, krausApply]

end QAlgorithms.CopyMeasurements


