-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Sec3_Parameters
-- name    : Submission_ThreeSumApsp_Sec3_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:07:43.826786+00:00
-- url     : https://prove2.me/theorems/1579f1ac-82dd-4ead-ba1c-ca8a270b12c8
-- title:
--   Parameters
-- statement:
--   Definitions and structural lemmas for Parameters, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Sec3/Parameters.lean

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option autoImplicit false
section
namespace ThreeSumApsp
noncomputable def TriangleInstance.totalChunks {n : ℕ} (T : TriangleInstance ℤ n) (D p : ℕ) : ℕ :=
  ∑ ϱ : Fin p, numChunks (T.residueClass p ϱ) (queryCap n D)
def DivNondecreasing (T : ℕ → ℝ) : Prop :=
  ∀ s₁ s₂ : ℕ, 1 ≤ s₁ → s₁ ≤ s₂ → T s₁ / s₁ ≤ T s₂ / s₂
def GoodTime (T : ℕ → ℝ → ℝ) : Prop :=
  (∀ (s : ℕ) (u : ℝ), 1 ≤ s → (s : ℝ) ^ 2 * (1 + logU u) ≤ T s u) ∧
    ∀ u : ℝ, DivNondecreasing fun s => T s u
noncomputable def uniformTime (K δ : ℝ) (e : ℕ) (s : ℕ) (u : ℝ) : ℝ :=
  K * ((s : ℝ) ^ (3 - δ) * (Real.log s + 1) ^ e * (1 + logU u) ^ 2)
noncomputable def termScans (n g : ℕ) (κ : ℝ) : ℝ := κ * (n : ℝ) ^ 3 * Real.log n / (g : ℝ)
noncomputable def termPrime (MM : ℕ → ℝ) (n D : ℕ) : ℝ := MM n * (D : ℝ) ^ (3 / 2 : ℝ)
noncomputable def termBuild (n D g : ℕ) : ℝ := (n : ℝ) ^ 2 * (D : ℝ) * (g : ℝ)
noncomputable def strassen (n : ℕ) : ℝ := (n : ℝ) ^ Real.logb 2 7
noncomputable def paramD₅ (n : ℕ) : ℕ := 4 ^ Nat.log 4 ⌊(n : ℝ) ^ (1 / 18 : ℝ)⌋₊
noncomputable def paramG₅ (n : ℕ) : ℕ := ⌈(paramD₅ n : ℝ) ^ (1 / 36 : ℝ)⌉₊
noncomputable def paramD₂₆ (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 18 : ℝ)⌋₊
noncomputable def paramG₂₆ (n : ℕ) : ℕ := ⌈(paramD₂₆ n : ℝ) ^ (0.0315 : ℝ)⌉₊
noncomputable def splitCap (n D : ℕ) : ℕ := max 1 (queryCap n D)
end ThreeSumApsp


