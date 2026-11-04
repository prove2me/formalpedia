-- Prove2me | Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
-- name    : Submission_ThreeSum_FiniteMomentZeroDetector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:41:05.912502+00:00
-- url     : https://prove2.me/theorems/7ea654f9-894a-4c4a-af8b-5ad5518547ee
-- title:
--   Finite Moment Zero Detector
-- statement:
--   Definitions and structural lemmas for Finite Moment Zero Detector, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
set_option autoImplicit false
namespace ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
def moment {t : ℕ} (v w : Fin t → ℤ) (k : ℕ) : ℤ :=
  ∑ s, w s * v s^k
def hankel {t : ℕ} (v w : Fin t → ℤ) (d : ℕ) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j => moment v w (i.val+j.val)
def powerTable {t : ℕ} (v : Fin t → ℤ) (d : ℕ) : Matrix (Fin t) (Fin d) ℤ :=
  fun s i => v s^i.val
def modifiedMoment {t : ℕ} (v w : Fin t → ℤ) (a : ℤ) (k : ℕ) : ℤ :=
  moment v w (k+2)-2*a*moment v w (k+1)+a^2*moment v w k
def modifiedHankel {t : ℕ} (v w : Fin t → ℤ) (a : ℤ) (d : ℕ) :
    Matrix (Fin d) (Fin d) ℤ := fun i j => modifiedMoment v w a (i.val+j.val)
end ThreeSum.FiniteMomentZeroDetector


