-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:04.010185+00:00
-- url     : https://prove2.me/theorems/16771965-9721-45e5-b135-e3d19b9635d1
-- title:
--   Is KMeas
-- statement:
--   Definitions and structural lemmas for Is KMeas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsKMeas.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ENNReal
noncomputable section
namespace GlobalTheory.HCXi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
def Kset (k r : ℕ) : Set (Mat k r) := {g | g ∈ GV k r ∧ gᴴ * g = 1}
def isoVec (k r : ℕ) : Fin (2 * r + k + 1) → ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (bvec (wI k r 0) + bvec (wI k r (Fin.last k)))
def frame (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i a => fvec k r (isoVec k r) a i
def Pset (k r : ℕ) : Set (Mat k r) :=
  {p | p ∈ GV k r ∧ ∃ u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
    u.BlockTriangular id ∧ p * frame k r = frame k r * u}
def gram (k r : ℕ) (g : Mat k r) (a : Fin (r + 1)) : ℝ :=
  (((g * frame k r)ᴴ * (g * frame k r)).submatrix (Fin.castLE (Nat.succ_le_of_lt a.isLt))
    (Fin.castLE (Nat.succ_le_of_lt a.isLt))).det.re
def vHalf (k r : ℕ) (g : Mat k r) : ℝ :=
  (∏ a : Fin r, (gram k r g a.castSucc)⁻¹) * gram k r g (Fin.last r) ^ (-((k : ℝ) / 2))
def IsKMeas (k r : ℕ) (μK : Measure (Mt k r)) : Prop := IsHaarOn (Kset k r) μK ∧ μK Set.univ = 1
def XiE (k r : ℕ) (μK : Measure (Mt k r)) (g : Mat k r) : ℝ≥0∞ :=
  ∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (g * Matrix.of κ)) ∂μK
def Xi (k r : ℕ) (μK : Measure (Mt k r)) (g : Mat k r) : NNReal := (XiE k r μK g).toNNReal
def sqLen {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (v i)
end GlobalTheory.HCXi


