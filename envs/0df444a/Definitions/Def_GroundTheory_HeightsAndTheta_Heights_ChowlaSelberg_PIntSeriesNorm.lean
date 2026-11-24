-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesNorm
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:52.621274+00:00
-- url     : https://prove2.me/theorems/22a7572d-f909-45d1-bbc7-34060f2de83a
-- title:
--   PInt Series Norm
-- statement:
--   Definitions and structural lemmas for PInt Series Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesNorm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries
open scoped Real
noncomputable section
namespace IntSeriesNorm
theorem intSeriesEval_one (z : ℂ) : intSeriesEval 1 z = 1 := by
  rw [intSeriesEval, tsum_eq_single 0]
  · simp
  · intro n hn; simp [coeff_one, hn]
def residuePart (F : PowerSeries ℤ) (p i : ℕ) : PowerSeries ℤ :=
  mk fun m ↦ coeff (m * p + i) F
def evalHom (S : Subring (PowerSeries ℤ)) (z : ℂ)
    (hmul : ∀ F G : S, intSeriesEval ((F : PowerSeries ℤ) * G) z =
      intSeriesEval F z * intSeriesEval G z)
    (hhas : ∀ F : S, HasSum (fun n ↦ ((coeff n (F : PowerSeries ℤ) : ℤ) : ℂ) * z ^ n)
      (intSeriesEval F z)) : S →+* ℂ where
  toFun f := intSeriesEval f z
  map_one' := by simp only [Subring.coe_one, intSeriesEval_one]
  map_mul' F G := by simp only [Subring.coe_mul]; exact hmul F G
  map_zero' := by simp [intSeriesEval]
  map_add' F G := by
    have h := hhas (F + G)
    simp only [Subring.coe_add, map_add, Int.cast_add, add_mul] at h
    exact h.unique ((hhas F).add (hhas G))
def normMatrix (F : PowerSeries ℤ) (p : ℕ) [NeZero p] : Matrix (Fin p) (Fin p) (PowerSeries ℤ) :=
  Matrix.of fun i k ↦ (if i ≤ k then 1 else X) * residuePart F p ((k - i : Fin p) : ℕ)
end IntSeriesNorm
end
end GroundTheory.Heights₂.Heights.ChowlaSelberg


