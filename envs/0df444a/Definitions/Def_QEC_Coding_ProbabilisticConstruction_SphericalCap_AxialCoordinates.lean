-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
-- name    : QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:48:08.8172+00:00
-- url     : https://prove2.me/theorems/d769bb93-7cec-44ed-97ee-2404ebddf89c
-- title:
--   Axial Coordinates
-- statement:
--   Definitions and structural lemmas for Axial Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/AxialCoordinates.lean

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev Transverse := EuclideanSpace ℝ (Fin 2)
noncomputable def axialEquiv : Ambient ≃ᵐ ℝ × Transverse :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))
noncomputable def axisReflection (u v : Ambient) : Ambient ≃ₗᵢ[ℝ] Ambient :=
  (ℝ ∙ (u - v))ᗮ.reflection
end QEC.Coding.ProbabilisticConstruction.SphericalCap


