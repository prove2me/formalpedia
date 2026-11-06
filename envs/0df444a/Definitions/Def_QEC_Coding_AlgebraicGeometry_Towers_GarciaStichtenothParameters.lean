-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
-- name    : QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:41:56.653563+00:00
-- url     : https://prove2.me/theorems/c625a733-0b7d-4383-934f-c31566439e8b
-- title:
--   Garcia Stichtenoth Parameters
-- statement:
--   Definitions and structural lemmas for Garcia Stichtenoth Parameters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/GarciaStichtenothParameters.lean

import Mathlib
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
def oddGenus (r : ℕ) : ℕ :=
  33 * 32 ^ (2 * r + 2) - 34 * 32 ^ (r + 1) + 1
def evenGenus (r : ℕ) : ℕ :=
  33 * 32 ^ (2 * r + 3) - 561 * 32 ^ (r + 1) + 1
def selectedPlaceCount (g : ℕ) : ℕ :=
  123 * g / 4
def selectedDivisorDegree (g : ℕ) : ℕ :=
  9 * g / 2
def selectedLogicalCount (g : ℕ) : ℕ :=
  5 * g / 4
def selectedDecodingRadius (g : ℕ) : ℕ :=
  g / 8
def selectedAuxiliaryDegree (g : ℕ) : ℕ :=
  9 * g / 8
def selectedCodeDimension (g : ℕ) : ℕ :=
  selectedDivisorDegree g + 1 - g
def selectedDistanceLowerBound (g : ℕ) : ℕ :=
  selectedDivisorDegree g - selectedLogicalCount g - 2 * g + 2
def selectedPhysicalLengthLowerBound (g : ℕ) : ℕ :=
  114 * g / 4 - 3
def selectedPhysicalLengthUpperBound (g : ℕ) : ℕ :=
  118 * g / 4 - 1
def selectedEvaluationPlaceLowerBound (g : ℕ) : ℕ :=
  selectedPlaceCount g - 2 - g
def selectedEvaluationPlaceUpperBound (g : ℕ) : ℕ :=
  selectedPlaceCount g - 2
def selectedEDegree (g : ℕ) : ℕ :=
  selectedPlaceCount g - 4 + g - 7 * selectedDivisorDegree g
def oddPlaceLowerBound (r : ℕ) : ℕ :=
  1023 * 32 ^ (2 * r + 2) + 64
def evenPlaceLowerBound (r : ℕ) : ℕ :=
  1023 * 32 ^ (2 * r + 3) + 64
end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters


