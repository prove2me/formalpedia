-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaQExpansionIntegral
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaQExpansionIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:47.725597+00:00
-- url     : https://prove2.me/theorems/3b276948-f0a1-4d13-b222-bba28f458788
-- title:
--   Delta QExpansion Integral
-- statement:
--   Definitions and structural lemmas for Delta QExpansion Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/DeltaQExpansionIntegral.lean

import Mathlib
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
open UpperHalfPlane ModularForm EisensteinSeries PowerSeries ArithmeticFunction
open scoped MatrixGroups ArithmeticFunction.sigma
noncomputable section
def DeltaQExpansionIntegral.Statement : Prop :=
  ∃ D : PowerSeries ℤ, constantCoeff D = 1 ∧
    qExpansion 1 ModularForm.discriminant = map (Int.castRingHom ℂ) (X * D)
namespace DeltaQExpansionIntegral
def sigmaSeries (k : ℕ) : PowerSeries ℤ := mk fun n ↦ (σ k n : ℤ)
def cSeries : PowerSeries ℤ := mk fun n ↦ (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)
end DeltaQExpansionIntegral
end
end GroundTheory.Heights₂.Heights.ChowlaSelberg


