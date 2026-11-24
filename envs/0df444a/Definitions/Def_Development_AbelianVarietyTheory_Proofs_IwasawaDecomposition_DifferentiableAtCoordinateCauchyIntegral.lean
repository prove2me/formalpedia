-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtCoordinateCauchyIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtCoordinateCauchyIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:03.286726+00:00
-- url     : https://prove2.me/theorems/868f3436-c0be-4c8f-a96e-a944af9e9710
-- title:
--   Differentiable At Coordinate Cauchy Integral
-- statement:
--   Definitions and structural lemmas for Differentiable At Coordinate Cauchy Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtCoordinateCauchyIntegral.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
noncomputable section
namespace GlobalTheory
def updCLM (n : ℕ) (k : Fin n) : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if i = k then ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ
    else (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)
end GlobalTheory


