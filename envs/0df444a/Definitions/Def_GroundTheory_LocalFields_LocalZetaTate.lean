-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
-- name    : GroundTheory_LocalFields_LocalZetaTate
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T10:06:24.958308+00:00
-- url     : https://prove2.me/theorems/daa3649b-3f53-40f6-ba7d-a03256be0f99
-- title:
--   Local Zeta Tate
-- statement:
--   Definitions and structural lemmas for Local Zeta Tate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaTate.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
section Symmetric
variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
include hψ
end Symmetric
section Multiplicative
variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
include hψ
end Multiplicative
section Tate
variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
  (hψ1 : ψ ≠ 1) {χ : Kˣ →* ℂˣ} (hχ : Continuous χ)
include hψ hψ1 hχ
end Tate
end GroundTheory.LocalField


