-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalZeta
-- name    : GroundTheory_LocalFields_LocalZeta
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:20:27.013672+00:00
-- url     : https://prove2.me/theorems/1ef605dc-6103-5c2c-8d8e-c440375d2944
-- title:
--   Local Zeta
-- statement:
--   Definitions and structural lemmas for Local Zeta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
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
section Identity
end Identity
section Helpers
end Helpers
variable [MeasurableSpace K] [BorelSpace K]
section Epsilon
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}
end Epsilon
section Uniqueness
variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}
end Uniqueness
section FunctionalEquation
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ
end FunctionalEquation
end GroundTheory.LocalField


