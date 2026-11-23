-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:49.936929+00:00
-- url     : https://prove2.me/theorems/df800638-f6d0-43af-b0d6-f251df809b1f
-- title:
--   Truncated Gaussian Integral Uniform Pos Semidef
-- statement:
--   Definitions and structural lemmas for Truncated Gaussian Integral Uniform Pos Semidef, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
namespace GlobalTheory.TruncGauss
noncomputable def qf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (w : V n) : ℂ :=
  ∑ j, ∑ l, A j l * w j * (starRingEnd ℂ) (w l)
end GlobalTheory.TruncGauss


