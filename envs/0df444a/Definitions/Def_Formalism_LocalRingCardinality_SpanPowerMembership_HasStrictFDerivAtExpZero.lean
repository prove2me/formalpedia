-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:38:57.210384+00:00
-- url     : https://prove2.me/theorems/7f2f58e1-95e0-4a8b-b7a8-e771502b19b9
-- title:
--   Has Strict FDeriv At Exp Zero
-- statement:
--   Definitions and structural lemmas for Has Strict FDeriv At Exp Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HasStrictFDerivAtExpZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.CD
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
theorem hasStrictFDerivAt_exp_zero_alt : HasStrictFDerivAt (exp : 𝔸 → 𝔸)
    ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
  have h := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)
  exact h
variable (𝔸) in

def logA : 𝔸 → 𝔸 := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse _ _ _
def F1 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp (-p.1) * exp (p.1 + p.2))
def F2 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp p.1 * exp p.2)
end Formalism.BasicNotions.Examples₂.CD


