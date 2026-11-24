-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:49.255888+00:00
-- url     : https://prove2.me/theorems/8d424023-9dc1-4d25-a741-10035619213c
-- title:
--   St Rat Sheet No Chart Null
-- statement:
--   Definitions and structural lemmas for St Rat Sheet No Chart Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StRatSheetNoChartNull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RatChartObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix
def RatSheetNoChartNull.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ComplexSets.IsFiniteProjection J A →
    (∀ y, (RatChart.ratFibre J p q y).Finite) →
      volume (RatChart.ratMap p q ''
        {x | x ∈ ComplexSets.zeroSet J ∧ (∃ s, RatChart.IsRatSheetAt J p q x s) ∧
          ¬ ∃ s', IsSheetAt J A x s'}) = 0
end GroundTheory.Heights₂.Heights


