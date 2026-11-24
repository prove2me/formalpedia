-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:48.016015+00:00
-- url     : https://prove2.me/theorems/11adfbdb-8353-46aa-96e6-8775c92d9454
-- title:
--   Lower Bound Conditional
-- statement:
--   Definitions and structural lemmas for Lower Bound Conditional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
def BaseChangeLogBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e δ : ℕ) (h : HermNorm n)
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → K)
    (σ : K →+* ℂ),
    IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f → linForm u ∉ I →
      cycleIntegral h (fundCycle (I.map (MvPolynomial.map σ))) e (fsLog h fun j => σ (u j)) ≤
        δ * Real.log (h.norm fun j => σ (u j))
section Lemmas
variable {R : Type*} [CommRing R]
variable {k n : ℕ}
end Lemmas
section Components
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type*} [CommRing R] {n : ℕ}
variable [IsNoetherianRing R]
end Components
section Height
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
end Height
end
end GroundTheory.Heights₂.Heights


