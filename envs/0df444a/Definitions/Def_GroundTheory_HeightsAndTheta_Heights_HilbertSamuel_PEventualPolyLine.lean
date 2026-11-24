-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:54.630649+00:00
-- url     : https://prove2.me/theorems/10c79158-675e-4dc6-9ba1-84a0853a16e8
-- title:
--   PEventual Poly Line
-- statement:
--   Definitions and structural lemmas for PEventual Poly Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
namespace EventualPolyLine
variable {K : Type}
def lineRestrict [Fintype K] (a c : K → ℚ) (p : MvPolynomial K ℚ) : ℚ[X] :=
  MvPolynomial.aeval (fun k => C (a k) * X + C (c k)) p
def topCoeff [Fintype K] (D : ℕ) (a : K → ℚ) (p : MvPolynomial K ℚ) : ℚ :=
  ∑ s ∈ p.support, p.coeff s * if ∑ k, s k = D then ∏ k, a k ^ s k else 0
end EventualPolyLine
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


