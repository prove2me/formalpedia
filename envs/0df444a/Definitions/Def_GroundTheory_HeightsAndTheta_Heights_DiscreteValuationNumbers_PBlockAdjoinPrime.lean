-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlockAdjoinPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlockAdjoinPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:59.080778+00:00
-- url     : https://prove2.me/theorems/a8195e3d-3cd4-4901-b1f4-5ff58a7f148d
-- title:
--   PBlock Adjoin Prime
-- statement:
--   Definitions and structural lemmas for PBlock Adjoin Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace BlockAdjoinPrime
variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
open Classical in

def killB (B : Set K) : MRing ι R →ₐ[R] MRing ι R :=
  aeval fun v => if v.1 ∈ B then 0 else X v
def varIdeal (B : Set K) : Ideal (MRing ι R) :=
  Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B ∧ p = X v}
variable [DecidableEq K]
end BlockAdjoinPrime
end
end GroundTheory.Heights₂.Heights.NumbersDVR


