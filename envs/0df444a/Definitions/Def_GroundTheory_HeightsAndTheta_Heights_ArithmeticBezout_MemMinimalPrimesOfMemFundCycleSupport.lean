-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemMinimalPrimesOfMemFundCycleSupport
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemMinimalPrimesOfMemFundCycleSupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:57:32.426279+00:00
-- url     : https://prove2.me/theorems/6b623343-ae9c-4042-a06d-ca910badcda0
-- title:
--   Mem Minimal Primes Of Mem Fund Cycle Support
-- statement:
--   Definitions and structural lemmas for Mem Minimal Primes Of Mem Fund Cycle Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MemMinimalPrimesOfMemFundCycleSupport.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ComplexFibreIdealBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar ptsIntegral pot)
def ConeIntegralPts.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (u : Fin n → ℂ),
    IsArithVar P (e + 1) → (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W) →
      cycleIntegral (ObjectsHeight.ofPointMatrix S hS) (fundCycle (complexFibreIdeal P)) e
          (fsLog (ObjectsHeight.ofPointMatrix S hS) u) =
        ptsIntegral P (pot fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
          (IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u)
end GroundTheory.Heights₂.Heights


