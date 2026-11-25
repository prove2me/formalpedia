-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocalRing
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocalRing
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:41.588437+00:00
-- url     : https://prove2.me/theorems/a93c9229-4eca-5d40-bafa-93396b310d33
-- title:
--   Statements Deg Zero Local Ring
-- statement:
--   Definitions and structural lemmas for Statements Deg Zero Local Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLocalRing.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
def DegZeroLocalRing.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)), IsMultiProjPrime W → P ≤ W →
    haveI := hP.isPrime
    (IsNoetherianRing (degZeroLoc P {W}) ∧ IsLocalRing (degZeroLoc P {W})) ∧
      ∀ n : ℕ, relDim P = (n + 1 : ℕ) → relDim W = (n : ℕ) → ringKrullDim (degZeroLoc P {W}) = 1
end
end GroundTheory.Heights₂.Heights.FieldNumbers


