-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:33:32.801399+00:00
-- url     : https://prove2.me/theorems/721e2874-6700-54a2-84f2-c341d1f5fdbf
-- title:
--   Norm Le One Iff Is Integral Elem Of Equiv
-- statement:
--   Definitions and structural lemmas for Norm Le One Iff Is Integral Elem Of Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/NormLeOneIffIsIntegralElemOfEquiv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum
def IntegralOnModelRat : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 ℚ) R] [Module.Flat (𝓞 ℚ) R]
    [Algebra.FiniteType (𝓞 ℚ) R] [IsIntegrallyClosed R] (r g : R) (s : 𝓞 ℚ),
    FourB.IntegralOnModel.Hyp ℚ R r g s → ∃ r' : R, r = algebraMap (𝓞 ℚ) R s * r'
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB


