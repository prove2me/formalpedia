-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqZeroOfForallLeExp
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqZeroOfForallLeExp
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:54:43.970795+00:00
-- url     : https://prove2.me/theorems/ba9a975b-074e-4ad4-a42d-4da29495cccd
-- title:
--   Eq Zero Of Forall Le Exp
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Forall Le Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqZeroOfForallLeExp.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousOfValuationEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open WithZero
namespace GlobalTheory.DenseCompl
section DVR
variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]
noncomputable def closedPoint (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] :
    HeightOneSpectrum W :=
  ⟨IsLocalRing.maximalIdeal W, inferInstance, IsDiscreteValuationRing.not_a_field W⟩
end DVR
end GlobalTheory.DenseCompl


