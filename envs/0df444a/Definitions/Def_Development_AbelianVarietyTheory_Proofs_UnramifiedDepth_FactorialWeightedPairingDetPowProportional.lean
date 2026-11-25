-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportional
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportional
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:07:05.603961+00:00
-- url     : https://prove2.me/theorems/ed3b4db8-b39e-403d-9132-501ab7de2d4e
-- title:
--   Factorial Weighted Pairing Det Pow Proportional
-- statement:
--   Definitions and structural lemmas for Factorial Weighted Pairing Det Pow Proportional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FactorialWeightedPairingDetPowProportional.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPolynomial
namespace GlobalTheory.DetPowPairing
section General
variable {C : Type} [CommRing C] {κ : Type}
noncomputable def pairing (F : MvPolynomial κ C) : MvPolynomial κ C →ₗ[C] C :=
  ∑ A ∈ F.support, (coeff A F * (A.prod fun _ e => (e.factorial : C))) • lcoeff C A
end General
variable {C : Type} [CommRing C] {n : ℕ}
end GlobalTheory.DetPowPairing


