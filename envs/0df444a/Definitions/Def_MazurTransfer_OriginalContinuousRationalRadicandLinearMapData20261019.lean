-- Prove2me | Definitions.Def_MazurTransfer_OriginalContinuousRationalRadicandLinearMapData20261019
-- name    : MazurTransfer_OriginalContinuousRationalRadicandLinearMapData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T00:26:45.467107+00:00
-- url     : https://prove2.me/theorems/f1d7b53f-0d79-45e1-b05a-2135369fec4d
-- title:
--   Original continuous rational radicand linear map
-- statement:
--   Retain the original rational radicand additive group homomorphism and F19 linear map on the original continuous H1 submodule with its same given representative family. Use the separately accepted original zero and addition laws. Both complete constructor types and whole values, fifty-one context types, thirty-five whole values, all three original record kernel schemas and the recursor computation rule are checked independently. The complete original zero and addition proof types are checked separately. Named downstream consumer: the actual selected pi Selmer injective rational radicand map and numerical support bound.
-- source:
--   MazurTheorem ContinuousRationalRadicandMap by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: construct the original rational radicand group homomorphism and F19 linear map from the same original representative family and power-class value, using the separately accepted original zero and addition laws.
Named downstream consumer: the original selected pi Selmer injective rational radicand map and its numerical support bound.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousRationalRadicandRepresentativeData20261019
import Theorems.Thm_MazurTransfer_original_representative_independent_rational_power_class
noncomputable section
open MazurTransfer NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel RationalNineteenthPowerClasses ContinuousCoefficientExponentAndContinuity ContinuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatH1AlgEquivRatCoefficientAdditiveSubtypeUnitsMemSubgroupRootsRootsRepresentation_continuousRationalRadicandMap
attribute [local instance] MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditivePowerClasses_continuousRationalRadicandMap
namespace MazurTransfer.ContinuousRationalRadicandMap
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
local notation "Γ" => K ≃ₐ[ℚ] K
local notation "M" => Coefficient (rootsRepresentation K)
local notation "H" => H1 Γ M
def radicandHom (W : Submodule (ZMod 19) H)
    (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) : W →+ Additive PowerClasses where
  toFun x := Additive.ofMul (powerClass K W hrep x)
  map_zero' := congrArg Additive.ofMul (MazurTransfer.original_representative_independent_rational_power_class.2.2.1 K W hrep)
  map_add' x y := congrArg Additive.ofMul (MazurTransfer.original_representative_independent_rational_power_class.2.2.2 K W hrep x y)
def radicandLinearMap (W : Submodule (ZMod 19) H)
    (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) : W →ₗ[ZMod 19] Additive PowerClasses :=
  (radicandHom K W hrep).toZModLinearMap 19
end MazurTransfer.ContinuousRationalRadicandMap
#print axioms MazurTransfer.ContinuousRationalRadicandMap.radicandHom
#print axioms MazurTransfer.ContinuousRationalRadicandMap.radicandLinearMap


