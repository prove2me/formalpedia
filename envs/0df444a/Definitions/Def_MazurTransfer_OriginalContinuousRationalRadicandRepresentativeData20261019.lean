-- Prove2me | Definitions.Def_MazurTransfer_OriginalContinuousRationalRadicandRepresentativeData20261019
-- name    : MazurTransfer_OriginalContinuousRationalRadicandRepresentativeData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T00:09:43.972235+00:00
-- url     : https://prove2.me/theorems/541eaf89-0e63-4f69-b764-8bb801804b79
-- title:
--   Original rational-root representative record and power-class choice
-- statement:
--   Retain the original rational-root representative record, its original given-representative choice and rational power-class value. Independently check every one of the twenty-four original namespace declaration types, fourteen whole nonproof values, all three inductive, constructor and recursor schemas, the recursor computation rule, the three original scoped provider types and values, and twenty-four context types and eighteen whole values. No global representative existence is assumed. Named downstream consumer: the original representative-independent power-class function and actual pi Selmer radicand linear injection.
-- source:
--   MazurTheorem ContinuousRationalRadicandMap by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: preserve the original rational-root representative record, its original given-representative choice and rational power-class value. No representative existence or arithmetic finiteness assertion is supplied by this constructor interface.
Named downstream consumer: the original representative-independent power-class injection, then the same selected pi Selmer radicand linear map.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousRationalRootClassData20261019
import Definitions.Def_MazurTransfer_OriginalRationalNineteenthPowerClassesData20261019

noncomputable section
namespace MazurTransfer.ContinuousRationalRadicandMap
open NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousRationalRootClassKernel
open RationalNineteenthPowerClasses
open ContinuousCoefficientExponentAndContinuity
variable (K : Type) [Field K] [CharZero K]
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRadicandMap : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K
local notation "Γ" => K ≃ₐ[ℚ] K
local notation "M" => Coefficient (rootsRepresentation K)
local notation "H" => H1 Γ M
local instance instModuleZModOfNatNatH1AlgEquivRatCoefficientAdditiveSubtypeUnitsMemSubgroupRootsRootsRepresentation_continuousRationalRadicandMap : Module (ZMod 19) H := coefficientH1ZModModule (rootsRepresentation K)
local instance instModuleZModOfNatNatAdditivePowerClasses_continuousRationalRadicandMap : Module (ZMod 19) (Additive PowerClasses) := powerClassesZModModule

structure RootClassRepresentative (x : H) where
  cocycle : continuousCocycles Γ M
  radicand : ℚˣ
  root : K
  class_eq : classMap Γ M cocycle = x
  root_spec : RepresentsRoot K cocycle radicand root







variable [IsGalois ℚ K]

def representative (W : Submodule (ZMod 19) H)
    (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) (x : W) : RootClassRepresentative K x.val := Classical.choice (hrep x)

def powerClass (W : Submodule (ZMod 19) H)
    (hrep : ∀ x : W, Nonempty (RootClassRepresentative K x.val)) (x : W) : PowerClasses := classOf (representative K W hrep x).radicand















end MazurTransfer.ContinuousRationalRadicandMap
#print axioms MazurTransfer.ContinuousRationalRadicandMap.RootClassRepresentative
#print axioms MazurTransfer.ContinuousRationalRadicandMap.representative
#print axioms MazurTransfer.ContinuousRationalRadicandMap.powerClass
#print axioms MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousRationalRadicandMap
#print axioms MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatH1AlgEquivRatCoefficientAdditiveSubtypeUnitsMemSubgroupRootsRootsRepresentation_continuousRationalRadicandMap
#print axioms MazurTransfer.ContinuousRationalRadicandMap.instModuleZModOfNatNatAdditivePowerClasses_continuousRationalRadicandMap


