-- Prove2me | Definitions.Def_MazurTransfer_OriginalRationalThirteenSupportedPowerClassSubmoduleData20261019
-- name    : MazurTransfer_OriginalRationalThirteenSupportedPowerClassSubmoduleData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T20:25:27.922761+00:00
-- url     : https://prove2.me/theorems/cde5bb89-9910-402e-a6d3-f23bf29c8af0
-- title:
--   Original rational thirteen-support and coordinate constructors
-- statement:
--   Retain the original submodule of genuine rational nineteenth-power classes whose prime valuation coordinates vanish outside thirteen, its thirteen-coordinate map and the generic codomain restriction constructor. All three complete constructor types and whole values, both original scoped provider types, their one whole nonproof value and three generated structural proof types are checked. Named downstream consumer: the same support space dimension bound and original selected pi Selmer radicand theorem.
-- source:
--   MazurTheorem RationalThirteenPowerClassBound by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original submodule of genuine rational nineteenth-power classes with zero prime valuation coordinates outside thirteen, its thirteen-coordinate map and restriction constructor. Injectivity, finite dimension and arithmetic image claims are separate theorem results.
Named downstream consumer: the rational thirteen-support dimension theorem and the original selected pi Selmer radicand bound.
-/
import Definitions.Def_MazurTransfer_OriginalRationalNineteenthPowerValuationCoordinateData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the genuine rational nineteenth-power classes whose
prime valuations vanish modulo nineteen outside thirteen form a finite
F19 subspace of dimension at most one. The coordinate at thirteen is
proved injective; no arithmetic property of an actual curve is assumed.
Named downstream consumer: restrict the checked actual pi Selmer radicand
injection after identifying its rational prime valuation conditions.
-/

noncomputable section
namespace MazurTransfer.RationalThirteenPowerClassBound
open RationalNineteenthPowerClasses RationalNineteenthPowerValuations
local instance instFactPrimeOfNatNat_rationalThirteenPowerClassBound : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance instModuleZModOfNatNatAdditivePowerClasses_rationalThirteenPowerClassBound : Module (ZMod 19) (Additive PowerClasses) := powerClassesZModModule

def thirteenSupport : Submodule (ZMod 19) (Additive PowerClasses) :=
  ⨅ (q : ℕ) (hq : q.Prime) (_ : q ≠ 13), (valuationLinearMap q hq).ker



def thirteenCoordinate : thirteenSupport →ₗ[ZMod 19] ZMod 19 :=
  (valuationLinearMap 13 (by decide)).comp thirteenSupport.subtype









variable {W : Type} [AddCommGroup W] [Module (ZMod 19) W]

def restrictToThirteenSupport (f : W →ₗ[ZMod 19] Additive PowerClasses)
    (hf : ∀ x : W, f x ∈ thirteenSupport) : W →ₗ[ZMod 19] thirteenSupport :=
  f.codRestrict thirteenSupport hf



end MazurTransfer.RationalThirteenPowerClassBound
#print axioms MazurTransfer.RationalThirteenPowerClassBound.thirteenSupport
#print axioms MazurTransfer.RationalThirteenPowerClassBound.thirteenCoordinate
#print axioms MazurTransfer.RationalThirteenPowerClassBound.restrictToThirteenSupport
#print axioms MazurTransfer.RationalThirteenPowerClassBound.instModuleZModOfNatNatAdditivePowerClasses_rationalThirteenPowerClassBound
#print axioms MazurTransfer.RationalThirteenPowerClassBound.instFactPrimeOfNatNat_rationalThirteenPowerClassBound


