-- Prove2me | Definitions.Def_MazurTransfer_OriginalRationalNineteenthPowerValuationCoordinateData20261019
-- name    : MazurTransfer_OriginalRationalNineteenthPowerValuationCoordinateData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T20:17:31.707817+00:00
-- url     : https://prove2.me/theorems/d3d69e5c-74e0-44da-a3d8-6a9f8eef284b
-- title:
--   Original rational power-class prime valuation coordinates
-- statement:
--   Retain the original rational prime valuation homomorphisms and their descent to the genuine nineteenth-power quotient. The two intrinsic exponent and range-kernel certificates define that descent. Five complete types, three whole constructor values, one original scoped module type and value, and three generated structural helper types are checked. Named downstream consumer: zero detection by all prime valuation coordinates, rational thirteen-support and the original pi Selmer radicand dimension bound.
-- source:
--   MazurTheorem RationalNineteenthPowerValuations by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original rational prime valuation maps on units and their descent to the genuine nineteenth-power quotient. The two intrinsic exponent and range-kernel certificates define the quotient map. Common-kernel and arithmetic support theorems are separate downstream results.
Named downstream consumer: zero detection by all prime valuations, rational thirteen-support and the original pi Selmer radicand dimension bound.
-/
import Definitions.Def_MazurTransfer_OriginalRationalNineteenthPowerClassesData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: rational prime valuations modulo nineteen descend to
linear maps on the genuine rational power quotient. Their common kernel
is zero by the checked constructive nineteenth-root criterion.
Named downstream consumer: the dimension bound for rational power
classes supported at thirteen and the actual pi Selmer image.
-/

noncomputable section
namespace MazurTransfer.RationalNineteenthPowerValuations
open RationalNineteenthPowerClasses
local instance instModuleZModOfNatNatAdditivePowerClasses_rationalNineteenthPowerValuations : Module (ZMod 19) (Additive PowerClasses) := powerClassesZModModule

def unitValuationHom (p : ℕ) (hp : p.Prime) : ℚˣ →* Multiplicative (ZMod 19) :=
  letI : Fact p.Prime := ⟨hp⟩
  { toFun := fun a => Multiplicative.ofAdd ((padicValRat p (a : ℚ) : ℤ) : ZMod 19)
    map_one' := by
      apply Multiplicative.toAdd.injective
      change ((padicValRat p 1 : ℤ) : ZMod 19) = 0
      simp
    map_mul' := by
      intro a b
      apply Multiplicative.toAdd.injective
      change ((padicValRat p ((a * b : ℚˣ) : ℚ) : ℤ) : ZMod 19) =
        ((padicValRat p (a : ℚ) : ℤ) : ZMod 19) + ((padicValRat p (b : ℚ) : ℤ) : ZMod 19)
      rw [Units.val_mul, padicValRat.mul (Units.ne_zero a) (Units.ne_zero b), Int.cast_add] }

theorem unitValuation_nineteenth_power (p : ℕ) (hp : p.Prime) (a : ℚˣ) :
    unitValuationHom p hp (a ^ 19) = 1 := by
  rw [map_pow]
  apply Multiplicative.toAdd.injective
  change (19 : ℕ) • (unitValuationHom p hp a).toAdd = 0
  rw [nsmul_eq_mul]
  change (19 : ZMod 19) * (unitValuationHom p hp a).toAdd = 0
  rw [show (19 : ZMod 19) = 0 by decide, zero_mul]

theorem nineteenth_powers_le_valuation_kernel (p : ℕ) (hp : p.Prime) :
    (powMonoidHom 19 : ℚˣ →* ℚˣ).range ≤ (unitValuationHom p hp).ker := by
  intro x hx
  obtain ⟨a, ha⟩ := hx
  apply MonoidHom.mem_ker.mpr
  rw [← ha]
  exact unitValuation_nineteenth_power p hp a

def valuationClassHom (p : ℕ) (hp : p.Prime) : PowerClasses →* Multiplicative (ZMod 19) :=
  QuotientGroup.lift (powMonoidHom 19 : ℚˣ →* ℚˣ).range (unitValuationHom p hp)
    (nineteenth_powers_le_valuation_kernel p hp)

def valuationLinearMap (p : ℕ) (hp : p.Prime) : Additive PowerClasses →ₗ[ZMod 19] ZMod 19 :=
  (valuationClassHom p hp).toAdditiveLeft.toZModLinearMap 19







end MazurTransfer.RationalNineteenthPowerValuations
#print axioms MazurTransfer.RationalNineteenthPowerValuations.unitValuationHom
#print axioms MazurTransfer.RationalNineteenthPowerValuations.unitValuation_nineteenth_power
#print axioms MazurTransfer.RationalNineteenthPowerValuations.nineteenth_powers_le_valuation_kernel
#print axioms MazurTransfer.RationalNineteenthPowerValuations.valuationClassHom
#print axioms MazurTransfer.RationalNineteenthPowerValuations.valuationLinearMap
#print axioms MazurTransfer.RationalNineteenthPowerValuations.instModuleZModOfNatNatAdditivePowerClasses_rationalNineteenthPowerValuations


