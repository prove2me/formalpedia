-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:29:48.971471+00:00
-- url     : https://prove2.me/theorems/6564b617-19a8-49e6-aa37-db12c352e2cf
-- title:
--   Closure Canonical Differential
-- statement:
--   Definitions and structural lemmas for Closure Canonical Differential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureCanonicalDifferential.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWBase_generator_pow_fifteen
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedVanishingFunction_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_eq_functionFieldDerivation_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
local instance canonicalDifferentialModule (m : ℕ) :
    Module (SourceGaloisClosureField m) (Differential F256 (SourceGaloisClosureField m)) :=
  instModuleKaehlerDifferentialOfSMulCommClass F256 (SourceGaloisClosureField m)
    (R' := SourceGaloisClosureField m)
local instance canonicalDifferentialSMul (m : ℕ) :
    SMul (SourceGaloisClosureField m) (Differential F256 (SourceGaloisClosureField m)) :=
  (canonicalDifferentialModule m).toSMul
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
theorem sourceClosure_selectedVanishing_eq_z_sub_one (m : ℕ) :
    sourceGaloisClosureSelectedVanishingFunction m =
      algebraMap (RatFunc F256) (SourceGaloisClosureField m) RatFunc.X - 1 := by
  rw [sourceGaloisClosureSelectedVanishingFunction_eq]
  congr 1
  have h := congrArg (algebraMap (sourceClosureWBase m) (SourceGaloisClosureField m))
    (sourceClosureWBase_generator_pow_fifteen m)
  erw [map_pow, ← IsScalarTower.algebraMap_apply (RatFunc F256)
    (sourceClosureWBase m) (SourceGaloisClosureField m)] at h
  exact h
theorem sourceClosure_selectedVanishing_derivative (m : ℕ) :
    functionFieldDerivation (k := F256) (F := SourceGaloisClosureField m)
      (sourceGaloisClosureSelectedVanishingFunction m) = 1 := by
  rw [sourceClosure_selectedVanishing_eq_z_sub_one, map_sub,
    functionFieldDerivation_apply_X, Derivation.map_one_eq_zero, sub_zero]
def sourceClosureCanonicalDifferential (m : ℕ) : Differential F256 (SourceGaloisClosureField m) :=
  Differential.logarithmicDifferential (sourceGaloisClosureSelectedVanishingFunction m)
theorem sourceClosureCanonicalDifferential_eq_inverse_smul_dz (m : ℕ) :
    sourceClosureCanonicalDifferential m =
      (sourceGaloisClosureSelectedVanishingFunction m : SourceGaloisClosureField m)⁻¹ •
        functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m) := by
  rw [sourceClosureCanonicalDifferential, Differential.logarithmicDifferential,
    differential_eq_functionFieldDerivation_smul_generator,
    sourceClosure_selectedVanishing_derivative]
  exact congrArg (fun omega => (sourceGaloisClosureSelectedVanishingFunction m)⁻¹ • omega)
    ((canonicalDifferentialModule m).one_smul _)
theorem sourceClosureCanonicalDifferential_ne_zero (m : ℕ) :
    sourceClosureCanonicalDifferential m ≠ 0 := by
  rw [sourceClosureCanonicalDifferential_eq_inverse_smul_dz]
  exact smul_ne_zero (inv_ne_zero (sourceGaloisClosureSelectedVanishingFunction_ne_zero m))
    functionFieldDifferentialGenerator_ne_zero
def sourceClosureCanonicalDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (SourceGaloisClosureField m)) :=
  differentialDivisor (sourceClosureCanonicalDifferential m)
    (sourceClosureCanonicalDifferential_ne_zero m)
def sourceClosureCanonicalDifferentialAtPlace (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) : Differential.simplePoleDifferentialLattice Q :=
  Differential.logarithmicDifferentialAtSimplePole Q
    (sourceGaloisClosureSelectedVanishingFunction m)
    (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


