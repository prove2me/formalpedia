-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferent
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T21:05:32.577228+00:00
-- url     : https://prove2.me/theorems/d7021625-9c3c-4b9b-89d5-2dd95fd6a089
-- title:
--   Closure Fibre Different
-- statement:
--   Definitions and structural lemmas for Closure Fibre Different, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureFibreDifferent.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
variable (m : ℕ)
local instance fibreDifferent_baseAlgebra (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Algebra P.valuationRing (sourceClosureWBase m) :=
  inferInstanceAs (Algebra P.valuationRing (SourceGaloisWClosureField m))
local instance fibreDifferent_baseFraction (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsFractionRing P.valuationRing (sourceClosureWBase m) :=
  inferInstanceAs (IsFractionRing P.valuationRing (SourceGaloisWClosureField m))
local instance fibreDifferent_baseFaithful (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    FaithfulSMul P.valuationRing (sourceClosureWBase m) := by
  apply (faithfulSMul_iff_algebraMap_injective P.valuationRing (sourceClosureWBase m)).mpr
  exact ValuationSubring.subtype_injective P.valuationRing
local instance fibreDifferent_baseDVR (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsDiscreteValuationRing P.valuationRing := P.valuationRing_isDiscreteValuationRing
local instance fibreDifferent_ambientAlgebra (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Algebra P.valuationRing (SourceGaloisClosureField m) :=
  ((algebraMap (sourceClosureWBase m) (SourceGaloisClosureField m)).comp
    (algebraMap P.valuationRing (sourceClosureWBase m))).toAlgebra
local instance fibreDifferent_baseTower (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsScalarTower P.valuationRing (sourceClosureWBase m) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance fibreDifferent_ambientTorsionFree (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Module.IsTorsionFree P.valuationRing (SourceGaloisClosureField m) := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  change Function.Injective ((algebraMap (sourceClosureWBase m) (SourceGaloisClosureField m)).comp
    (algebraMap P.valuationRing (sourceClosureWBase m)))
  exact (algebraMap (sourceClosureWBase m) (SourceGaloisClosureField m)).injective.comp
    (ValuationSubring.subtype_injective P.valuationRing)
def sourceClosurePlaceDifferentIdeal (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Ideal (integralClosure P.valuationRing (SourceGaloisClosureField m)) :=
  differentIdeal P.valuationRing (integralClosure P.valuationRing (SourceGaloisClosureField m))
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


