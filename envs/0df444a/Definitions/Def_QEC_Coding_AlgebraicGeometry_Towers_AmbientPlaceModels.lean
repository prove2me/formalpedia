-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
-- name    : QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:35:07.597879+00:00
-- url     : https://prove2.me/theorems/be7da80c-c3a4-4370-b4cf-0f3801e79ce6
-- title:
--   Ambient Place Models
-- statement:
--   Definitions and structural lemmas for Ambient Place Models, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/AmbientPlaceModels.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_restrictedIntegralClosure_prime
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
noncomputable section
variable {k E : Type*} [Field k] [Finite k] [Field E] [Algebra k E]
    (F : Type*) [Field F] [Algebra k F] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace k E)
def baseRing : ValuationSubring F := (Q.restrict (F := F)).valuationRing
scoped instance baseDiscreteValuationRing : IsDiscreteValuationRing (baseRing F Q) :=
  (Q.restrict (F := F)).valuationRing_isDiscreteValuationRing
scoped instance baseAmbientAlgebra : Algebra (baseRing F Q) E :=
  ((algebraMap F E).comp (baseRing F Q).subtype).toAlgebra
scoped instance baseAmbientTower : IsScalarTower (baseRing F Q) F E :=
  IsScalarTower.of_algebraMap_eq' rfl
scoped instance baseAmbientTorsionFree : Module.IsTorsionFree (baseRing F Q) E :=
  Module.IsTorsionFree.trans_faithfulSMul (baseRing F Q) F E
abbrev Model := integralClosure (baseRing F Q) E
scoped instance modelDedekind : IsDedekindDomain (Model F Q) :=
  integralClosure.isDedekindDomain (baseRing F Q) F E
scoped instance modelFractionRing : IsFractionRing (Model F Q) E :=
  integralClosure.isFractionRing_of_finite_extension F E
scoped instance modelFinite : Module.Finite (baseRing F Q) (Model F Q) :=
  IsIntegralClosure.finite (baseRing F Q) F E (Model F Q)
scoped instance modelTorsionFree : Module.IsTorsionFree (baseRing F Q) (Model F Q) :=
  IsIntegralClosure.isTorsionFree (baseRing F Q) E
theorem exists_prime :
    ∃ H : IsDedekindDomain.HeightOneSpectrum (Model F Q),
      H.valuationSubringAtPrime E = Q.valuationRing ∧
        (heightOnePlace (k := k) (K := E) H).order = Q.order := by
  letI : Algebra (Q.restrict (F := F)).valuationRing E := baseAmbientAlgebra F Q
  letI : IsScalarTower (Q.restrict (F := F)).valuationRing F E := baseAmbientTower F Q
  letI : IsDedekindDomain (integralClosure (Q.restrict (F := F)).valuationRing E) :=
    modelDedekind F Q
  letI : IsFractionRing (integralClosure (Q.restrict (F := F)).valuationRing E) E :=
    modelFractionRing F Q
  exact Q.exists_restrictedIntegralClosure_prime (F := F)
def prime : IsDedekindDomain.HeightOneSpectrum (Model F Q) :=
  Classical.choose (exists_prime F Q)
end
end QEC.Coding.AlgebraicGeometry.AmbientPlaceModels


