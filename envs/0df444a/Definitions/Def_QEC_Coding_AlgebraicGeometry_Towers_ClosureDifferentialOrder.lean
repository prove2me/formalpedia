-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialOrder
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:47:46.634397+00:00
-- url     : https://prove2.me/theorems/cc9f7279-f50d-4138-9e1b-9eaba36d616d
-- title:
--   Closure Differential Order
-- statement:
--   Definitions and structural lemmas for Closure Differential Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferentialOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedDifferentialRefinement
set_option autoImplicit false
open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
def sourceClosureWBase_zMap (m : ℕ) : RatFunc F256 →ₐ[F256] sourceClosureWBase m :=
  (sourceGaloisClosureRatFuncEmbedding m).codRestrict (sourceClosureWBase m).toSubalgebra
    (fun r => (SourceGaloisWClosureField m).algebraMap_mem (galoisBaseFieldEquivRatFunc r))
scoped instance sourceClosureWBase_zAlgebra (m : ℕ) :
    Algebra (RatFunc F256) (sourceClosureWBase m) := (sourceClosureWBase_zMap m).toRingHom.toAlgebra
scoped instance sourceClosureWBase_zConstantTower (m : ℕ) :
    IsScalarTower F256 (RatFunc F256) (sourceClosureWBase m) := by
  refine @IsScalarTower.of_algebraMap_eq' F256 (RatFunc F256) (sourceClosureWBase m)
    _ _ _ _ (sourceClosureWBase_zAlgebra m) (sourceClosureWBase m).algebra' ?_
  apply RingHom.ext
  intro c
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply F256 (RatFunc F256) (SourceGaloisClosureField m) c
scoped instance sourceClosureWBase_zAmbientTower (m : ℕ) :
    IsScalarTower (RatFunc F256) (sourceClosureWBase m) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
scoped instance sourceClosureWBase_zFinite (m : ℕ) :
    FiniteDimensional (RatFunc F256) (sourceClosureWBase m) := by
  letI : Module.IsTorsionFree (sourceClosureWBase m) (SourceGaloisClosureField m) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap (sourceClosureWBase m) (SourceGaloisClosureField m)).injective
  exact FiniteDimensional.left (RatFunc F256) (sourceClosureWBase m)
    (SourceGaloisClosureField m)
scoped instance sourceClosureWBase_zSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (sourceClosureWBase m) :=
  Algebra.isSeparable_tower_bot_of_isSeparable (RatFunc F256) (sourceClosureWBase m)
    (SourceGaloisClosureField m)
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


