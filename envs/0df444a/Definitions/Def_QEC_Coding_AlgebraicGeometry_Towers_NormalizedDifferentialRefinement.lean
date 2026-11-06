-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedDifferentialRefinement
-- name    : QEC_Coding_AlgebraicGeometry_Towers_NormalizedDifferentialRefinement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:10:36.897206+00:00
-- url     : https://prove2.me/theorems/3916bba9-d93b-4ba6-85da-4506710499bd
-- title:
--   Normalized Differential Refinement
-- statement:
--   Definitions and structural lemmas for Normalized Differential Refinement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedDifferentialRefinement.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Algebra (RatFunc F256) F] [Algebra (RatFunc F256) E]
    [IsScalarTower F256 (RatFunc F256) F] [IsScalarTower F256 (RatFunc F256) E]
    [IsScalarTower (RatFunc F256) F E]
    [FiniteDimensional (RatFunc F256) F] [Algebra.IsSeparable (RatFunc F256) F]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q
local instance intermediateRationalConstantTower (K : IntermediateField F E) :
    IsScalarTower F256 (RatFunc F256) K := IsScalarTower.of_algebraMap_eq' (by
  apply RingHom.ext
  intro c
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply F256 (RatFunc F256) E c)
local instance intermediateRationalRelativeTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower (RatFunc F256) K L := IsScalarTower.of_algebraMap_eq' rfl
local instance intermediateConstantRelativeTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower F256 K L := IsScalarTower.of_algebraMap_eq' rfl
local instance intermediateRationalFinite (K : IntermediateField F E) :
    FiniteDimensional (RatFunc F256) K := FiniteDimensional.trans (RatFunc F256) F K
local instance intermediateRationalSeparable (K : IntermediateField F E) :
    Algebra.IsSeparable (RatFunc F256) K := Algebra.IsSeparable.trans (RatFunc F256) F K
def intermediateDifferentialGeneratorOrder (K : IntermediateField F E) : ℤ :=
  differentialOrder (heightOnePlace (k := F256) (K := K) (P K))
    (functionFieldDifferentialGenerator (k := F256) (F := K))
    functionFieldDifferentialGenerator_ne_zero
local notation "g" => intermediateDifferentialGeneratorOrder A F E Q
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


