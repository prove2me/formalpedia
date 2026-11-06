-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_SeparableNormalCover
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_SeparableNormalCover
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:04:49.063989+00:00
-- url     : https://prove2.me/theorems/993eab0f-92d5-48d9-a6bf-3256d7cd09a3
-- title:
--   Separable Normal Cover
-- statement:
--   Definitions and structural lemmas for Separable Normal Cover, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/SeparableNormalCover.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.RamificationInertia.Inertia
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.SeparableNormalCover
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
abbrev directRingOfIntegers : Type _ := _root_.FunctionField.ringOfIntegers k F
local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F
local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing B
local instance _p2m_local_instance_ece2c1af97_56 : Module.IsTorsionFree R B :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
local instance _p2m_local_instance_ece2c1af97_60 : Module.Finite R B := AffinePlace.finite_ringOfIntegers k F
noncomputable local instance _p2m_local_instance_ece2c1af97_62 : Algebra K L := FractionRing.liftAlgebra _ _
theorem fractionRing_isSeparable : Algebra.IsSeparable K L := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv R k⟮X⟯).symm.toRingEquiv
    (FractionRing.algEquiv B F).symm.toRingEquiv ?_
  ext x
  exact IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv R k⟮X⟯).symm
    (FractionRing.algEquiv B F).symm x
local instance _p2m_local_instance_ece2c1af97_76 : Algebra.IsSeparable K L := fractionRing_isSeparable k F
local notation3 "M" => SeparableClosure K
noncomputable def directSeparableEmbedding : L →ₐ[K] M :=
  (IsSepClosed.lift : L →ₐ[K] M)
local instance _p2m_local_instance_ece2c1af97_87 : Algebra L M := (directSeparableEmbedding k F).toRingHom.toAlgebra
local instance _p2m_local_instance_ece2c1af97_89 : IsScalarTower K L M :=
  IsScalarTower.of_algebraMap_eq' (directSeparableEmbedding k F).comp_algebraMap.symm
local notation3 "E" => IntermediateField.normalClosure K L M
local instance _p2m_local_instance_ece2c1af97_96 : FiniteDimensional K E := normalClosure.is_finiteDimensional K L M
local instance _p2m_local_instance_ece2c1af97_98 : IsGalois K E := IsGalois.normalClosure K L M
local instance _p2m_local_instance_ece2c1af97_100 : Algebra B E := ((algebraMap L E).comp (algebraMap B L)).toAlgebra
local instance _p2m_local_instance_ece2c1af97_102 : IsScalarTower B L E := IsScalarTower.of_algebraMap_eq' rfl
local notation "T" => integralClosure B E
local instance _p2m_local_instance_ece2c1af97_108 : Algebra R T := ((algebraMap B T).comp (algebraMap R B)).toAlgebra
local instance _p2m_local_instance_ece2c1af97_110 : IsIntegralClosure T B E := integralClosure.isIntegralClosure B E
local instance _p2m_local_instance_ece2c1af97_112 : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
local instance _p2m_local_instance_ece2c1af97_114 : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E
local instance _p2m_local_instance_ece2c1af97_116 : IsScalarTower R B E := IsScalarTower.to₁₂₄ R B L E
local instance _p2m_local_instance_ece2c1af97_118 : IsScalarTower R T E := IsScalarTower.to₁₃₄ R B T E
local instance _p2m_local_instance_ece2c1af97_120 : FaithfulSMul B E :=
  (faithfulSMul_iff_algebraMap_injective B E).mpr <|
    (FaithfulSMul.algebraMap_injective L E).comp
      (FaithfulSMul.algebraMap_injective B L)
local instance _p2m_local_instance_ece2c1af97_125 : FaithfulSMul B T :=
  (faithfulSMul_iff_algebraMap_injective B T).mpr <| by
    intro x y h
    apply FaithfulSMul.algebraMap_injective B E
    simpa using congrArg (fun z : T => (z : E)) h
local instance _p2m_local_instance_ece2c1af97_131 : Module.IsTorsionFree B E :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective B E)
local instance _p2m_local_instance_ece2c1af97_135 : Module.IsTorsionFree B T :=
  Subalgebra.instIsTorsionFree (integralClosure B E)
local instance _p2m_local_instance_ece2c1af97_138 : Module.IsTorsionFree R T :=
  Module.IsTorsionFree.trans_faithfulSMul R B T
local instance _p2m_local_instance_ece2c1af97_141 : FaithfulSMul R T :=
  (faithfulSMul_iff_algebraMap_injective R T).mpr <|
    (FaithfulSMul.algebraMap_injective B T).comp
      (FaithfulSMul.algebraMap_injective R B)
local instance _p2m_local_instance_ece2c1af97_146 : FiniteDimensional L E := FiniteDimensional.right K L E
local instance _p2m_local_instance_ece2c1af97_148 : IsFractionRing T E :=
  integralClosure.isFractionRing_of_finite_extension L E
local instance _p2m_local_instance_ece2c1af97_151 : IsIntegrallyClosed T :=
  integralClosure.isIntegrallyClosedOfFiniteExtension L
local instance _p2m_local_instance_ece2c1af97_154 : Algebra.IsSeparable L E :=
  Algebra.isSeparable_tower_top_of_isSeparable K L E
local instance _p2m_local_instance_ece2c1af97_157 : Algebra.IsIntegral B T :=
  IsIntegralClosure.isIntegral_algebra B (A := T) E
local instance _p2m_local_instance_ece2c1af97_160 : Module.Finite B T := IsIntegralClosure.finite B L E T
local instance _p2m_local_instance_ece2c1af97_162 : Module.Finite R T := Module.Finite.trans B T
local instance _p2m_local_instance_ece2c1af97_164 : IsDedekindDomain T := integralClosure.isDedekindDomain B L E
noncomputable local instance _p2m_local_instance_ece2c1af97_168 : Algebra T (FractionRing T) := OreLocalization.instAlgebra
noncomputable local instance _p2m_local_instance_ece2c1af97_170 : Algebra K (FractionRing T) :=
  FractionRing.liftAlgebra R (FractionRing T)
theorem directCover_fractionRing_isGalois : IsGalois K (FractionRing T) := by
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext x
  simpa using @IsFractionRing.algEquiv_commutes R inferInstance T inferInstance inferInstance
    K (FractionRing R) inferInstance inferInstance inferInstance inferInstance inferInstance
    E (FractionRing T) inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm x
local instance _p2m_local_instance_ece2c1af97_185 : IsGalois K (FractionRing T) := directCover_fractionRing_isGalois k F
noncomputable local instance directBFracAlgebra : Algebra B (FractionRing T) :=
  OreLocalization.instAlgebra
local instance _p2m_local_instance_ece2c1af97_189 : SMul B (FractionRing T) := (directBFracAlgebra k F).toSMul
local instance _p2m_local_instance_ece2c1af97_190 : FaithfulSMul B (FractionRing T) :=
  (faithfulSMul_iff_algebraMap_injective B (FractionRing T)).mpr
    ((IsFractionRing.injective T (FractionRing T)).comp
      (FaithfulSMul.algebraMap_injective B T))
noncomputable local instance _p2m_local_instance_ece2c1af97_194 : Algebra L (FractionRing T) :=
  FractionRing.liftAlgebra B (FractionRing T)
end
end QEC.Coding.AlgebraicGeometry.SeparableNormalCover


