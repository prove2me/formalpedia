-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:12:33.727693+00:00
-- url     : https://prove2.me/theorems/8ac55e23-9a23-40a9-a76d-45089ec81f3e
-- title:
--   LPSOriginal Local Regular Differential Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Local Regular Differential Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalRegularDifferentialComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance _p2m_local_instance_dde5696b56_25 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance _p2m_local_instance_dde5696b56_30 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_dde5696b56_31 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_dde5696b56_32 : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl
local instance _p2m_local_instance_dde5696b56_33 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance _p2m_local_instance_dde5696b56_34 : SMulCommClass ℂ K K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f * g) = f * (algebraMap ℂ K c * g)
    ring
local instance _p2m_local_instance_dde5696b56_38 : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_dde5696b56_40 : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
variable (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance _p2m_local_instance_dde5696b56_47 : Algebra ℂ G := (germComplexConstants a).toAlgebra
def lpsOriginalFieldToLocalComplexAlgHom : K →ₐ[ℂ] G where
  toRingHom := lpsOriginalFieldToLocal N hN hpos x
  commutes' c := by
    change lpsOriginalFieldToLocal N hN hpos x (algebraMap ℂ K c) =
      germComplexConstants a c
    rw [lpsOriginalFieldToLocal_constant N hN hpos x c]
    rfl
local instance _p2m_local_instance_dde5696b56_58 : Algebra K G := (lpsOriginalFieldToLocalComplexAlgHom N hpos hN x).toAlgebra
local instance _p2m_local_instance_dde5696b56_59 : SMul K G := Algebra.toSMul (R := K) (A := G)
local instance _p2m_local_instance_dde5696b56_60 : Module K G := Algebra.toModule (R := K) (A := G)
local instance _p2m_local_instance_dde5696b56_61 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance _p2m_local_instance_dde5696b56_62 : SMul V K := Algebra.toSMul (R := V) (A := K)
local instance _p2m_local_instance_dde5696b56_63 : Module V K := Algebra.toModule (R := V) (A := K)
local instance _p2m_local_instance_dde5696b56_64 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance _p2m_local_instance_dde5696b56_68 : SMul V (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_dde5696b56_70 : Module V (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_dde5696b56_72 : IsScalarTower ℂ K G :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((lpsOriginalFieldToLocalComplexAlgHom N hpos hN x).commutes c).symm
local instance _p2m_local_instance_dde5696b56_75 : IsDiscreteValuationRing V :=
  lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x
local instance _p2m_local_instance_dde5696b56_78 : IsDiscreteValuationRing
    (Valuation.valuationSubring (AddValuation.toValuation
      (AddValuation.comap (algebraMap K G) (meromorphicOrderValuation a)))) := by
  change IsDiscreteValuationRing V
  exact lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x
abbrev lpsOriginalFieldLocalDifferentialMap : KaehlerDifferential ℂ K →ₗ[K] G :=
  QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.fieldLocalDifferentialMap K a
abbrev lpsOriginalLocalDifferentialLattice : Submodule V (KaehlerDifferential ℂ K) :=
  QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localDifferentialLattice K a
abbrev lpsOriginalComplexConstantsToMeromorphicValuationRing : ℂ →+* V :=
  QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.complexConstantsToValuationRing K a
local instance _p2m_local_instance_dde5696b56_113 : Algebra ℂ V := (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance _p2m_local_instance_dde5696b56_114 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl
end
end QEC.Coding.TannerLiftedProduct


