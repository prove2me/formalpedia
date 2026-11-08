-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:11:07.766292+00:00
-- url     : https://prove2.me/theorems/b215bfc6-edad-48d2-9307-5568ac4e3da7
-- title:
--   LPSOriginal Local Kaehler Injective
-- statement:
--   Definitions and structural lemmas for LPSOriginal Local Kaehler Injective, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalKaehlerInjective.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerFiniteness
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicValuationDifferentials
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalLocalKaehlerInjectiveDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance LPSOriginalLocalKaehlerInjectiveDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary004 : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl
local instance LPSOriginalLocalKaehlerInjectiveDictionary005 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance LPSOriginalLocalKaehlerInjectiveDictionary006 : SMulCommClass ℂ K K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f * g) = f * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalLocalKaehlerInjectiveDictionary007 : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerInjectiveDictionary008 : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
variable (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance LPSOriginalLocalKaehlerInjectiveDictionary009 : Algebra ℂ G := (germComplexConstants a).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary010 : Algebra K G := (lpsOriginalFieldToLocalComplexAlgHom N hpos hN x).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary011 : SMul K G := Algebra.toSMul (R := K) (A := G)
local instance LPSOriginalLocalKaehlerInjectiveDictionary012 : Module K G := Algebra.toModule (R := K) (A := G)
local instance LPSOriginalLocalKaehlerInjectiveDictionary013 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary014 : SMul V K := Algebra.toSMul (R := V) (A := K)
local instance LPSOriginalLocalKaehlerInjectiveDictionary015 : Module V K := Algebra.toModule (R := V) (A := K)
local instance LPSOriginalLocalKaehlerInjectiveDictionary016 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance LPSOriginalLocalKaehlerInjectiveDictionary017 : SMul V (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerInjectiveDictionary018 : Module V (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance LPSOriginalLocalKaehlerInjectiveDictionary019 : IsScalarTower ℂ K G :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((lpsOriginalFieldToLocalComplexAlgHom N hpos hN x).commutes c).symm
local instance LPSOriginalLocalKaehlerInjectiveDictionary020 : IsDiscreteValuationRing V :=
  lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x
local instance LPSOriginalLocalKaehlerInjectiveDictionary021 : IsDiscreteValuationRing
    (Valuation.valuationSubring (AddValuation.toValuation
      (AddValuation.comap (algebraMap K G) (meromorphicOrderValuation a)))) := by
  change IsDiscreteValuationRing V
  exact lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x
local instance LPSOriginalLocalKaehlerInjectiveDictionary022 : Algebra ℂ V := (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance LPSOriginalLocalKaehlerInjectiveDictionary023 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl
end
end QEC.Coding.TannerLiftedProduct


