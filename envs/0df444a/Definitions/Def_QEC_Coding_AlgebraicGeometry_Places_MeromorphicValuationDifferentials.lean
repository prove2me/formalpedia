-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicValuationDifferentials
-- name    : QEC_Coding_AlgebraicGeometry_Places_MeromorphicValuationDifferentials
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:06:11.884209+00:00
-- url     : https://prove2.me/theorems/570a846c-7773-4198-afc4-43f15b78634e
-- title:
--   Meromorphic Valuation Differentials
-- statement:
--   Definitions and structural lemmas for Meromorphic Valuation Differentials, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicValuationDifferentials.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicNoPoleEvaluation_rep

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
local instance MeromorphicValuationDifferentialsDictionary001 : Algebra ℂ (MeromorphicGermRing a) := (germComplexConstants a).toAlgebra
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
local notation "V" => localValuationRing K a
local instance MeromorphicValuationDifferentialsDictionary002 : Algebra ℂ V := (complexConstantsToValuationRing K a).toAlgebra
local instance MeromorphicValuationDifferentialsDictionary003 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl
def localValuationToMeromorphicInteger : V →+*
    (AddValuation.toValuation (meromorphicOrderValuation a)).integer := by
  let f := (algebraMap K (MeromorphicGermRing a)).comp (ValuationSubring.subtype V)
  refine f.codRestrict _ ?_
  intro t
  exact t.property
def localValuationResidueEvaluation : V →ₐ[ℂ] ℂ where
  toRingHom := (meromorphicNoPoleEvaluation a).comp (localValuationToMeromorphicInteger K a)
  commutes' c := by
    apply meromorphicNoPoleEvaluation_rep _ _ (fun _ => c) analyticAt_const
    change ((algebraMap K (MeromorphicGermRing a)) (algebraMap ℂ K c)).val = _
    rw [← IsScalarTower.algebraMap_apply ℂ K (MeromorphicGermRing a) c]
    rfl
end
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
local instance MeromorphicValuationDifferentialsDictionary004 : Algebra ℂ (MeromorphicGermRing a) := (germComplexConstants a).toAlgebra
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
local notation "V" => localValuationRing K a
local instance MeromorphicValuationDifferentialsDictionary005 : Algebra ℂ V := (complexConstantsToValuationRing K a).toAlgebra
local instance MeromorphicValuationDifferentialsDictionary006 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance MeromorphicValuationDifferentialsDictionary007 : SMul V K := Algebra.toSMul
local instance MeromorphicValuationDifferentialsDictionary008 : Module V K := Algebra.toModule
local instance MeromorphicValuationDifferentialsDictionary009 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl
local instance MeromorphicValuationDifferentialsDictionary010 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    simp only [Algebra.smul_def]
    ring
local instance MeromorphicValuationDifferentialsDictionary011 : SMul V (KaehlerDifferential ℂ K) := instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance MeromorphicValuationDifferentialsDictionary012 : Module V (KaehlerDifferential ℂ K) := instModuleKaehlerDifferentialOfSMulCommClass ℂ K
end
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential


