-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:19:13.476021+00:00
-- url     : https://prove2.me/theorems/e6a437a7-3127-4dce-959c-5f6c7f789cc8
-- title:
--   LPSOriginal Native Local Differential Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Native Local Differential Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeLocalDifferentialComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "Cov" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
local instance _p2m_local_instance_a8e2bd7548_26 : Algebra ℂ G := (germComplexConstants a).toAlgebra
local instance _p2m_local_instance_a8e2bd7548_28 : AddCommGroup Cov := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
def lpsOriginalCovectorRepresentativeToLocal : Cov →ₗ[ℂ] G := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := lpsOriginalLocalChart N hN x
  have ha : a ∈ e.target := e.map_source (lpsOriginalLocalChart_mem_source N hN x)
  exact
    { toFun := fun σ => ⟨(lpsOriginalFilledCovectorChartCoefficient N hN σ.val x : Germ (𝓝[≠] a) ℂ),
        lpsOriginalFilledCovectorChartCoefficient N hN σ.val x,σ.property x a ha,rfl⟩
      map_add' := by
        intro σ τ
        apply Subtype.ext
        change ((lpsOriginalFilledCovectorChartCoefficientLinearMap N hN x) (σ.val+τ.val) :
          Germ (𝓝[≠] a) ℂ) = _
        rw [map_add]
        rfl
      map_smul' := by
        intro c σ
        apply Subtype.ext
        change ((lpsOriginalFilledCovectorChartCoefficientLinearMap N hN x) (c • σ.val) :
          Germ (𝓝[≠] a) ℂ) = _
        rw [map_smul]
        rfl }
lemma lpsOriginalCovectorGlobalZero_le_localKernel :
    lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN ≤
      (lpsOriginalCovectorRepresentativeToLocal N hN x).ker := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro σ hσ
  change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N), σ.val y = 0 at hσ
  let e := lpsOriginalLocalChart N hN x
  have hx : x ∈ e.source := lpsOriginalLocalChart_mem_source N hN x
  have ha : e x ∈ e.target := e.map_source hx
  have hp : ∀ᶠ y in 𝓝[≠] x, σ.val y = 0 := by
    have h := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hσ x (Set.mem_univ x)
    change {y | σ.val y = 0} ∈ 𝓝[≠] x
    simpa only [Set.compl_univ,Set.union_empty] using h
  have ht : Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] x) := by
    have h : Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] (e.symm (e x))) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(e.symm.continuousAt ha).tendsto.mono_left nhdsWithin_le_nhds,
          e.symm.eventually_ne_nhdsWithin ha⟩
    simpa only [e.left_inv hx] using h
  change lpsOriginalCovectorRepresentativeToLocal N hN x σ = 0
  apply Subtype.ext
  change (lpsOriginalFilledCovectorChartCoefficient N hN σ.val x : Germ (𝓝[≠] a) ℂ) = 0
  apply Germ.coe_eq.mpr
  filter_upwards [ht.eventually hp] with z hz
  change σ.val ((chartAt ℂ x).symm z) = 0 at hz
  simp only [lpsOriginalFilledCovectorChartCoefficient,ContinuousLinearMap.inCoordinates]
  rw [hz]
  simp
def lpsOriginalNativeCovectorToLocal :
    LPSOriginalCompactMeromorphicCovectorGerms N hN →ₗ[ℂ] G :=
  (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN).liftQ
    (lpsOriginalCovectorRepresentativeToLocal N hN x)
    (lpsOriginalCovectorGlobalZero_le_localKernel N hN x)
section GenericComparison
local instance _p2m_local_instance_a8e2bd7548_142 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local instance _p2m_local_instance_a8e2bd7548_148 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_a8e2bd7548_149 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_a8e2bd7548_150 : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl
local instance _p2m_local_instance_a8e2bd7548_151 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local instance _p2m_local_instance_a8e2bd7548_152 : SMulCommClass ℂ K K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f * g) = f * (algebraMap ℂ K c * g)
    ring
local instance _p2m_local_instance_a8e2bd7548_156 : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_a8e2bd7548_158 : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_a8e2bd7548_160 : Algebra ℂ L := ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.comp
  (lpsOriginalFilledMeromorphicComplexConstants N hN)).toAlgebra
local instance _p2m_local_instance_a8e2bd7548_162 : Algebra K G := (lpsOriginalFieldToLocalComplexAlgHom N hpos hN x).toAlgebra
local instance _p2m_local_instance_a8e2bd7548_163 : SMul K G := Algebra.toSMul (R := K) (A := G)
local instance _p2m_local_instance_a8e2bd7548_164 : Module K G := Algebra.toModule (R := K) (A := G)
section Regularity
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance _p2m_local_instance_a8e2bd7548_221 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance _p2m_local_instance_a8e2bd7548_222 : SMul V K := Algebra.toSMul (R := V) (A := K)
local instance _p2m_local_instance_a8e2bd7548_223 : Module V K := Algebra.toModule (R := V) (A := K)
local instance _p2m_local_instance_a8e2bd7548_224 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance _p2m_local_instance_a8e2bd7548_228 : SMul V (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_a8e2bd7548_230 : Module V (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_a8e2bd7548_232 : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
local instance _p2m_local_instance_a8e2bd7548_234 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl
end Regularity
end GenericComparison
end
end QEC.Coding.TannerLiftedProduct


