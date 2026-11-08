-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:57:46.075197+00:00
-- url     : https://prove2.me/theorems/3f5c142c-24f8-4058-8ea5-4a25b23301b2
-- title:
--   LPSOriginal Local Meromorphic Order
-- statement:
--   Definitions and structural lemmas for LPSOriginal Local Meromorphic Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalMeromorphicOrder.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
local instance lpsOriginalLocalChartGermTopology : TopologicalSpace (LPSOriginalFilledCurve N) :=
  lpsOriginalFilledTopology N
abbrev lpsOriginalLocalChart (x : LPSOriginalFilledCurve N) :
    OpenPartialHomeomorph (LPSOriginalFilledCurve N) ℂ := by
  letI := lpsOriginalFilledChartedSpace N hN
  exact chartAt ℂ x
lemma lpsOriginalLocalChart_mem_source (x : LPSOriginalFilledCurve N) :
    x ∈ (lpsOriginalLocalChart N hN x).source := by
  let := lpsOriginalFilledChartedSpace N hN
  exact mem_chart_source ℂ x
abbrev lpsOriginalLocalChartCenter (x : LPSOriginalFilledCurve N) : ℂ := (lpsOriginalLocalChart N hN x) x
def lpsOriginalRepresentativeToLocal (x : LPSOriginalFilledCurve N) :
    LPSOriginalFilledMeromorphicFunctionRing N hN →+*
      MeromorphicGermRing (lpsOriginalLocalChartCenter N hN x) where
  toFun F := ⟨(F.val ∘ (lpsOriginalLocalChart N hN x).symm : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ),
    F.val ∘ (lpsOriginalLocalChart N hN x).symm,
    F.property x _ ((lpsOriginalLocalChart N hN x).map_source (lpsOriginalLocalChart_mem_source N hN x)), rfl⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
lemma lpsOriginalGlobalKernel_le_localKernel (x : LPSOriginalFilledCurve N) :
    RingHom.ker (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict ≤
      RingHom.ker (lpsOriginalRepresentativeToLocal N hN x) := by
  intro F hF
  change (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F = 0 at hF
  have hzero := congrArg Subtype.val hF
  have hg : F.val =ᶠ[Filter.codiscrete (LPSOriginalFilledCurve N)] 0 :=
    Filter.Germ.coe_eq.mp hzero
  let e := lpsOriginalLocalChart N hN x
  have hx : x ∈ e.source := lpsOriginalLocalChart_mem_source N hN x
  have ha : e x ∈ e.target := e.map_source hx
  have hp : F.val =ᶠ[𝓝[≠] x] 0 := by
    have hh := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hg x (Set.mem_univ x)
    have hh' : {y | F.val y = (0 : ℂ)} ∈ 𝓝[≠] x := by
      simpa only [Set.compl_univ, Set.union_empty, Pi.zero_apply] using hh
    exact hh'
  have ht : Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] x) := by
    have h : Tendsto e.symm (𝓝[≠] (e x)) (𝓝[≠] (e.symm (e x))) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(e.symm.continuousAt ha).tendsto.mono_left nhdsWithin_le_nhds,
          e.symm.eventually_ne_nhdsWithin ha⟩
    simpa only [e.left_inv hx] using h
  change lpsOriginalRepresentativeToLocal N hN x F = 0
  apply Subtype.ext
  change (F.val ∘ (lpsOriginalLocalChart N hN x).symm : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ) =
    (0 : Germ (𝓝[≠] lpsOriginalLocalChartCenter N hN x) ℂ)
  apply Filter.Germ.coe_eq.mpr
  exact ht.eventually hp
def lpsOriginalCompactToLocal (x : LPSOriginalFilledCurve N) :
    LPSOriginalCompactMeromorphicGermRing N hN →+*
      MeromorphicGermRing (lpsOriginalLocalChartCenter N hN x) :=
  ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.liftOfSurjective
    (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective)
    ⟨lpsOriginalRepresentativeToLocal N hN x, lpsOriginalGlobalKernel_le_localKernel N hN x⟩
def lpsOriginalFieldToLocal (hpos : 0 < N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    lpsOriginalGeneratedFunctionField N hpos →+* MeromorphicGermRing (lpsOriginalLocalChartCenter N hN x) :=
  (lpsOriginalCompactToLocal N hN x).comp
    (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN).toRingHom
def lpsOriginalFieldLocalOrder (hpos : 0 < N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    AddValuation (lpsOriginalGeneratedFunctionField N hpos) (WithTop ℤ) := by
  letI := lpsOriginalJFractionEmbedding.toAlgebra
  exact (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)).comap
    (lpsOriginalFieldToLocal N hN hpos x)
section ActualScalarAndCoordinate
variable (hpos : 0 < N)
local instance _p2m_local_instance_4f02bb1b4c_125 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local instance _p2m_local_instance_4f02bb1b4c_131 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_4f02bb1b4c_132 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_4f02bb1b4c_133 : Algebra ℂ L := ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.comp
  (lpsOriginalFilledMeromorphicComplexConstants N hN)).toAlgebra
local instance _p2m_local_instance_4f02bb1b4c_135 : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance _p2m_local_instance_4f02bb1b4c_136 : IsScalarTower ℂ P K := IsScalarTower.of_algebraMap_eq' rfl
end ActualScalarAndCoordinate
end
end QEC.Coding.TannerLiftedProduct


