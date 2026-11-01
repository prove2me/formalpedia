-- Prove2me | Definitions.Def_OAIQ075A007
-- name    : OAIQ075A007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:00:47.175134+00:00
-- url     : https://prove2.me/theorems/18844b90-1d10-475d-987f-cf86ddfb8c94
-- title:
--   Definitions bundle OAIQ075A007 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 188 declarations of OpenAI's Lean: 26 definitions, 5 instances and 157 theorems. The definitions and types are `OAI.BoundedHochschild.KadisonRingrose.compressCompletelyPositive`, `OAI.BoundedHochschild.KadisonRingrose.cpMatrixVectorFunctional`, `OAI.BoundedHochschild.KadisonRingrose.doubleCoordinate`, `OAI.BoundedHochschild.KadisonRingrose.doubleMatrixHom`, `OAI.BoundedHochschild.KadisonRingrose.normalUnitaryEquiv`, `OAI.BoundedHochschild.KadisonRingrose.operatorMatrixVectorFunctional`, `OAI.BoundedHochschild.KadisonRingrose.partialIsoFinsetSum`, `OAI.BoundedHochschild.KadisonRingrose.positiveSingularPart`, `OAI.BoundedHochschild.KadisonRingrose.projectionInCorner`, `OAI.BoundedHochschild.KadisonRingrose.vectorPositiveFunctional`, `OAI.BoundedHochschild.WeakAlgebra.traceRestriction`, `OAI.HochschildCorners.CornerPredual`, `OAI.HochschildCorners.cornerPredualEquiv`, `OAI.HochschildCorners.cornerStrongEquiv`, `OAI.HochschildCorners.weakCorner`, `OAI.HochschildMatrixDilation.diag`, `OAI.HochschildMatrixDilation.matrixMap`, `OAI.HochschildMatrixDilation.matrixTrace`, `OAI.HochschildMatrixDilation.matrixTraceLinear`, `OAI.HochschildMatrixDilation.offdiag`, `OAI.HochschildMatrixSystems.MatrixSystem.mapEquiv`, `OAI.HochschildNormalPart.hilbertNormalFunctional`, `OAI.HochschildNormalPart.scalarNormalPart`, `OAI.PopaCenter.average`, `OAI.PopaCenter.expectation`, `OAI.PopaCorners.CornerIso.final`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_AbelianCentralSupport`, `BoundedHochschild_AbelianComparison`, `BoundedHochschild_AbelianProjectionForms`, `BoundedHochschild_AbelianSupportEquivalence`, `BoundedHochschild_AdditivePositiveSupport`, `BoundedHochschild_CentralColumnCuts`, `BoundedHochschild_CentralProjectionSuprema`, `BoundedHochschild_CochainLimits`, `BoundedHochschild_CompleteAdditivity`, `BoundedHochschild_CompletelyPositiveCompression`, `BoundedHochschild_Corners`, `BoundedHochschild_Dixmier`, `BoundedHochschild_DoubleCoordinates`, `BoundedHochschild_FiniteCentralDecomposition`, `BoundedHochschild_FiniteCountableComparison`, `BoundedHochschild_FiniteIncreasingComparison`, `BoundedHochschild_FiniteNormalOrbit`, `BoundedHochschild_FiniteProjectionAbsoluteContinuity`, `BoundedHochschild_FiniteProjectionEquivalence`, `BoundedHochschild_FiniteProjectionExtension`, `BoundedHochschild_FiniteTraceCover`, `BoundedHochschild_FiniteTypeIPieces`, `BoundedHochschild_Frames`, `BoundedHochschild_HomogeneousCornerTransport`, `BoundedHochschild_IsometryDefectColumns`, `BoundedHochschild_MatrixDilation`, `BoundedHochschild_MixedWords`, `BoundedHochschild_NormalModulus`, `BoundedHochschild_NormalMultiplication`, `BoundedHochschild_NormalOperators`, `BoundedHochschild_NormalOrbitHull`, `BoundedHochschild_NormalVectors`, `BoundedHochschild_OperatorPrimitives`, `BoundedHochschild_OrthogonalPartialIsoSums`, `BoundedHochschild_OrthogonalProjectionSums`, `BoundedHochschild_OrthogonalProjectionTails`, `BoundedHochschild_PartialIsoCornerEquivalence`, `BoundedHochschild_PartialIsoProducts`, `BoundedHochschild_PartialIsometries`, `BoundedHochschild_PartialIsometryChains`, `BoundedHochschild_PaulsenExtension`, `BoundedHochschild_PositiveCompleteAdditivity`, `BoundedHochschild_PositiveCompression`, `BoundedHochschild_PositiveKernelMatrices`, `BoundedHochschild_PositiveNormalParts`, `BoundedHochschild_PowerRigidity`, `BoundedHochschild_PrimitiveAverages`, `BoundedHochschild_ProjectionChainSuprema`, `BoundedHochschild_ProjectionJoinComparison`, `BoundedHochschild_ProjectionPositivity`, `BoundedHochschild_ProjectionSequenceLimits`, `BoundedHochschild_SpectralProjections`, `BoundedHochschild_StinespringBounds`, `BoundedHochschild_TraceExpectations`, `BoundedHochschild_TraceFreeComparison`, `BoundedHochschild_TraceFreeProjectionJoins`, `BoundedHochschild_TraceFreeSeparation`, `BoundedHochschild_TracialTypeIHomogeneousPiece`, `BoundedHochschild_TypeICentralDecomposition`, `BoundedHochschild_TypeICentralPieces`, `BoundedHochschild_TypeICentralSupport`, `BoundedHochschild_TypeIColumnArithmetic`, `BoundedHochschild_TypeIColumnExtension`, `BoundedHochschild_TypeIIStructure`, `BoundedHochschild_TypeIMatrixColumns`, `BoundedHochschild_UnitaryPredualAction`, `BoundedHochschild_WeakAlgebras`, `TracialCohomology_CenterTrace`, `TracialCohomology_CornerComparison`, `TracialCohomology_HilbertNormalParts`, `WeakInfiniteness_MatrixRepresentation`.
--
--   **Imports.** It imports the bundles `OAIQ075A000`, `OAIQ075A001`, `OAIQ075A003` and `OAIQ075A004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A013`, `OAIQ075A014`, `OAIQ075A015`, `OAIQ075A016` and `OAIQ075A017`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A000
import Definitions.Def_OAIQ075A001
import Definitions.Def_OAIQ075A003
import Definitions.Def_OAIQ075A004

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CochainLimits
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-star cochain limits, averaging operators and preadjoints. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology



open Filter Topology



open Filter Topology
namespace BoundedHochschild
variable {M X I J : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_of_norm {a : I → M} {l : Filter I} {b : M}
    (h : Tendsto a l (𝓝 b)) : PredualTendsto e a l b := by
  intro z
  exact (((ContinuousLinearMap.apply ℂ ℂ) z).continuous.tendsto _).comp
    (e.symm.continuous.tendsto _ |>.comp h)

end BoundedHochschild
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixDilation
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix dilations, tracial matrix algebras and bounded linear maps. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildMatrixDilation
noncomputable section
open scoped Matrix ComplexOrder
open Complex
variable {A : Type*} [CStarAlgebra A]

def diag (a b : A) : Mat A := CStarMatrix.ofMatrix !![a,0;0,b]

def offdiag (a b : A) : Mat A := CStarMatrix.ofMatrix !![0,a;b,0]

@[simp] lemma diag_zero_zero : diag (0:A) 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma diag_one_one : diag (1:A) 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma diag_add (a b c d : A) : diag (a+c) (b+d) = diag a b + diag c d := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
@[simp] lemma diag_smul (z : ℂ) (a b : A) : diag (z • a) (z • b) = z • diag a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
@[simp] lemma diag_mul (a b c d : A) : diag a b * diag c d = diag (a*c) (b*d) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, CStarMatrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma star_diag (a b : A) : star (diag a b) = diag (star a) (star b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, CStarMatrix.star_eq_conjTranspose]
@[simp] lemma star_offdiag (a b : A) : star (offdiag a b) = offdiag (star b) (star a) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [offdiag, CStarMatrix.star_eq_conjTranspose]
@[simp] lemma offdiag_mul (a b c d : A) :
    offdiag a b * offdiag c d = diag (a*d) (b*c) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, offdiag, CStarMatrix.mul_apply, Fin.sum_univ_two]


variable [PartialOrder A] [StarOrderedRing A]

local instance instNonUnitalContinuousFunctionalCalculusRealMatIsSelfAdjoint : NonUnitalContinuousFunctionalCalculus ℝ (Mat A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance instNonnegSpectrumClassRealMat : NonnegSpectrumClass ℝ (Mat A) :=
  CStarAlgebra.instNonnegSpectrumClass

lemma diagEntry_nonneg (M : Mat A) (hM : 0 ≤ M) (i : Fin 2) : 0 ≤ M i i := by
  have hs := CFC.sqrt_nonneg M
  have he : M = star (CFC.sqrt M) * CFC.sqrt M := by
    rw [hs.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self M hM]
  rw [he, CStarMatrix.mul_apply]
  simp only [CStarMatrix.star_apply]
  exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg _

def matrixTraceLinear (τ : A →ₚ[ℂ] ℂ) : Mat A →ₗ[ℂ] ℂ where
  toFun M := (τ (M 0 0) + τ (M 1 1)) / 2
  map_add' M N := by simp only [CStarMatrix.add_apply, map_add]; ring
  map_smul' z M := by
    simp only [CStarMatrix.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

 
def matrixTrace (τ : A →ₚ[ℂ] ℂ) : Mat A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (matrixTraceLinear τ) (fun M hM =>
    div_nonneg (add_nonneg (τ.map_nonneg (diagEntry_nonneg M hM 0))
      (τ.map_nonneg (diagEntry_nonneg M hM 1))) (by norm_num))

@[simp] lemma matrixTrace_diag (τ : A →ₚ[ℂ] ℂ) (a b : A) :
    matrixTrace τ (diag a b) = (τ a + τ b)/2 := rfl

open scoped Matrix.Norms.Elementwise in
 
def matrixMap (R : A →L[ℂ] A) : Mat A →L[ℂ] Mat A where
  toLinearMap := CStarMatrix.mapₗ R.toLinearMap
  cont := by
    let e := CStarMatrix.ofMatrixL (m:=Fin 2) (n:=Fin 2) (A:=A)
    have hc : Continuous (fun M : Mat A => fun i j => R (e.symm M i j)) := by
      apply continuous_pi; intro i
      apply continuous_pi; intro j
      exact R.continuous.comp ((continuous_apply j).comp ((continuous_apply i).comp e.symm.continuous))
    exact e.continuous.comp hc

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixMap_apply (R : A →L[ℂ] A) (M : Mat A) (i j : Fin 2) :
    matrixMap R M i j = R (M i j) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixMap_diag (R : A →L[ℂ] A) (a b : A) :
    matrixMap R (diag a b) = diag (R a) (R b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]

end
end HochschildMatrixDilation
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PowerRigidity
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Approximate power identities and rigidity for contractions. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology

namespace HochschildMatrixDilation
noncomputable section
open scoped ComplexOrder
open Filter HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)

local instance powerRigidityMatrixContinuousFunctionalCalculus_r077768_1 :
    NonUnitalContinuousFunctionalCalculus ℝ (Mat A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
local instance powerRigidityMatrixNonnegSpectrum_r077768_1 : NonnegSpectrumClass ℝ (Mat A) :=
  CStarAlgebra.instNonnegSpectrumClass
omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma diag_pow (a b : A) (k : ℕ) : (diag a b)^k = diag (a^k) (b^k) := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ, ih, diag_mul]

end
end HochschildMatrixDilation
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PrimitiveAverages
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace preduals, primitives from averages and finite exactness. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)



omit [StarOrderedRing M] in
lemma trace_predual_tendsto (hτ : TraceInPredual e τ)
    {a : I → M} {l : Filter I} {b : M} (h : PredualTendsto e a l b) :
    Tendsto (fun i => τ (a i)) l (𝓝 (τ b)) := by
  obtain ⟨z,hz⟩ := hτ
  simpa only [hz] using (h z).star

 

lemma preGNS_norm_le_of_predual_tendsto
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) {a : I → M} {l : Filter I} [l.NeBot] {b : M}
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖τ.toPreGNS (a i)‖ ≤ C)
    (h : PredualTendsto e a l b) : ‖τ.toPreGNS b‖ ≤ C := by
  have ht := trace_predual_tendsto e τ hτ ((hL (star b)).tendsto e h)
  have ht' : Tendsto (fun i => inner ℂ (τ.toPreGNS b) (τ.toPreGNS (a i))) l
      (𝓝 (inner ℂ (τ.toPreGNS b) (τ.toPreGNS b))) := by
    simpa only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,ContinuousLinearMap.mul_apply'] using ht
  have hb : ‖inner ℂ (τ.toPreGNS b) (τ.toPreGNS b)‖ ≤ ‖τ.toPreGNS b‖ * C := by
    apply le_of_tendsto ht'.norm
    filter_upwards [ha] with i hi
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hi (norm_nonneg _))
  simp only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at hb
  nlinarith [norm_nonneg (τ.toPreGNS b)]

end BoundedHochschild



open Filter Topology
open scoped ComplexOrder



open MeasureTheory Filter Topology
open scoped ENNReal



open MeasureTheory Filter Topology
open scoped ComplexOrder



open Filter Topology
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalModulus
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal cochains, bounded-ball continuity and primitive construction. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)



theorem exists_bounded_preGNS_limit
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) {a : ℕ → M} (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C)
    (hc : CauchySeq (fun i => τ.toPreGNS (a i))) :
    ∃ b : M, ‖b‖ ≤ C ∧ Tendsto (fun i => ‖τ.toPreGNS (a i-b)‖) atTop (𝓝 0) := by
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  have hu : (u : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨b,hb,ht⟩ := exists_predual_ultralimit e u a C ha
  refine ⟨b,hb,?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hsmall : ∀ᶠ m in (u : Filter ℕ), ‖τ.toPreGNS (a n-a m)‖ ≤ ε/2 := by
    apply hu
    filter_upwards [eventually_ge_atTop N] with m hm
    simpa only [map_sub,← dist_eq_norm] using (hN n hn m hm).le
  have hbound := preGNS_norm_le_of_predual_tendsto e τ hL hτ (ε/2) (half_pos hε).le
    hsmall (predual_tendsto_sub e (predual_tendsto_const e (a n) (u : Filter ℕ)) ht)
  simpa only [Real.dist_eq,sub_zero,abs_norm] using hbound.trans_lt (half_lt_self hε)

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TraceExpectations
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace pairing norms, predual vectors and trace-preserving expectations. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder



open scoped ComplexOrder



open scoped ComplexOrder
namespace BoundedHochschild
open HochschildTraceNorm
variable {N X : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (τ : N →ₚ[ℂ] ℂ)

variable (hL : ∀ b : N, HasPreadjoint e (ContinuousLinearMap.mul ℂ N b))
  (hτ : TraceInPredual e τ)

lemma norm_traceVector (b : N) :
    ‖traceVector e τ hL hτ b‖=‖tracePair τ (star b)‖ := by
  apply le_antisymm
  · apply NormedSpace.norm_le_dual_bound ℂ _ (norm_nonneg _)
    intro f
    have hs := congrArg norm (traceVector_spec e τ hL hτ b (e f))
    simp only [e.symm_apply_apply,norm_star] at hs
    rw [hs]
    simpa only [e.norm_map,tracePair_apply] using (tracePair τ (star b)).le_opNorm (e f)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    have hs := congrArg norm (traceVector_spec e τ hL hτ b a)
    simp only [norm_star] at hs
    change ‖τ (star b*a)‖ ≤ _
    rw [← hs]
    simpa only [e.symm.norm_map,mul_comm] using (e.symm a).le_opNorm (traceVector e τ hL hτ b)

end BoundedHochschild

 

open scoped ComplexOrder



open scoped ComplexOrder



open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_SpectralProjections
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support projections, power limits and density of projection spans. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
open scoped ComplexOrder



open Filter Topology



open Filter Topology

namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in
 

theorem projection_span_dense :
    (Submodule.span ℂ {p : M | IsStarProjection p}).topologicalClosure=⊤ := by
  let S := (Submodule.span ℂ {p : M | IsStarProjection p}).topologicalClosure
  let : IsClosed (S : Set M) := Submodule.isClosed_topologicalClosure _
  apply top_unique
  intro a _
  change a ∈ S
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro F
  have hzero : F.comp S.mkQL=0 := dual_zero_of_projection_zero e (F.comp S.mkQL) (by
    intro p hp
    have hm : p ∈ S := (Submodule.le_topologicalClosure _)
      (Submodule.subset_span hp)
    have hh : (Submodule.Quotient.mk (p := S) p : M ⧸ S)=0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr hm
    change F (Submodule.Quotient.mk p)=0
    rw [hh,map_zero])
  exact congrArg (fun G : StrongDual ℂ M => G a) hzero

end HochschildSakai
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalMultiplication
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preadjoints for left and right multiplication. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)


variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

 

theorem mul_hasPreadjoint (a : M) : HasPreadjoint e (ContinuousLinearMap.mul ℂ M a) := by
  intro z
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let K := starLeftMatrixMap e z
  let J := NormedSpace.inclusionInDoubleDual ℂ X
  let S := (LinearMap.range J.toLinearMap).comap K.toLinearMap
  have hc : IsClosed (S : Set M) := by
    change IsClosed (K ⁻¹' Set.range J)
    apply IsClosed.preimage (f := K) K.continuous
    exact (NormedSpace.inclusionInDoubleDualLi ℂ (E := X)).isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℂ {p : M | IsStarProjection p} ≤ S := by
    apply Submodule.span_le.mpr
    intro p hp
    obtain ⟨w,hw⟩ := projection_mul_hasPreadjoint e p hp z
    refine ⟨w,?_⟩
    ext f
    change f w=e.symm (star p*e f) z
    rw [hp.isSelfAdjoint.star_eq]
    simpa using (hw (e f)).symm
  have htop : (⊤ : Submodule ℂ M) ≤ S := by
    rw [← projection_span_dense e]
    exact Submodule.topologicalClosure_minimal _ hspan hc
  obtain ⟨w,hw⟩ := htop (show star a ∈ (⊤ : Submodule ℂ M) from Submodule.mem_top)
  refine ⟨w,fun b => ?_⟩
  have hh := congrArg (fun G : StrongDual ℂ (StrongDual ℂ X) => G (e.symm b)) hw
  change e.symm b w=e.symm (star (star a)*e (e.symm b)) z at hh
  simpa using hh.symm

 
theorem predual_tendsto_mul_left (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => a*b i) l (a*c) :=
  HasPreadjoint.tendsto e (mul_hasPreadjoint e a) hb

 
theorem mul_right_hasPreadjoint (a : M) :
    HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a) := by
  intro z
  obtain ⟨w,hw⟩ := exists_star_predual_vector e z
  obtain ⟨v,hv⟩ := mul_hasPreadjoint e (star a) w
  obtain ⟨u,hu⟩ := exists_star_predual_vector e v
  refine ⟨u,fun b => ?_⟩
  have hh := hw (star a*star b)
  simp only [star_mul,star_star] at hh
  have hvb : e.symm (star a*star b) w=e.symm (star b) v := by
    simpa using hv (star b)
  rw [hvb,hu b,star_star] at hh
  simpa using hh

 
theorem predual_tendsto_mul_right (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => b i*a) l (c*a) :=
  HasPreadjoint.tendsto e (mul_right_hasPreadjoint e a) hb

end HochschildSakai

 

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)



theorem abstract_multiplication_normal :
    (∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a)) ∧
    (∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a)) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact ⟨mul_hasPreadjoint e,mul_right_hasPreadjoint e⟩

end HochschildSakai
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalVectors
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.predualNormalEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal vectors and projections for Hilbert-space representations. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)



variable [CompleteSpace X]

omit [CompleteSpace X] in
lemma normalDual_comp {φ : StrongDual ℂ M} (hφ : φ ∈ normalDual e)
    (L : M →L[ℂ] M) (hL : BoundedHochschild.HasPreadjoint e L) :
    φ.comp L ∈ normalDual e := by
  obtain ⟨z,hz⟩ := (mem_normalDual e φ).mp hφ
  obtain ⟨w,hw⟩ := hL z
  exact (mem_normalDual e _).mpr ⟨w,fun a => by simp only [ContinuousLinearMap.comp_apply,hz,hw]⟩

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))


lemma normalVectors_mul {ξ : H} (hξ : ξ ∈ normalVectors e π) (b : M) :
    π b ξ ∈ normalVectors e π := by
  rw [mem_normalVectors] at hξ ⊢
  intro η
  have hc : coefficient π η (π b ξ) =
      (coefficient π η ξ).comp ((ContinuousLinearMap.mul ℂ M).flip b) := by
    ext a; simp [map_mul]
  rw [hc]
  exact normalDual_comp e (hξ η) _ ((HochschildSakai.abstract_multiplication_normal e).2 b)

lemma normalProjection_mul (a : M) :
    normalProjection e π*π a=π a*normalProjection e π := by
  apply projection_commutes
  · intro ξ hξ; exact normalVectors_mul e π hξ a
  · intro ξ hξ
    rw [← map_star]
    exact normalVectors_mul e π hξ (star a)



lemma cyclic_coefficients_normal (η ξ : H)
    (h : coefficient π η ξ ∈ normalDual e) {ζ : H} (hζ : ζ ∈ cyclicSpace π η) :
    coefficient π ζ ξ ∈ normalDual e := by
  let S := (normalDual e).comap (coefficientLeft π ξ).toLinearMap
  have hle : cyclicSpace π η ≤ S := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨b,rfl⟩
      change coefficient π (π b η) ξ ∈ normalDual e
      have hc : coefficient π (π b η) ξ=(coefficient π η ξ).comp
          (ContinuousLinearMap.mul ℂ M (star b)) := by
        ext a
        change ⟪π b η,π a ξ⟫_ℂ=⟪η,π (star b*a) ξ⟫_ℂ
        rw [map_mul,mul_apply_eq_comp,map_star]
        exact (ContinuousLinearMap.adjoint_inner_right (π b) η (π a ξ)).symm
      rw [hc]
      exact normalDual_comp e h _ ((HochschildSakai.abstract_multiplication_normal e).1 _)
    · exact (normalDual_closed e).preimage (coefficientLeft π ξ).continuous
  exact hle hζ

 

lemma normalProjection_fixes_normal (η ξ : H)
    (h : coefficient π η ξ ∈ normalDual e) :
    coefficient π η (normalProjection e π ξ)=coefficient π η ξ := by
  let K := cyclicSpace π η
  let Q := K.starProjection
  have hQ : ∀ a : M, Q*π a=π a*Q := cyclicProjection_mul π η
  have hcoef (ζ : H) : coefficient π ζ (Q ξ)=coefficient π (Q ζ) ξ := by
    ext a
    change ⟪ζ,π a (Q ξ)⟫_ℂ=⟪Q ζ,π a ξ⟫_ℂ
    have hc := congrArg (fun T : H →L[ℂ] H => T ξ) (hQ a)
    change Q (π a ξ)=π a (Q ξ) at hc
    rw [← hc]
    exact (K.inner_starProjection_left_eq_right ζ (π a ξ)).symm
  have hn : Q ξ ∈ normalVectors e π := by
    rw [mem_normalVectors]
    intro ζ
    rw [hcoef]
    exact cyclic_coefficients_normal e π η ξ h (by simp [Q,K])
  have hP : normalProjection e π (Q ξ)=Q ξ :=
    Submodule.starProjection_eq_self_iff.mpr hn
  have hcomm := congrArg (fun T : H →L[ℂ] H => T ξ) (normalProjection_commutant e π Q hQ)
  change normalProjection e π (Q ξ)=Q (normalProjection e π ξ) at hcomm
  have hη : Q η=η := Submodule.starProjection_eq_self_iff.mpr (cyclicSpace_mem π η)
  calc
    coefficient π η (normalProjection e π ξ) = coefficient π (Q η) (normalProjection e π ξ) := by rw [hη]
    _ = coefficient π η (Q (normalProjection e π ξ)) := by
      ext a
      change ⟪Q η,π a (normalProjection e π ξ)⟫_ℂ=⟪η,π a (Q (normalProjection e π ξ))⟫_ℂ
      rw [K.inner_starProjection_left_eq_right]
      exact congrArg (inner ℂ η) (congrArg (fun T : H →L[ℂ] H => T (normalProjection e π ξ)) (hQ a))
    _ = coefficient π η (Q ξ) := by rw [← hcomm,hP]
    _ = coefficient π (Q η) ξ := hcoef η
    _ = coefficient π η ξ := by rw [hη]

end HochschildNormalPart

 

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v w
variable {M : Type u} [CStarAlgebra M]
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]


variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))



lemma coefficient_normal_eq_of_eq
    (η ξ : H) (ζ ω : K) (h : coefficient π η ξ=coefficient ρ ζ ω) :
    coefficient π η (normalProjection e π ξ)=coefficient ρ ζ (normalProjection e ρ ω) := by
  let A : WithLp 2 (H×K) := WithLp.toLp 2 (η,ζ)
  let B : WithLp 2 (H×K) := WithLp.toLp 2 (ξ,-ω)
  have hz : coefficient (sumRepresentation π ρ) A B=0 := by
    rw [coefficient_sum]
    change coefficient π η ξ+coefficient ρ ζ (-ω)=0
    rw [map_neg,h,add_neg_cancel]
  have hn : coefficient (sumRepresentation π ρ) A B ∈ normalDual e := hz ▸ (normalDual e).zero_mem
  have hp := normalProjection_fixes_normal e (sumRepresentation π ρ) A B hn
  rw [hz,normalProjection_sum,coefficient_sum] at hp
  change coefficient π η (normalProjection e π ξ)+coefficient ρ ζ (normalProjection e ρ (-ω))=0 at hp
  rw [map_neg,map_neg] at hp
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hp)

end HochschildNormalPart
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalOperators
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.predualNormalEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal parts of scalar functionals and bounded operators. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
namespace HochschildNormalPart
universe u
attribute [instance] FunctionalModel.normed FunctionalModel.innerSpace FunctionalModel.complete

end HochschildNormalPart

 

namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma normalPartRaw_coefficient (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    normalPartRaw e (coefficient π η ξ)=coefficient π η (normalProjection e π ξ) := by
  exact coefficient_normal_eq_of_eq e _ π _ _ η ξ (functionalModel _).realizes

lemma normalPartRaw_add (φ ψ : StrongDual ℂ M) :
    normalPartRaw e (φ+ψ)=normalPartRaw e φ+normalPartRaw e ψ := by
  let m := functionalModel φ
  let n := functionalModel ψ
  let π := sumRepresentation m.representation n.representation
  let η : WithLp 2 (m.H×n.H) := WithLp.toLp 2 (m.leftVector,n.leftVector)
  let ξ : WithLp 2 (m.H×n.H) := WithLp.toLp 2 (m.rightVector,n.rightVector)
  have hc : coefficient π η ξ=φ+ψ := by
    rw [coefficient_sum]
    change coefficient m.representation m.leftVector m.rightVector+
      coefficient n.representation n.leftVector n.rightVector=φ+ψ
    rw [m.realizes,n.realizes]
  rw [← hc,normalPartRaw_coefficient,normalProjection_sum,coefficient_sum]
  rfl

lemma normalPartRaw_smul (r : ℂ) (φ : StrongDual ℂ M) :
    normalPartRaw e (r • φ)=r • normalPartRaw e φ := by
  let m := functionalModel φ
  have hc : coefficient m.representation m.leftVector (r • m.rightVector)=r • φ := by
    rw [map_smul,m.realizes]
  rw [← hc,normalPartRaw_coefficient,map_smul,map_smul]
  rfl



def scalarNormalPart : StrongDual ℂ M →L[ℂ] StrongDual ℂ M :=
  LinearMap.mkContinuous
    { toFun := normalPartRaw e
      map_add' := normalPartRaw_add e
      map_smul' := normalPartRaw_smul e } 4 (normalPartRaw_norm e)

@[simp] lemma scalarNormalPart_coefficient (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    scalarNormalPart e (coefficient π η ξ)=coefficient π η (normalProjection e π ξ) :=
  normalPartRaw_coefficient e π η ξ

lemma scalarNormalPart_norm : ‖scalarNormalPart e‖≤4 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) (normalPartRaw_norm e)

lemma scalarNormalPart_mem (φ : StrongDual ℂ M) : scalarNormalPart e φ ∈ normalDual e := by
  apply (mem_normalVectors e (functionalModel φ).representation _).mp
  simp [normalProjection]

lemma scalarNormalPart_fixes {φ : StrongDual ℂ M} (hφ : φ ∈ normalDual e) :
    scalarNormalPart e φ=φ := by
  let m := functionalModel φ
  change coefficient m.representation m.leftVector (normalProjection e m.representation m.rightVector)=φ
  rw [normalProjection_fixes_normal e _ _ _ (m.realizes.symm ▸ hφ),m.realizes]

end HochschildNormalPart



end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Dixmier
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.PopaCorner.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert-space averaging and central elements in unitary orbit closures. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDixmier
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

include e hL hτ in
 

theorem isClosed_gns_ball (C : ℝ) :
    IsClosed (gnsVector τ '' Metric.closedBall (0 : M) C) := by
  apply isSeqClosed_iff_isClosed.mp
  intro y z hy hz
  choose a ha hay using hy
  have hnorm : ∀ n, ‖a n‖ ≤ C := fun n => by simpa only [Metric.mem_closedBall,dist_zero_right] using ha n
  have hc : CauchySeq (fun n => τ.toPreGNS (a n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hz.cauchySeq ε hε
    refine ⟨N,fun m hm n hn => ?_⟩
    rw [dist_eq_norm,← map_sub,← gnsVector_norm τ, map_sub,hay m,hay n,← dist_eq_norm]
    exact hN m hm n hn
  obtain ⟨b,hb,ht⟩ := exists_bounded_preGNS_limit e τ hL hτ C hnorm hc
  have ht' : Tendsto (fun n => gnsVector τ (a n)) atTop (𝓝 (gnsVector τ b)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [← map_sub,gnsVector_norm] using ht
  have he : gnsVector τ b=z := tendsto_nhds_unique ht' (by simpa only [hay] using hz)
  exact ⟨b,by simpa only [Metric.mem_closedBall,dist_zero_right] using hb,he⟩

include e hL hτ in
 

theorem orbit_closure_lift (a : M) {z : τ.GNS}
    (hz : z ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) :
    ∃ b : M, ‖b‖ ≤ ‖a‖ ∧ gnsVector τ b=z := by
  have hsub : closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) ⊆
      gnsVector τ '' Metric.closedBall (0 : M) ‖a‖ :=
    closure_minimal (Set.image_mono (orbit_hull_bounded a)) (isClosed_gns_ball e τ hL hτ ‖a‖)
  obtain ⟨b,hb,hbz⟩ := hsub hz
  exact ⟨b,by simpa only [Metric.mem_closedBall,dist_zero_right] using hb,hbz⟩

include e hL hτ in
 

theorem exists_central_average (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ x : M, τ (star x*x)=0 → x=0) (a : M) :
    ∃ b : M, ‖b‖ ≤ ‖a‖ ∧ (∀ x : M, Commute b x) ∧
      gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
        (Set.range (fun v : unitary M => conjugate v a))) := by
  let := InnerProductSpace.rclikeToReal ℂ τ.GNS
  let K := closure (gnsVector τ '' convexHull ℝ
    (Set.range (fun v : unitary M => conjugate v a)))
  have hne : K.Nonempty := ⟨gnsVector τ (conjugate 1 a),
    subset_closure ⟨conjugate 1 a,subset_convexHull ℝ _ ⟨1,rfl⟩,rfl⟩⟩
  obtain ⟨z,hz,hmin⟩ := exists_min_norm hne isClosed_closure (orbit_gns_convex τ a)
  obtain ⟨b,hb,hbz⟩ := orbit_closure_lift e τ hL hτ a hz
  have hbmem : gnsVector τ b ∈ K := hbz ▸ hz
  have hfix : ∀ u : unitary M, conjugate u b=b := by
    intro u
    have he : gnsVector τ (conjugate u b)=gnsVector τ b := by
      apply min_norm_unique (orbit_gns_convex τ a) hbmem
        (conjugate_mem_orbit_closure τ htr a b hbmem u)
      · intro y hy; rw [hbz]; exact hmin y hy
      · exact conjugate_gns_norm τ htr u b
    apply sub_eq_zero.mp
    apply (preGNS_norm_eq_zero_iff τ hfaith _).mp
    rw [← gnsVector_norm τ,map_sub,he,sub_self,norm_zero]
  have hucomm : ∀ u : unitary M, Commute b (u : M) := by
    intro u
    have he := congrArg (fun x : M => x*(u : M)) (hfix u)
    simp only [conjugate_apply,mul_assoc,Unitary.star_mul_self_of_mem u.prop,mul_one] at he
    exact he.symm
  refine ⟨b,hb,?_,hbmem⟩
  intro x
  have hx : x ∈ Submodule.span ℂ (unitary M : Set M) := by
    rw [CStarAlgebra.span_unitary]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hucomm ⟨y,hy⟩
  | zero => exact Commute.zero_right b
  | add y z hy hz ihy ihz => exact ihy.add_right ihz
  | smul r y hy ih => exact ih.smul_right r

end HochschildDixmier
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_OperatorPrimitives
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitives on operator algebras and polar partial isometries. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra



open Filter Topology
namespace HochschildPolar
open BoundedHochschild HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in
 

theorem exists_polar_contraction (b : M) :
    ∃ v : M, ‖v‖ ≤ 1 ∧ b=v*CFC.abs b ∧ CFC.abs b=star v*b := by
  classical
  have hpos (n : ℕ) : 0 < (1:ℝ)/((n:ℝ)+1) := by positivity
  choose v hv hleft hright using
    fun n : ℕ => HochschildTraceNorm.exists_approx_polar b _ (hpos n)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨w,hw,ht⟩ := exists_predual_ultralimit e U v 1 hv
  have hε : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun n => v n*CFC.abs b) atTop (𝓝 b) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) _ hε
    intro n
    rw [norm_sub_rev]
    exact hleft n
  have hr : Tendsto (fun n => star (v n)*b) atTop (𝓝 (CFC.abs b)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) _ hε
    intro n
    rw [norm_sub_rev]
    exact hright n
  exact ⟨w,hw,
    predual_tendsto_unique e (predual_tendsto_of_norm e (hl.mono_left hU))
      (predual_tendsto_mul_right e _ ht),
    predual_tendsto_unique e (predual_tendsto_of_norm e (hr.mono_left hU))
      (predual_tendsto_mul_right e _ (predual_tendsto_star e ht))⟩

include e in
 

theorem exists_polar_partial_isometry (b : M) :
    ∃ v p q : M, IsSupportProjection (CFC.abs b) p ∧
      star v*v=p ∧ v*star v=q ∧ IsStarProjection q ∧ b=v*CFC.abs b ∧
      v*p=v ∧ q*b=b := by
  obtain ⟨w,hw,hb,ha⟩ := exists_polar_contraction e b
  obtain ⟨p,hp⟩ := HochschildSakai.exists_support_projection e (CFC.abs b) (CFC.abs_nonneg b)
  let v := w*p
  have hvp : v*p=v := by
    dsimp [v]
    rw [mul_assoc,hp.proj.isIdempotentElem.eq]
  have hvb : v*CFC.abs b=b := by
    dsimp [v]
    rw [mul_assoc,hp.left,← hb]
  have hv : star v*b=CFC.abs b := by
    dsimp [v]
    rw [star_mul,hp.proj.isSelfAdjoint.star_eq,mul_assoc,← ha,hp.left]
  have hinit : star v*v=p := by
    have hz : (star v*v-p)*CFC.abs b=0 := by
      rw [sub_mul,mul_assoc,hvb,hv,hp.left,sub_self]
    have hh := support_right_annihilate hp (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)) hz
    rw [sub_mul,mul_assoc,hvp,hp.proj.isIdempotentElem.eq,sub_eq_zero] at hh
    exact hh
  have hfinal : IsStarProjection (v*star v) := by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc
        _ = v*(star v*v)*star v := by simp only [mul_assoc]
        _ = v*star v := by rw [hinit,hvp]
    · exact IsSelfAdjoint.mul_star_self v
  refine ⟨v,p,v*star v,hp,hinit,rfl,hfinal,hvb.symm,hvp,?_⟩
  rw [mul_assoc,hv,hvb]

end HochschildPolar
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsometries
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial isometries and comparison of equal-trace projections. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M]

namespace PartialIso
lemma norm_le_one (v : PartialIso M) : ‖(v : M)‖ ≤ 1 := by
  have hi := v.initial_proj.norm_le _
  have he : ‖(v : M)‖ * ‖(v : M)‖ = ‖v.initial‖ := by
    exact CStarRing.norm_star_mul_self.symm
  nlinarith [norm_nonneg (v : M)]

variable [PartialOrder M]

variable [StarOrderedRing M]

instance instPartialOrder : PartialOrder (PartialIso M) where
  le_refl v := ⟨le_rfl, v.mul_initial⟩
  le_trans v w z hvw hwz := by
    refine ⟨hvw.1.trans hwz.1, ?_⟩
    calc
      (z : M) * v.initial = (z : M) * (w.initial * v.initial) := by
        rw [(v.initial_proj.le_iff_mul_eq_right w.initial_proj).mp hvw.1]
      _ = (w : M) * v.initial := by rw [← mul_assoc,hwz.2]
      _ = v := hvw.2
  le_antisymm v w hvw hwv := by
    apply ext
    have he := le_antisymm hvw.1 hwv.1
    have hh := hvw.2
    rw [he, w.mul_initial] at hh
    exact hh.symm

omit [StarOrderedRing M] in
lemma initial_mono {v w : PartialIso M} (h : v ≤ w) : v.initial ≤ w.initial := h.1
lemma star_mul_of_le {v w : PartialIso M} (h : v ≤ w) : star (v : M) * w = v.initial := by
  have hv := congrArg star h.2
  simp only [star_mul, v.initial_proj.isSelfAdjoint.star_eq] at hv
  calc
    star (v : M) * w = (v.initial * star (w : M)) * w := by rw [hv]
    _ = v.initial * w.initial := by simp only [initial,mul_assoc]
    _ = v.initial := (v.initial_proj.le_iff_mul_eq_left w.initial_proj).mp h.1
lemma star_mul_of_ge {v w : PartialIso M} (h : v ≤ w) : star (w : M) * v = v.initial := by
  simpa only [star_mul,star_star,v.initial_proj.isSelfAdjoint.star_eq]
    using congrArg star (star_mul_of_le h)
lemma final_mono {v w : PartialIso M} (h : v ≤ w) : v.final ≤ w.final := by
  apply (v.final_proj.le_iff_mul_eq_right w.final_proj).mpr
  calc
    w.final * v.final = (w : M) * (star (w : M) * v) * star (v : M) := by
      simp only [final,mul_assoc]
    _ = (w : M) * v.initial * star (v : M) := by rw [star_mul_of_ge h]
    _ = v.final := by rw [h.2]; rfl

lemma le_orthogonalSum (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : v ≤ orthogonalSum v w hi hf := by
  constructor
  · rw [orthogonalSum_initial]
    exact le_add_of_nonneg_right w.initial_proj.nonneg
  · change ((v : M)+w)*v.initial=v
    rw [add_mul,v.mul_initial]
    have hh : (w : M)*v.initial=0 := by
      calc
        (w : M)*v.initial = ((w : M)*w.initial)*v.initial := by rw [w.mul_initial]
        _ = 0 := by rw [mul_assoc,orthogonal_initial_symm hi,mul_zero]
    rw [hh,add_zero]

end PartialIso
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild HochschildRigidity HochschildDixmier
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e in
lemma partialIso_of_nonzero_corner [CompleteSpace X]
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (b : M) (hb : b ≠ 0) (hpb : p*b=b) (hbq : b*q=b) :
    ∃ v : PartialIso M, (v : M) ≠ 0 ∧ v.initial ≤ q ∧ v.final ≤ p := by
  obtain ⟨v,r,s,hr,hvr,hvs,hs,hbabs,hvrv,_hsb⟩ :=
    HochschildPolar.exists_polar_partial_isometry e b
  have hva : star v*b=CFC.abs b := by
    calc
      star v*b = star v*(v*CFC.abs b) := congrArg (star v * ·) hbabs
      _ = CFC.abs b := by rw [← mul_assoc,hvr,hr.left]
  have hvp : p*v=v := by
    have hz : ((1-p)*v)*CFC.abs b=0 := by
      rw [mul_assoc,← hbabs,sub_mul,one_mul,hpb,sub_self]
    have hz' := HochschildPolar.support_right_annihilate hr
      (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)) hz
    rw [mul_assoc,hvrv,sub_mul,one_mul,sub_eq_zero] at hz'
    exact hz'.symm
  have hrq : r*q=r := by
    have ha : CFC.abs b*(1-q)=0 := by
      rw [← hva,mul_assoc,mul_sub,mul_one,hbq,sub_self,mul_zero]
    have hz := hr.annihilate (1-q) ha
    simpa only [mul_sub,mul_one,sub_eq_zero,eq_comm] using hz
  have hvpartial : v*star v*v=v := by rw [mul_assoc,hvr,hvrv]
  let w : PartialIso M := ⟨v,hvpartial⟩
  refine ⟨w,?_,?_,?_⟩
  · intro hv0
    change v=0 at hv0
    apply hb
    simpa only [hv0,zero_mul] using hbabs
  · change star v*v ≤ q
    rw [hvr]
    exact (hr.proj.le_iff_mul_eq_left hq).mpr hrq
  · apply (w.final_proj.le_iff_mul_eq_right hp).mpr
    change p*(v*star v)=v*star v
    rw [← mul_assoc,hvp]

end HochschildComparison
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MixedWords
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-word Taylor expansions, moment corners and patch coefficients. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M : Type*} [CStarAlgebra M]


variable {I : Type*} (F : I → M)
@[simp] lemma wordCoeff_none : wordCoeff F none=1 := rfl
end HochschildPatching

 

 

open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_WeakAlgebras
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-star algebra closures, inherited traces and generated finite-path primitives. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma normal_continuous (A : M →L[ℂ] M) (hA : HasPreadjoint e A) :
    Continuous (fun f : WeakDual ℂ X => (weakEquiv e).symm (A (weakEquiv e f))) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ X)
  intro z
  obtain ⟨w,hw⟩ := hA z
  change Continuous (fun f : WeakDual ℂ X => e.symm (A (weakEquiv e f)) z)
  simp_rw [hw]
  simpa [weakEquiv] using WeakDual.eval_continuous (𝕜 := ℂ) w

end WeakAlgebra
end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
namespace WeakAlgebra
open HochschildTraceNorm
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (A : StarSubalgebra ℂ M)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))
  (hτ : TraceInPredual e τ)

lemma traceVector_norm_bound (b : M) :
    ‖traceVectorLinear e τ hL hτ b‖ ≤ ‖traceCLM τ‖*‖b‖ := by
  rw [traceVectorLinear_apply,norm_traceVector]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro a
  calc
    ‖tracePair τ (star b) a‖ ≤ ‖traceCLM τ‖*‖star b*a‖ := (traceCLM τ).le_opNorm _
    _ ≤ ‖traceCLM τ‖*(‖b‖*‖a‖) := mul_le_mul_of_nonneg_left
      (by simpa using norm_mul_le (star b) a) (norm_nonneg _)
    _ = (‖traceCLM τ‖*‖b‖)*‖a‖ := (mul_assoc _ _ _).symm

def traceRestriction : A →L[ℂ] (X ⧸ WeakSubspace.preannihilator (linearClosure e A)) :=
  (WeakSubspace.preannihilator (linearClosure e A)).mkQL.comp
    (((traceVectorLinear e τ hL hτ).mkContinuous ‖traceCLM τ‖
      (traceVector_norm_bound e τ hL hτ)).comp
      { toLinearMap := A.toSubalgebra.toSubmodule.subtype
        cont := continuous_subtype_val })

@[simp] lemma traceRestriction_apply (a : A) :
    traceRestriction e τ A hL hτ a=
      Submodule.Quotient.mk (traceVectorLinear e τ hL hτ (a:M)) := rfl

end WeakAlgebra
end BoundedHochschild



open Filter Topology
open scoped ComplexOrder




open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Corners
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral corners, corner preduals and factor structure. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma projection_mem_corner {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q ≤ p) : q ∈ corner p hp :=
  ⟨(hq.le_iff_mul_eq_right hp).mp hqp,(hq.le_iff_mul_eq_left hp).mp hqp⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma compress_mem_corner {p : M} (hp : IsStarProjection p) (a : M) :
    p*a*p ∈ corner p hp := by
  exact ⟨by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq],
    by rw [mul_assoc,hp.isIdempotentElem.eq]⟩

end HochschildCorners

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild BoundedHochschild.WeakAlgebra HochschildRigidity HochschildSakai
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p)

instance cornerStarOrderedRing : StarOrderedRing (Corner p hp) :=
  StarOrderedRing.of_nonneg_iff' (fun {a b} h c => show (c:M)+(a:M) ≤ (c:M)+(b:M) from add_le_add le_rfl (show (a:M) ≤ (b:M) from h))
    (fun a => by
      constructor
      · intro ha
        have haM : (0:M) ≤ (a:M) := ha
        have hs : CFC.sqrt (a:M) ∈ corner p hp := by
          rw [CFC.sqrt_eq_real_sqrt (a:M) haM]
          exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
        refine ⟨⟨CFC.sqrt (a:M),hs⟩,Subtype.ext ?_⟩
        change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
        rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq,CFC.sqrt_mul_sqrt_self (a:M) haM]
      · rintro ⟨b,rfl⟩
        exact star_mul_self_nonneg (b:M))

section Predual
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def weakCorner : Submodule ℂ (WeakDual ℂ X) where
  carrier := {f | weakEquiv e f ∈ corner p hp}
  zero_mem' := by
    change weakEquiv e 0 ∈ corner p hp
    rw [map_zero]
    exact (corner p hp).zero_mem
  add_mem' := by
    intro a b ha hb
    change weakEquiv e (a+b) ∈ corner p hp
    rw [map_add]
    exact (corner p hp).add_mem ha hb
  smul_mem' := by
    intro c a ha
    change weakEquiv e (c • a) ∈ corner p hp
    rw [LinearEquiv.map_smulₛₗ]
    exact (corner p hp).smul_mem (star c) ha

lemma weakCorner_closed : IsClosed (weakCorner p hp e : Set (WeakDual ℂ X)) := by
  have hL := mul_hasPreadjoint e p
  have hR := mul_right_hasPreadjoint e p
  have hLeft := isClosed_eq (normal_continuous e _ hL) (continuous_id : Continuous (id : WeakDual ℂ X → _))
  have hRight := isClosed_eq (normal_continuous e _ hR) (continuous_id : Continuous (id : WeakDual ℂ X → _))
  change IsClosed {f | (weakEquiv e).symm (p*weakEquiv e f)=f} at hLeft
  change IsClosed {f | (weakEquiv e).symm (weakEquiv e f*p)=f} at hRight
  convert hLeft.inter hRight using 1
  all_goals try with_reducible_and_instances rfl
  ext f
  change (p*weakEquiv e f=weakEquiv e f ∧ weakEquiv e f*p=weakEquiv e f) ↔
    ((weakEquiv e).symm (p*weakEquiv e f)=f ∧ (weakEquiv e).symm (weakEquiv e f*p)=f)
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨by rw [h,LinearEquiv.symm_apply_apply],by rw [h',LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨h,h'⟩
    exact ⟨by simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e) h,
      by simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e) h'⟩

def CornerPredual := X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)
instance instNormedAddCommGroupCornerPredual : NormedAddCommGroup (CornerPredual p hp e) := inferInstanceAs
  (NormedAddCommGroup (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))
instance instNormedSpaceComplexCornerPredual : NormedSpace ℂ (CornerPredual p hp e) := inferInstanceAs
  (NormedSpace ℂ (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))
instance instCompleteSpaceCornerPredual : CompleteSpace (CornerPredual p hp e) := inferInstanceAs
  (CompleteSpace (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))

def cornerStrongEquiv : WeakSubspace.strong (weakCorner p hp e) ≃ₗᵢ⋆[ℂ] Corner p hp where
  toFun f := ⟨e f.val,by
    have hf := (WeakSubspace.mem_strong (weakCorner p hp e) f.val).mp f.property
    exact hf⟩
  invFun a := ⟨e.symm a.val,by
    rw [WeakSubspace.mem_strong]
    change e (e.symm a.val) ∈ corner p hp
    simpa only [LinearIsometryEquiv.apply_symm_apply] using a.property⟩
  left_inv f := Subtype.ext (e.symm_apply_apply f.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)
  map_add' f g := Subtype.ext (map_add e f.val g.val)
  map_smul' c f := Subtype.ext (e.map_smulₛₗ c f.val)
  norm_map' f := e.norm_map f.val

def cornerPredualEquiv : StrongDual ℂ (CornerPredual p hp e) ≃ₗᵢ⋆[ℂ] Corner p hp :=
  (WeakSubspace.quotientDualEquiv (weakCorner p hp e) (weakCorner_closed p hp e)).trans
    (cornerStrongEquiv p hp e)

end Predual
end HochschildCorners

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)

lemma corner_projection_le {q : Corner p hp} (hq : IsStarProjection q) : (q:M) ≤ p :=
  ((corner_projection_coe p hp hq).le_iff_mul_eq_left hp).mpr q.property.2

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma cornerTrace_tracial (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (a b : Corner p hp) : cornerTrace p hp τ (a*b)=cornerTrace p hp τ (b*a) := by
  simp only [cornerTrace_apply,corner_coe_mul,htr a.val b.val]

lemma cornerTrace_faithful (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hp0 : p ≠ 0)
    (a : Corner p hp) (ha : cornerTrace p hp τ (star a*a)=0) : a=0 := by
  have hne : ((τ p).re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne'
  have hh := (mul_eq_zero.mp ha).resolve_left (inv_ne_zero hne)
  exact Subtype.ext (hfaith a.val hh)

end HochschildCorners

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeIIStructure
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection comparison and matrix structure in finite type-II algebras. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildTypeII
open BoundedHochschild HochschildRigidity HochschildDiffuse HochschildComparison
open FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma abelian_of_le {p q : M} (hp : AbelianProjection p)
    (hq : IsStarProjection q) (hqp : q ≤ p) : AbelianProjection q := by
  refine ⟨hq,?_⟩
  intro a b
  have he (x : M) : p*(q*x*q)*p=q*x*q := by
    rw [← mul_assoc,← mul_assoc,(hq.le_iff_mul_eq_right hp.1).mp hqp,
      mul_assoc,mul_assoc,(hq.le_iff_mul_eq_left hp.1).mp hqp,← mul_assoc]
  simpa only [he] using hp.2 (q*a*q) (q*b*q)

end HochschildTypeII

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Frames
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal frames of partial isometries and maximal frame construction. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace PartialIso

lemma restrict_le (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : v.restrict hp hpv ≤ v := by
  exact ⟨by simpa only [restrict_initial] using hpv,by simp only [restrict_initial,restrict_coe]⟩
end PartialIso

end HochschildComparison

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_AbelianComparison
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison with abelian projections. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildTypeII
open BoundedHochschild HochschildComparison FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma abelian_orthogonal_mul {p r t : M} (hp : AbelianProjection p)
    (hr : IsStarProjection r) (ht : IsStarProjection t) (hrp : r ≤ p) (htp : t ≤ p)
    (hrt : r*t=0) (a : M) : r*a*t=0 := by
  have hpr := (hr.le_iff_mul_eq_right hp.1).mp hrp
  have hrp' := (hr.le_iff_mul_eq_left hp.1).mp hrp
  have hpt := (ht.le_iff_mul_eq_right hp.1).mp htp
  have he : p*r*p=r := by rw [hpr,hrp']
  have hc := hp.2 r a
  rw [he] at hc
  calc
    r*a*t = r*(p*a*p)*t := by rw [← mul_assoc,← mul_assoc,hrp',mul_assoc,mul_assoc,hpt,← mul_assoc]
    _ = (p*a*p)*(r*t) := by rw [hc.eq,mul_assoc]
    _ = 0 := by rw [hrt,mul_zero]

end HochschildTypeII

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProjectionChainSuprema
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace-free suprema of chains of projections in a von Neumann algebra. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A bounded weak-star limit gives the supremum of a projection chain,
including its common annihilators. No trace is needed. -/
theorem exists_projection_chain_supremum_with_limit
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (S : Set M) (hne : S.Nonempty)
    (hchain : IsChain (· ≤ ·) S) (hproj : ∀ q ∈ S, IsStarProjection q) :
    ∃ p : M, IsStarProjection p ∧ (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) ∧
      ∃ U : Ultrafilter S, (U : Filter S) ≤ atTop ∧
        PredualTendsto e (fun q : S => (q : M)) (U : Filter S) p := by
  classical
  let : Nonempty S := hne.to_subtype
  let : IsDirectedOrder S := ⟨fun a b => by
    rcases hchain.total a.property b.property with hab | hba
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hba⟩⟩
  let U : Ultrafilter S := Ultrafilter.of atTop
  have hU : (U : Filter S) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨p, _, ht⟩ := exists_predual_ultralimit e U (fun q : S => (q : M)) 1
    (fun q => (hproj q q.property).norm_le)
  have hfixed (q : S) : (q : M) * p = q := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (q : M) ht
    have heq : (fun r : S => (q : M) * r) =ᶠ[U] (fun _ => (q : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop q] with r hqr
      exact ((hproj q q.property).le_iff_mul_eq_left (hproj r r.property)).mp hqr
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a z) h.symm)
  have hp : IsStarProjection p := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e p ht
      have heq : (fun q : S => (q : M) * p) = (fun q : S => (q : M)) :=
        funext hfixed
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hs := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun q : S => star (q : M)) = (fun q : S => (q : M)) := by
        funext q
        exact (hproj q q.property).isSelfAdjoint.star_eq
      rw [heq] at hs
      exact predual_tendsto_unique e hs ht
  refine ⟨p, hp, ?_, ?_, ?_, U, hU, ht⟩
  · intro q hq
    exact ((hproj q hq).le_iff_mul_eq_left hp).mpr (hfixed ⟨q, hq⟩)
  · intro r hr hu
    apply (hp.le_iff_mul_eq_left hr).mpr
    have hm := HochschildSakai.predual_tendsto_mul_right e r ht
    have heq : (fun q : S => (q : M) * r) = (fun q : S => (q : M)) := by
      funext q
      exact ((hproj q q.property).le_iff_mul_eq_left hr).mp (hu q q.property)
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  · intro a ha
    have hm := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => (q : M) * a) = (fun _ : S => (0 : M)) :=
      funext fun q => ha q q.property
    rw [heq] at hm
    exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter S))

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsometryChains
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Suprema of chains of partial isometries

The initial projections have a supremum. A weak-star cluster point of the
partial isometries agrees with each member on its initial projection. The
common-annihilator property of the supremum then identifies its initial
projection, without a trace or multiplication of two varying weak-star nets.
-/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A nonempty chain of partial isometries has a least upper bound, whose
initial and final projections respect every projection bound on the chain. -/
theorem exists_partialIso_chain_supremum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : Set (PartialIso M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ w : PartialIso M, (∀ v ∈ c, v ≤ w) ∧
      (∀ z : PartialIso M, (∀ v ∈ c, v ≤ z) → w ≤ z) ∧
      (∀ r : M, IsStarProjection r → (∀ v ∈ c, v.initial ≤ r) → w.initial ≤ r) ∧
      (∀ r : M, IsStarProjection r → (∀ v ∈ c, v.final ≤ r) → w.final ≤ r) := by
  classical
  let S : Set M := PartialIso.initial '' c
  have hSne : S.Nonempty := hne.image _
  have hSchain : IsChain (· ≤ ·) S := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ _
    exact (hc.total hv hw).imp PartialIso.initial_mono PartialIso.initial_mono
  have hSproj : ∀ r ∈ S, IsStarProjection r := by
    rintro _ ⟨v, _, rfl⟩
    exact v.initial_proj
  obtain ⟨p, hp, hupper, hleast, hann, _⟩ :=
    exists_projection_chain_supremum_with_limit e S hSne hSchain hSproj
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := ⟨fun a b => by
    rcases hc.total a.property b.property with hab | hba
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hba⟩⟩
  let U : Ultrafilter c := Ultrafilter.of atTop
  have hU : (U : Filter c) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨V, _, ht⟩ := exists_predual_ultralimit e U
    (fun v : c => ((v : PartialIso M) : M)) 1 (fun v => v.val.norm_le_one)
  have hVi (v : c) : V * v.val.initial = (v.val : M) := by
    have hm := HochschildSakai.predual_tendsto_mul_right e v.val.initial ht
    have heq : (fun w : c => (w.val : M) * v.val.initial) =ᶠ[U]
        (fun _ => (v.val : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop v] with w hvw
      exact hvw.2
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr'
      (heq.mono fun _ h => congrArg (fun a : M => e.symm a x) h.symm)
  have hstarVi (v : c) : star V * (v.val : M) = v.val.initial := by
    have hm := HochschildSakai.predual_tendsto_mul_right e (v.val : M)
      (HochschildSakai.predual_tendsto_star e ht)
    have heq : (fun w : c => star (w.val : M) * (v.val : M)) =ᶠ[U]
        (fun _ => v.val.initial) := by
      apply hU
      filter_upwards [eventually_ge_atTop v] with w hvw
      exact PartialIso.star_mul_of_ge hvw
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr'
      (heq.mono fun _ h => congrArg (fun a : M => e.symm a x) h.symm)
  have hVp : V * p = V := by
    have hm := HochschildSakai.predual_tendsto_mul_right e p ht
    have heq : (fun v : c => (v.val : M) * p) =
        (fun v : c => (v.val : M)) := by
      funext v
      calc
        (v.val : M) * p = ((v.val : M) * v.val.initial) * p := by
          rw [v.val.mul_initial]
        _ = (v.val : M) := by
          rw [mul_assoc, (v.val.initial_proj.le_iff_mul_eq_left hp).mp
            (hupper _ ⟨v.val, v.property, rfl⟩), v.val.mul_initial]
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  have hpstar : p * star V = star V := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hVp
  have hVV : star V * V = p := by
    have hann' : p * (star V * V - p) = 0 := by
      apply hann
      rintro _ ⟨v, hv, rfl⟩
      have hfixed : v.initial * (star V * V) = v.initial := by
        have hs : v.initial * star V = star (v : M) := by
          simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq] using
            congrArg star (hVi ⟨v, hv⟩)
        calc
          v.initial * (star V * V) = star (v : M) * V := by rw [← mul_assoc, hs]
          _ = v.initial := by
            simpa only [star_mul, star_star, v.initial_proj.isSelfAdjoint.star_eq]
              using congrArg star (hstarVi ⟨v, hv⟩)
      rw [mul_sub, hfixed, (v.initial_proj.le_iff_mul_eq_left hp).mp
        (hupper _ ⟨v, hv, rfl⟩), sub_self]
    rw [mul_sub, ← mul_assoc, hpstar, hp.isIdempotentElem.eq] at hann'
    exact sub_eq_zero.mp hann'
  let w : PartialIso M := ⟨V, by rw [mul_assoc, hVV, hVp]⟩
  have hwi : w.initial = p := hVV
  have hwupper : ∀ v ∈ c, v ≤ w := by
    intro v hv
    exact ⟨by rw [hwi]; exact hupper _ ⟨v, hv, rfl⟩, hVi ⟨v, hv⟩⟩
  refine ⟨w, hwupper, ?_, ?_, ?_⟩
  · intro z hz
    have hpz : p ≤ z.initial := by
      apply hleast z.initial z.initial_proj
      rintro _ ⟨v, hv, rfl⟩
      exact (hz v hv).1
    have hzp : (z : M) * p = V := by
      have ha : p * star ((z : M) - V) = 0 := by
        apply hann
        rintro _ ⟨v, hv, rfl⟩
        have heq : ((z : M) - V) * v.initial = 0 := by
          rw [sub_mul, (hz v hv).2, hVi ⟨v, hv⟩, sub_self]
        simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq, star_zero]
          using congrArg star heq
      have ha' : ((z : M) - V) * p = 0 := by
        simpa only [star_mul, star_star, hp.isSelfAdjoint.star_eq, star_zero]
          using congrArg star ha
      rwa [sub_mul, hVp, sub_eq_zero] at ha'
    exact ⟨by rw [hwi]; exact hpz, by change (z : M) * w.initial = V; rw [hwi, hzp]⟩
  · intro r hr hb
    rw [hwi]
    apply hleast r hr
    rintro _ ⟨v, hv, rfl⟩
    exact hb v hv
  · intro r hr hb
    have hrV : r * V = V := by
      have hm := HochschildSakai.predual_tendsto_mul_left e r ht
      have heq : (fun v : c => r * (v.val : M)) =
          (fun v : c => (v.val : M)) := by
        funext v
        calc
          r * (v.val : M) = r * (v.val.final * (v.val : M)) := by rw [v.val.final_mul]
          _ = (v.val : M) := by
            rw [← mul_assoc, (v.val.final_proj.le_iff_mul_eq_right hr).mp
              (hb v.val v.property), v.val.final_mul]
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    apply (w.final_proj.le_iff_mul_eq_right hr).mpr
    change r * (V * star V) = V * star V
    rw [← mul_assoc, hrV]

/-- Projection bounds are retained by an upper bound of a chain of partial
isometries, without a tracial state. -/
theorem partialIso_chain_upper (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (c : Set (PartialIso M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ v ∈ c, v.initial ≤ p ∧ v.final ≤ q) :
    ∃ w : PartialIso M, w.initial ≤ p ∧ w.final ≤ q ∧ ∀ v ∈ c, v ≤ w := by
  obtain ⟨w, hupper, _, hi, hf⟩ := exists_partialIso_chain_supremum e c hc hne
  exact ⟨w, hi p hp (fun v hv => (hs v hv).1),
    hf q hq (fun v hv => (hs v hv).2), hupper⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TraceFreeSeparation
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Central separation without a trace

A maximal projection annihilating the right ideal generated by a projection
is central. Any off-diagonal block would have a nonzero support projection
orthogonal to that maximal projection and permit an extension.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Projections with zero intervening products admit a central separator. -/
theorem exists_trace_free_central_separator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : IsStarProjection p) (_hq : IsStarProjection q)
    (hpq : ∀ a : M, p * a * q = 0) :
    ∃ z : M, CentralProjection z ∧ p ≤ z ∧ z * q = 0 := by
  classical
  let S : Set M := {r | IsStarProjection r ∧ ∀ a : M, r * a * q = 0}
  have hpS : p ∈ S := ⟨hp, hpq⟩
  obtain ⟨r, hpr, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s, hs, hu, _, ha, _⟩ := exists_projection_chain_supremum_with_limit e c
      ⟨y, hy⟩ hchain (fun t ht => (hc ht).1)
    refine ⟨s, ⟨hs, ?_⟩, hu⟩
    intro a
    rw [mul_assoc]
    apply ha
    intro t ht
    exact (mul_assoc t a q) ▸ (hc ht).2 a) p hpS
  have hr : IsStarProjection r := hmax.1.1
  have hrq : ∀ a : M, r * a * q = 0 := hmax.1.2
  have hcross (a : M) : (1 - r) * a * r = 0 := by
    let b : M := (1 - r) * a * r
    have hbq : ∀ d : M, b * d * q = 0 := by
      intro d
      calc
        b * d * q = (1 - r) * a * (r * d * q) := by simp only [b, mul_assoc]
        _ = 0 := by rw [hrq d, mul_zero]
    have hrb : r * b = 0 := by
      change r * ((1 - r) * a * r) = 0
      rw [← mul_assoc, ← mul_assoc, hr.mul_one_sub_self, zero_mul, zero_mul]
    obtain ⟨t, ht⟩ := HochschildSakai.exists_support_projection e (b * star b)
      (mul_star_self_nonneg b)
    have hrt : r * t = 0 := HochschildPolar.support_right_annihilate ht
      (IsSelfAdjoint.mul_star_self b) (by rw [← mul_assoc, hrb, zero_mul])
    have htq : ∀ d : M, t * d * q = 0 := by
      intro d
      rw [mul_assoc]
      apply ht.annihilate
      calc
        (b * star b) * (d * q) = b * (star b * d) * q := by simp only [mul_assoc]
        _ = 0 := hbq (star b * d)
    have hsum : r + t ∈ S := ⟨hr.add ht.proj hrt, fun d => by
      rw [add_mul, add_mul, hrq d, htq d, zero_add]⟩
    have hle : r ≤ r + t := le_add_of_nonneg_right ht.proj.nonneg
    have heq : r + t = r := le_antisymm (hmax.2 hsum hle) hle
    have ht0 : t = 0 := add_eq_left.mp heq
    have hb0 : b * star b = 0 := by
      have hh := ht.left
      rw [ht0, zero_mul] at hh
      exact hh.symm
    exact (CStarRing.mul_star_self_eq_zero_iff b).mp hb0
  have hcentral : ∀ a : M, Commute r a := by
    intro a
    have hright : a * r = r * a * r := by
      have h := hcross a
      rw [sub_mul, one_mul, sub_mul, sub_eq_zero] at h
      exact h
    have hleft : r * a = r * a * r := by
      have h := congrArg star (hcross (star a))
      simp only [star_mul, star_sub, star_one, star_star, hr.isSelfAdjoint.star_eq,
        star_zero] at h
      rw [mul_sub, mul_one, mul_sub, ← mul_assoc, sub_eq_zero] at h
      exact h
    exact hleft.trans hright.symm
  refine ⟨r, ⟨hr, hcentral⟩, hpr, ?_⟩
  simpa only [mul_one] using hrq 1

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TraceFreeComparison
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection comparison before constructing a trace

Maximal partial isometries and the central comparison theorem are constructed
directly from a predual. Their proofs do not presuppose the trace whose
existence is needed in the finite-algebra reduction.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The unmatched remainders of a maximal partial isometry have no connecting corner. -/
theorem exists_maximal_partialIso (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ v : PartialIso M, v.initial ≤ p ∧ v.final ≤ q ∧
      ∀ a : M, (q - v.final) * a * (p - v.initial) = 0 := by
  classical
  let S : Set (PartialIso M) := {v | v.initial ≤ p ∧ v.final ≤ q}
  have hz : (0 : PartialIso M) ∈ S :=
    ⟨by simpa using hp.nonneg, by simpa using hq.nonneg⟩
  obtain ⟨v, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s, hsp, hsq, hu⟩ := partialIso_chain_upper e hp hq c hchain ⟨y, hy⟩
      (fun z hz => hc hz)
    exact ⟨s, ⟨hsp, hsq⟩, hu⟩) 0 hz
  have hvp : v.initial ≤ p := hmax.1.1
  have hvq : v.final ≤ q := hmax.1.2
  refine ⟨v, hvp, hvq, fun a => ?_⟩
  by_contra ha
  have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
  have hq' := (v.final_proj.le_iff_sub hq).mp hvq
  obtain ⟨w, hw0, hwp, hwq⟩ := partialIso_of_nonzero_corner e hq' hp'
    ((q - v.final) * a * (p - v.initial)) ha
    (by rw [← mul_assoc, ← mul_assoc, hq'.isIdempotentElem.eq])
    (by rw [mul_assoc, hp'.isIdempotentElem.eq])
  have hi := HochschildCentralComparison.orthogonal_of_le_sub
    hp v.initial_proj w.initial_proj hvp hwp
  have hf := HochschildCentralComparison.orthogonal_of_le_sub
    hq v.final_proj w.final_proj hvq hwq
  have hs : v.orthogonalSum w hi hf ∈ S := by
    constructor
    · rw [PartialIso.orthogonalSum_initial]
      calc
        v.initial + w.initial ≤ v.initial + (p - v.initial) := add_le_add_right hwp _
        _ = p := by abel
    · rw [PartialIso.orthogonalSum_final]
      calc
        v.final + w.final ≤ v.final + (q - v.final) := add_le_add_right hwq _
        _ = q := by abel
  have hle := v.le_orthogonalSum w hi hf
  have he := le_antisymm (hmax.2 hs hle) hle
  have hvw : (v : M) + w = v := congrArg (fun z : PartialIso M => (z : M)) he
  exact hw0 (add_eq_left.mp hvw)

/-- Murray--von Neumann comparison over complementary central parts, with no
trace assumption. This is the structural comparison used before trace existence. -/
theorem trace_free_central_comparison (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ (z : M) (v : PartialIso M), CentralProjection z ∧ v.initial ≤ p ∧ v.final ≤ q ∧
      z * v.final = z * q ∧ (1 - z) * v.initial = (1 - z) * p := by
  obtain ⟨v, hvp, hvq, horth⟩ := exists_maximal_partialIso e hp hq
  have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
  have hq' := (v.final_proj.le_iff_sub hq).mp hvq
  have horth' : ∀ a : M, (p - v.initial) * a * (q - v.final) = 0 := by
    intro a
    have h := congrArg star (horth (star a))
    simpa only [star_mul, star_star, star_zero, hp'.isSelfAdjoint.star_eq,
      hq'.isSelfAdjoint.star_eq, mul_assoc] using h
  obtain ⟨z, hz, hpz, hzq⟩ := exists_trace_free_central_separator e hp' hq' horth'
  have hzp : z * (p - v.initial) = p - v.initial :=
    (hp'.le_iff_mul_eq_right hz.1).mp hpz
  refine ⟨z, v, hz, hvp, hvq, ?_, ?_⟩
  · exact (sub_eq_zero.mp (by simpa only [mul_sub] using hzq)).symm
  · have h : (1 - z) * (p - v.initial) = 0 := by
      rw [sub_mul, one_mul, hzp, sub_self]
    exact (sub_eq_zero.mp (by simpa only [mul_sub] using h)).symm

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_HilbertNormalParts
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert normal parts for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertNormalFunctional (T : M →L[ℂ] H) (a : M) : StrongDual ℂ H :=
  LinearMap.mkContinuous
    { toFun := fun η => star (scalarNormalPart e ((innerSL ℂ η).comp T) a)
      map_add' := by
        intro η ξ
        simp only [map_add,ContinuousLinearMap.add_comp,add_apply,star_add]
      map_smul' := by
        intro c η
        have hη : (innerSL ℂ (c • η)).comp T = star c • (innerSL ℂ η).comp T := by
          ext b
          change ⟪c • η,T b⟫_ℂ=star c*⟪η,T b⟫_ℂ
          simp only [inner_smul_left,starRingEnd_apply]
        change star (scalarNormalPart e ((innerSL ℂ (c • η)).comp T) a) =
          c • star (scalarNormalPart e ((innerSL ℂ η).comp T) a)
        rw [hη,map_smul,smul_apply,star_smul,star_star] }
    (4*‖T‖*‖a‖) (by
      intro η
      have hP := (scalarNormalPart e).le_opNorm ((innerSL ℂ η).comp T)
      have hT := ContinuousLinearMap.opNorm_comp_le (innerSL ℂ η) T
      have h := (scalarNormalPart e ((innerSL ℂ η).comp T)).le_opNorm a
      change ‖star (scalarNormalPart e ((innerSL ℂ η).comp T) a)‖ ≤ _
      rw [norm_star]
      calc
        _ ≤ ‖scalarNormalPart e ((innerSL ℂ η).comp T)‖*‖a‖ := h
        _ ≤ (4*(‖η‖*‖T‖))*‖a‖ := by
          gcongr
          exact hP.trans (mul_le_mul (scalarNormalPart_norm e)
            (by simpa only [innerSL_apply_norm] using hT) (norm_nonneg _) (by norm_num))
        _ = (4*‖T‖*‖a‖)*‖η‖ := by ring)

omit [CompleteSpace H] in
@[simp] lemma hilbertNormalFunctional_apply (T : M →L[ℂ] H) (a : M) (η : H) :
    hilbertNormalFunctional e T a η =
      star (scalarNormalPart e ((innerSL ℂ η).comp T) a) := rfl

end HochschildNormalPart

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_CornerComparison
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner comparison for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder
namespace PopaCorners
open BoundedHochschild HochschildRigidity HochschildDixmier HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace CornerIso
variable {p q : M}
def final (v : CornerIso p q) : M := (v:M)*star (v:M)

end CornerIso
end PopaCorners

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_CenterTrace
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Center trace for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

def average (a : M) : M := (exists_central_average e τ
  (HochschildSakai.abstract_multiplication_normal e).1 hτ htr hfaith a).choose
lemma average_norm (a : M) : ‖average e τ hτ htr hfaith a‖ ≤ ‖a‖ :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.1
lemma average_central (a : M) : Central (average e τ hτ htr hfaith a) :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.2.1
lemma average_orbit (a : M) :
    gnsVector τ (average e τ hτ htr hfaith a) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.2.2

variable (h1 : τ 1=1)

include htr h1 in
lemma central_pair_closure {z : M} (hz : Central z) (a b : M)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) : τ (z*b)=τ (z*a) := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc hcy using hy
  have htc : ∀ n, τ (z*c n)=τ (z*a) := fun n => central_pair_hull τ htr hz a (hc n)
  have ht : Tendsto (fun n => ‖τ.toPreGNS (c n-b)‖) atTop (𝓝 0) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [←hcy,←map_sub,gnsVector_norm] using hh
  have htt : Tendsto (fun n => ‖τ (z*(c n-b))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (HochschildUltrapower.norm_trace_le τ h1 _).trans
        (preGNS_norm_mul_le τ z _))
    simpa only [mul_zero] using ht.const_mul ‖z‖
  have he : ‖τ (z*a)-τ (z*b)‖=0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [mul_sub,map_sub,htc] using htt)
  exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

include h1
lemma average_pair {z : M} (hz : Central z) (a : M) :
    τ (z*average e τ hτ htr hfaith a)=τ (z*a) :=
  central_pair_closure τ htr h1 hz a _ (average_orbit e τ hτ htr hfaith a)

lemma average_eq (a b : M) (hb : Central b)
    (h : ∀ z : M, Central z → τ (z*b)=τ (z*a)) : average e τ hτ htr hfaith a=b := by
  apply central_unique τ hfaith (average_central e τ hτ htr hfaith a) hb
  intro z hz
  rw [average_pair e τ hτ htr hfaith h1 hz,h z hz]

lemma average_add (a b : M) : average e τ hτ htr hfaith (a+b)=
    average e τ hτ htr hfaith a+average e τ hτ htr hfaith b := by
  apply average_eq e τ hτ htr hfaith h1
  · intro x
    exact (average_central e τ hτ htr hfaith a x).add_left
      (average_central e τ hτ htr hfaith b x)
  · intro z hz
    rw [mul_add,map_add,mul_add,map_add,average_pair e τ hτ htr hfaith h1 hz,
      average_pair e τ hτ htr hfaith h1 hz]
lemma average_smul (r : ℂ) (a : M) : average e τ hτ htr hfaith (r • a)=
    r • average e τ hτ htr hfaith a := by
  apply average_eq e τ hτ htr hfaith h1
  · intro x; exact (average_central e τ hτ htr hfaith a x).smul_left r
  · intro z hz
    rw [mul_smul_comm,mul_smul_comm,map_smul,map_smul,average_pair e τ hτ htr hfaith h1 hz]

def expectation : M →L[ℂ] M := LinearMap.mkContinuous
  { toFun := average e τ hτ htr hfaith
    map_add' := average_add e τ hτ htr hfaith h1
    map_smul' := average_smul e τ hτ htr hfaith h1 }
  1 (by intro a; simpa using average_norm e τ hτ htr hfaith a)
@[simp] lemma expectation_apply (a : M) :
    expectation e τ hτ htr hfaith h1 a=average e τ hτ htr hfaith a := rfl

end PopaCenter

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsoCornerEquivalence
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Equivalence of corners joined by a partial isometry

Conjugation by a partial isometry identifies its initial and final corners as
actual star algebras. In particular abelianness passes between these corners
and to smaller projections.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- A subprojection of an abelian projection is abelian. -/
lemma abelian_projection_mono {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hqp : q ≤ p)
    (hab : PopaTypeII.AbelianProjection hp) : PopaTypeII.AbelianProjection hq := by
  let lift (a : PopaCorner.algebra hq) : PopaCorner.algebra hp := ⟨(a : M), by
    constructor
    · calc
        p * (a : M) = p * (q * (a : M)) := by rw [a.property.1]
        _ = (a : M) := by rw [← mul_assoc, (hq.le_iff_mul_eq_right hp).mp hqp,
          a.property.1]
    · calc
        (a : M) * p = ((a : M) * q) * p := by rw [a.property.2]
        _ = (a : M) := by rw [mul_assoc, (hq.le_iff_mul_eq_left hp).mp hqp,
          a.property.2]⟩
  intro a b
  apply Subtype.ext
  exact congrArg (fun c : PopaCorner.algebra hp => (c : M)) (hab (lift a) (lift b)).eq

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CentralProjectionSuprema
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Suprema of chains of central projections

A nonempty chain of central projections has a central projection supremum.
A bounded weak-star cluster point is a projection because multiplication by
each member of the chain eventually stabilizes. The same limiting argument
preserves annihilation of any fixed element. No trace is used.
-/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A chain of central projections has a least projection upper bound, preserving
any common right annihilator. -/
theorem exists_central_projection_chain_supremum_with_limit
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproj : ∀ q ∈ S, IsStarProjection q)
    (hcentral : ∀ q ∈ S, ∀ a : M, q * a = a * q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) ∧
      ∃ U : Ultrafilter S, (U : Filter S) ≤ atTop ∧
        PredualTendsto e (fun q : S => (q : M)) (U : Filter S) p := by
  classical
  let : Nonempty S := hne.to_subtype
  let : IsDirectedOrder S := ⟨fun a b => by
    rcases hchain.total a.property b.property with hab | hba
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hba⟩⟩
  let U : Ultrafilter S := Ultrafilter.of atTop
  have hU : (U : Filter S) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨p, _hpnorm, ht⟩ := exists_predual_ultralimit e U
    (fun q : S => (q : M)) 1 (fun q => (hproj q q.property).norm_le)
  have hfixed (q : S) : (q : M) * p = q := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (q : M) ht
    have heq : (fun r : S => (q : M) * r) =ᶠ[U] (fun _ => (q : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop q] with r hqr
      exact ((hproj q q.property).le_iff_mul_eq_left (hproj r r.property)).mp hqr
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ hr => congrArg (fun a : M => e.symm a z) hr.symm)
  have hpcentral (a : M) : p * a = a * p := by
    have hl := HochschildSakai.predual_tendsto_mul_left e a ht
    have hr := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => a * (q : M)) = (fun q : S => (q : M) * a) := by
      funext q
      exact (hcentral q q.property a).symm
    rw [heq] at hl
    exact predual_tendsto_unique e hr hl
  have hp : IsStarProjection p := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e p ht
      have heq : (fun q : S => (q : M) * p) = (fun q : S => (q : M)) :=
        funext hfixed
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hs := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun q : S => star (q : M)) = (fun q : S => (q : M)) := by
        funext q
        exact (hproj q q.property).isSelfAdjoint.star_eq
      rw [heq] at hs
      exact predual_tendsto_unique e hs ht
  refine ⟨p, hp, hpcentral, ?_, ?_, ?_, U, hU, ht⟩
  · intro q hq
    exact ((hproj q hq).le_iff_mul_eq_left hp).mpr (hfixed ⟨q, hq⟩)
  · intro r hr hub
    apply (hp.le_iff_mul_eq_left hr).mpr
    have hm := HochschildSakai.predual_tendsto_mul_right e r ht
    have heq : (fun q : S => (q : M) * r) = (fun q : S => (q : M)) := by
      funext q
      exact ((hproj q q.property).le_iff_mul_eq_left hr).mp (hub q q.property)
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  · intro a ha
    have hm := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => (q : M) * a) = (fun _ : S => (0 : M)) := by
      funext q
      exact ha q q.property
    rw [heq] at hm
    exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter S))

/-- A chain of central projections has a least projection upper bound, preserving
any common right annihilator. -/
theorem exists_central_projection_chain_supremum
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproj : ∀ q ∈ S, IsStarProjection q)
    (hcentral : ∀ q ∈ S, ∀ a : M, q * a = a * q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) := by
  obtain ⟨p, hp, hc, hu, hl, ha, _⟩ :=
    exists_central_projection_chain_supremum_with_limit e S hne hchain hproj hcentral
  exact ⟨p, hp, hc, hu, hl, ha⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeICentralSupport
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Central type I support without a trace

The maximal central projection annihilating an abelian projection exists by
weak-star compactness. Its complement is a nonzero central type I support.
The construction applies to every von Neumann algebra and requires no
faithful tracial state.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A chain of central projections annihilating one element has a central
projection upper bound that still annihilates it. -/
lemma central_annihilator_chain (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : M) (c : Set M) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ q ∈ c, CentralProjection q ∧ q * p = 0) :
    ∃ s : M, CentralProjection s ∧ s * p = 0 ∧ ∀ q ∈ c, q ≤ s := by
  obtain ⟨s, hsp, hsc, hub, _hleast, hann⟩ :=
    exists_central_projection_chain_supremum e c hne hc
      (fun q hq => (hs q hq).1.1) (fun q hq a => ((hs q hq).1.2 a).eq)
  exact ⟨s, ⟨hsp, fun a => hsc a⟩, hann p (fun q hq => (hs q hq).2), hub⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_AbelianCentralSupport
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Central support and comparison of abelian projections for type I reduction. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_central_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) : ∃ z : M, IsCentralSupport p z := by
  classical
  let S : Set M := {s | CentralProjection s ∧ s * p = 0}
  have hzero : (0 : M) ∈ S :=
    ⟨⟨IsStarProjection.zero M, fun _ => Commute.zero_left _⟩, zero_mul _⟩
  obtain ⟨s, _, hm⟩ := zorn_le_nonempty₀ S (fun C hC hchain a ha => by
    obtain ⟨t, ht, htp, hu⟩ := central_annihilator_chain e p C hchain ⟨a, ha⟩
      (fun q hq => hC hq)
    exact ⟨t, ⟨ht, htp⟩, hu⟩) 0 hzero
  have hs := hm.1.1
  have hsp := hm.1.2
  let z := 1 - s
  have hz : CentralProjection z :=
    ⟨hs.1.one_sub, fun a => (Commute.one_left a).sub_left (hs.2 a)⟩
  refine ⟨z, hz, (hp.le_iff_mul_eq_right hz.1).mpr ?_, ?_⟩
  · change (1 - s) * p = p
    rw [sub_mul, one_mul, hsp, sub_zero]
  · intro c hc hcp
    let t := z * c
    have ht : CentralProjection t :=
      ⟨hz.1.mul hc.1 (hz.2 c), fun a => (hz.2 a).mul_left (hc.2 a)⟩
    have hst : s * t = 0 := by
      change s * ((1 - s) * c) = 0
      rw [← mul_assoc, hs.1.mul_one_sub_self, zero_mul]
    have htp : t * p = 0 := by
      change z * c * p = 0
      rw [mul_assoc, hcp, mul_zero]
    have hnew : s + t ∈ S :=
      ⟨⟨hs.1.add ht.1 hst, fun a => (hs.2 a).add_left (ht.2 a)⟩,
        by rw [add_mul, hsp, htp, zero_add]⟩
    have hle : s ≤ s + t := le_add_of_nonneg_right ht.1.nonneg
    have ht0 : t = 0 := add_eq_left.mp (le_antisymm (hm.2 hnew hle) hle)
    exact (hc.2 z).eq.trans ht0

theorem central_support_full (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p z r : M} (hp : IsStarProjection p) (hz : IsCentralSupport p z)
    (hr : IsStarProjection r) (hrz : r ≤ z) (hr0 : r ≠ 0) :
    ∃ a : M, p * a * r ≠ 0 := by
  by_contra hn
  push Not at hn
  have hrp (a : M) : r * a * p = 0 := by
    simpa only [star_mul, star_star, hp.isSelfAdjoint.star_eq,
      hr.isSelfAdjoint.star_eq, star_zero, mul_assoc] using congrArg star (hn (star a))
  obtain ⟨c, hc, hrc, hcp⟩ := exists_trace_free_central_separator e hr hp hrp
  have hcz := hz.2.2 c hc hcp
  have he : c * z * r = r := by
    rw [mul_assoc, (hr.le_iff_mul_eq_right hz.1.1).mp hrz,
      (hr.le_iff_mul_eq_right hc.1).mp hrc]
  rw [hcz, zero_mul] at he
  exact hr0 he.symm

theorem trace_free_abelian_subequivalent (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : AbelianProjection p) (hq : IsStarProjection q)
    (hfull : ∀ r : M, IsStarProjection r → r ≤ p → r ≠ 0 → ∃ a : M, q * a * r ≠ 0) :
    ∃ v : PartialIso M, v.initial = p ∧ v.final ≤ q := by
  classical
  let S : Set (PartialIso M) := {v | v.initial ≤ p ∧ v.final ≤ q}
  have hz : (0 : PartialIso M) ∈ S :=
    ⟨by simpa using hp.1.nonneg, by simpa using hq.nonneg⟩
  obtain ⟨v, _, hm⟩ := zorn_le_nonempty₀ S (fun C hC hchain a ha => by
    obtain ⟨w, hwp, hwq, hu⟩ := partialIso_chain_upper e hp.1 hq C hchain ⟨a, ha⟩
      (fun t ht => hC ht)
    exact ⟨w, ⟨hwp, hwq⟩, hu⟩) 0 hz
  have hvp := hm.1.1
  have hvq := hm.1.2
  have hr := (v.initial_proj.le_iff_sub hp.1).mp hvp
  have hs := (v.final_proj.le_iff_sub hq).mp hvq
  have hir : v.initial * (p - v.initial) = 0 := by
    rw [mul_sub, (v.initial_proj.le_iff_mul_eq_left hp.1).mp hvp,
      v.initial_proj.isIdempotentElem.eq, sub_self]
  have hvr (a : M) : v.final * a * (p - v.initial) = 0 := by
    have h := HochschildTypeII.abelian_orthogonal_mul hp v.initial_proj hr hvp
      (sub_le_self _ v.initial_proj.nonneg) hir (star (v : M) * a)
    calc
      _ = (v : M) * (v.initial * (star (v : M) * a) * (p - v.initial)) := by
        simp only [← mul_assoc, v.mul_initial, PartialIso.final]
      _ = 0 := by rw [h, mul_zero]
  refine ⟨v, ?_, hvq⟩
  by_contra hi
  obtain ⟨a, ha⟩ := hfull (p - v.initial) hr (sub_le_self _ v.initial_proj.nonneg)
    (sub_ne_zero.mpr (Ne.symm hi))
  have hba : (q - v.final) * a * (p - v.initial) ≠ 0 := by
    simpa only [sub_mul, hvr a, sub_zero] using ha
  obtain ⟨w, hw0, hwi, hwf⟩ := partialIso_of_nonzero_corner e hs hr
    ((q - v.final) * a * (p - v.initial)) hba
    (by rw [← mul_assoc, ← mul_assoc, hs.isIdempotentElem.eq])
    (by rw [mul_assoc, hr.isIdempotentElem.eq])
  have hio := HochschildCentralComparison.orthogonal_of_le_sub hp.1 v.initial_proj
    w.initial_proj hvp hwi
  have hfo := HochschildCentralComparison.orthogonal_of_le_sub hq v.final_proj
    w.final_proj hvq hwf
  have hnew : v.orthogonalSum w hio hfo ∈ S := by
    constructor
    · rw [PartialIso.orthogonalSum_initial]
      calc
        v.initial + w.initial ≤ v.initial + (p - v.initial) := add_le_add_right hwi _
        _ = p := by abel
    · rw [PartialIso.orthogonalSum_final]
      calc
        v.final + w.final ≤ v.final + (q - v.final) := add_le_add_right hwf _
        _ = q := by abel
  have hle := v.le_orthogonalSum w hio hfo
  have he := congrArg (fun t : PartialIso M => (t : M))
    (le_antisymm (hm.2 hnew hle) hle)
  exact hw0 (add_eq_left.mp he)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteCentralDecomposition
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The maximal finite central cut, constructed without an assumed trace. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_iff (p : M) (hp : IsStarProjection p) :
    FiniteCorner p ↔ FiniteAlgebra (HochschildCorners.Corner p hp) := by
  constructor
  · intro h a ha
    apply Subtype.ext
    exact h a a.property.1 a.property.2 (congrArg Subtype.val ha)
  · intro h a hL hR ha
    let b : HochschildCorners.Corner p hp := ⟨a, hL, hR⟩
    exact congrArg Subtype.val (h b (Subtype.ext ha))

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_of_finiteAlgebra (hfinite : FiniteAlgebra M)
    (p : M) (hp : IsStarProjection p) : FiniteCorner p := by
  intro a hL hR haa
  have hsL : star a * p = star a := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hL
  have hsR : p * star a = star a := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hR
  have hca : (1 - p) * a = 0 := by rw [sub_mul, one_mul, hL, sub_self]
  have hac : a * (1 - p) = 0 := by rw [mul_sub, mul_one, hR, sub_self]
  have hcsa : (1 - p) * star a = 0 := by rw [sub_mul, one_mul, hsR, sub_self]
  have hsac : star a * (1 - p) = 0 := by rw [mul_sub, mul_one, hsL, sub_self]
  have hin : star (a + (1 - p)) * (a + (1 - p)) = 1 := by
    simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      add_mul, mul_add, hsac, hca, zero_add, add_zero, haa,
      hp.one_sub.isIdempotentElem.eq]
    abel
  have hout := hfinite (a + (1 - p)) hin
  simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq,
    add_mul, mul_add, hac, hcsa, zero_add, add_zero,
    hp.one_sub.isIdempotentElem.eq] at hout
  have hp1 : p + (1 - p) = 1 := by abel
  exact add_right_cancel (hout.trans hp1.symm)

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralCorner_central {p : M} (hp : IsStarProjection p)
    (hc : ∀ a : M, p * a = a * p) (q : HochschildCorners.Corner p hp)
    (hqc : ∀ b : HochschildCorners.Corner p hp, q * b = b * q) :
    ∀ a : M, (q : M) * a = a * (q : M) := by
  intro a
  have h := congrArg Subtype.val (hqc (CentralCorner.compressMap p hp hc a))
  change (q : M) * (p * a) = (p * a) * (q : M) at h
  calc
    (q : M) * a = ((q : M) * p) * a := by rw [q.property.2]
    _ = (q : M) * (p * a) := mul_assoc _ _ _
    _ = (p * a) * (q : M) := h
    _ = a * (p * (q : M)) := by rw [hc a, mul_assoc]
    _ = a * (q : M) := by rw [q.property.1]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeICentralDecomposition
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The central type I cut

Central type I summands are closed under chain suprema and orthogonal sums.
A maximal one therefore has a complementary corner with no abelian
projections, and in particular no type I central part. All constructions
use the given predual and require no trace.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
/-- The two corner formulations of an abelian projection agree in the direction needed here. -/
lemma finitePath_abelian_of_popa {p : M} (hp : IsStarProjection p)
    (h : PopaTypeII.AbelianProjection hp) : AbelianProjection p := by
  refine ⟨hp, fun a b => ?_⟩
  let A : PopaCorner.algebra hp := ⟨p * a * p, compress_mem_corner hp a⟩
  let B : PopaCorner.algebra hp := ⟨p * b * p, compress_mem_corner hp b⟩
  exact congrArg Subtype.val (h A B).eq

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeIMatrixColumns
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homogeneous matrix systems from equivalent orthogonal abelian projections. -/

noncomputable section

open scoped BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison HochschildMatrixSystems

variable {M : Type*} [CStarAlgebra M] {n : ℕ} {p : M}

variable [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma matrixSystemOfColumns_abelian (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hs : ∑ i, (v i).final = 1)
    (hp : IsStarProjection p) (hpa : PopaTypeII.AbelianProjection hp) (i : Fin n) :
    FinitePathMain.AbelianProjection ((matrixSystemOfColumns v hi ho hs).entry i i) := by
  have hinit : PopaTypeII.AbelianProjection (v i).initial_proj := by
    simpa only [hi] using hpa
  exact finitePath_abelian_of_popa (v i).final_proj (abelianProjection_partialIso (v i) hinit)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_AbelianProjectionForms
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conversion between the two existing abelian-corner formulations. -/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma popa_abelian_of_finitePath {p : M} (hp : AbelianProjection p) :
    PopaTypeII.AbelianProjection hp.1 := by
  have hc (a : PopaCorner.algebra hp.1) : p * (a : M) * p = (a : M) := by
    rw [a.property.1, a.property.2]
  intro a b
  apply Subtype.ext
  change (a : M) * (b : M) = (b : M) * (a : M)
  simpa only [hc] using (hp.2 (a : M) (b : M)).eq

omit [PartialOrder M] [StarOrderedRing M] in
lemma abelian_partialIso (v : PartialIso M) (hp : AbelianProjection v.initial) :
    AbelianProjection v.final :=
  finitePath_abelian_of_popa v.final_proj
    (abelianProjection_partialIso v (popa_abelian_of_finitePath hp))

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteProjectionEquivalence
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unitary equivalence of finite projections

In a finite von Neumann algebra a partial isometry extends to a unitary.
The proof uses trace-free central comparison of the complementary projections
and finiteness of central corners. No scalar trace is used.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
/-- A central cut of a partial isometry exhausts its initial projection
exactly when it exhausts its final projection in a finite algebra. -/
lemma finite_central_initial_iff_final (hfinite : FiniteAlgebra M)
    (z : M) (hz : IsStarProjection z) (hc : ∀ a : M, z * a = a * z)
    (v : PartialIso M) : z * v.initial = z ↔ z * v.final = z := by
  have forward (w : PartialIso M) (hi : z * w.initial = z) : z * w.final = z := by
    let a := centralCutPartialIso z hz hc w
    have hL : z * (a : M) = a := by
      change z * (z * (w : M)) = z * (w : M)
      rw [← mul_assoc, hz.isIdempotentElem.eq]
    have hR : (a : M) * z = a := by rw [← hc, hL]
    have hin : star (a : M) * a = z := by
      change a.initial = z
      change (centralCutPartialIso z hz hc w).initial = z
      rw [centralCutPartialIso_initial, hi]
    have hout := finiteCorner_of_finiteAlgebra hfinite z hz (a : M) hL hR hin
    change a.final = z at hout
    simpa only [a, centralCutPartialIso_final] using hout
  exact ⟨forward v, fun h => by simpa using forward (adjointPartialIso v) (by simpa using h)⟩

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A partial isometry in a finite von Neumann algebra extends to a unitary. -/
theorem finite_partialIso_extends_unitary (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (v : PartialIso M) :
    ∃ u : unitary M, (u : M) * v.initial = v := by
  classical
  obtain ⟨z, w, hz, hwi, hwf, hzf, hzi⟩ := trace_free_central_comparison e
    v.initial_proj.one_sub v.final_proj.one_sub
  have hi : v.initial * w.initial = 0 :=
    HochschildTypeII.projection_orthogonal_of_le_complement v.initial_proj w.initial_proj hwi
  have hf : v.final * w.final = 0 :=
    HochschildTypeII.projection_orthogonal_of_le_complement v.final_proj w.final_proj hwf
  let t := v.orthogonalSum w hi hf
  have hti : t.initial = v.initial + w.initial := PartialIso.orthogonalSum_initial v w hi hf
  have htf : t.final = v.final + w.final := PartialIso.orthogonalSum_final v w hi hf
  have hzc : ∀ a : M, z * a = a * z := fun a => (hz.2 a).eq
  have hzc' : ∀ a : M, (1 - z) * a = a * (1 - z) := by
    intro a
    simp only [sub_mul, mul_sub, one_mul, mul_one, hzc]
  have hzfinal : z * t.final = z := by
    rw [htf, mul_add, hzf, mul_sub, mul_one]
    abel
  have hczinitial : (1 - z) * t.initial = 1 - z := by
    rw [hti, mul_add, hzi, mul_sub, mul_one]
    abel
  have hzinitial := (finite_central_initial_iff_final hfinite z hz.1 hzc t).mpr hzfinal
  have hczfinal := (finite_central_initial_iff_final hfinite (1 - z) hz.1.one_sub hzc' t).mp hczinitial
  have hsplit (a : M) : z * a + (1 - z) * a = a := by noncomm_ring
  have htinitial : t.initial = 1 := by
    rw [← hsplit t.initial, hzinitial, hczinitial]
    abel
  have htfinal : t.final = 1 := by
    rw [← hsplit t.final, hzfinal, hczfinal]
    abel
  let u : unitary M := ⟨(t : M), by
    rw [Unitary.mem_iff]
    exact ⟨htinitial, htfinal⟩⟩
  refine ⟨u, ?_⟩
  change ((v : M) + (w : M)) * v.initial = v
  have hwv : (w : M) * v.initial = 0 := by
    calc
      (w : M) * v.initial = ((w : M) * w.initial) * v.initial := by rw [w.mul_initial]
      _ = 0 := by
        rw [mul_assoc]
        have hzero : w.initial * v.initial = 0 := by
          simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq,
            w.initial_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star hi
        rw [hzero, mul_zero]
  rw [add_mul, v.mul_initial, hwv, add_zero]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_AbelianSupportEquivalence
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Abelian projections with the same central support are equivalent. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Each subprojection of an abelian projection is a central cut of it. -/
theorem abelian_subprojection_central_cut (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q : M} (hp : AbelianProjection p) (hq : IsStarProjection q) (hqp : q ≤ p) :
    ∃ c : M, CentralProjection c ∧ c * p = q := by
  have hr := (hq.le_iff_sub hp.1).mp hqp
  have hqr : q * (p - q) = 0 := by
    rw [mul_sub, (hq.le_iff_mul_eq_left hp.1).mp hqp, hq.isIdempotentElem.eq, sub_self]
  obtain ⟨c, hc, hqc, hcr⟩ := exists_trace_free_central_separator e hq hr
    (HochschildTypeII.abelian_orthogonal_mul hp hq hr hqp
      (sub_le_self _ hq.nonneg) hqr)
  refine ⟨c, hc, ?_⟩
  have hcq := (hq.le_iff_mul_eq_right hc.1).mp hqc
  rw [mul_sub, hcq, sub_eq_zero] at hcr
  exact hcr

/-- Full abelian projections over the same central support are equivalent. -/
theorem abelian_equivalent_of_central_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p q z : M} (hp : AbelianProjection p) (hq : AbelianProjection q)
    (hpz : IsCentralSupport p z) (hqz : IsCentralSupport q z) :
    ∃ v : PartialIso M, v.initial = p ∧ v.final = q := by
  obtain ⟨v, hvp, hvq⟩ := trace_free_abelian_subequivalent e hp hq.1
    (fun r hr hrp hr0 => central_support_full e hq.1 hqz hr (hrp.trans hpz.2.1) hr0)
  have hvz : IsCentralSupport v.final z :=
    IsCentralSupport.partialIso v (by simpa only [hvp] using hpz)
  have hr := (v.final_proj.le_iff_sub hq.1).mp hvq
  have hrq : q - v.final ≤ q := sub_le_self _ v.final_proj.nonneg
  obtain ⟨c, hc, hcr⟩ := abelian_subprojection_central_cut e hq hr hrq
  have hcf : c * v.final = 0 := by
    have horth : (q - v.final) * v.final = 0 := by
      rw [sub_mul, (v.final_proj.le_iff_mul_eq_right hq.1).mp hvq,
        v.final_proj.isIdempotentElem.eq, sub_self]
    calc
      _ = (c * q) * v.final := by rw [mul_assoc,
        (v.final_proj.le_iff_mul_eq_right hq.1).mp hvq]
      _ = 0 := by rw [hcr, horth]
  have hcz := hvz.2.2 c hc hcf
  have hr0 : q - v.final = 0 := by
    calc
      _ = c * q := hcr.symm
      _ = c * (z * q) := by rw [(hq.1.le_iff_mul_eq_right hqz.1.1).mp hqz.2.1]
      _ = 0 := by rw [← mul_assoc, hcz, zero_mul]
  exact ⟨v, hvp, (sub_eq_zero.mp hr0).symm⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteTraceCover
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.predualNormalEquiv_coe _root_.OAI.BoundedHochschild.WeakAlgebra.traceRestriction_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.PopaCenter.expectation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal positive functionals for the finite trace cover

Every nonzero projection in an abstract von Neumann algebra is detected by
a normal positive state supported on that projection. This constructs the
normal positive functionals needed for a later trace cover; it does not
assume or assert that finiteness alone supplies a trace.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A vector state before normalizing its vector. -/
def vectorPositiveFunctional (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : M →ₚ[ℂ] ℂ where
  toLinearMap := (coefficient π ξ ξ).toLinearMap
  monotone' := by
    change Monotone (coefficient π ξ ξ)
    apply (monotone_iff_map_nonneg _).mpr
    intro a ha
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (map_nonneg π ha)).inner_nonneg_right ξ

@[simp] lemma vectorPositiveFunctional_apply (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) (a : M) : vectorPositiveFunctional π ξ a = inner ℂ ξ (π a ξ) := rfl

omit [CompleteSpace X] in
lemma vectorPositiveFunctional_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) {ξ : H} (hξ : ξ ∈ normalVectors e π) :
    TraceInPredual e (vectorPositiveFunctional π ξ) := by
  exact (mem_normalDual e _).mp ((mem_normalVectors e π ξ).mp hξ ξ)

/-- Every nonzero projection supports a normal positive state. -/
theorem exists_normal_state_on_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ ψ : M →ₚ[ℂ] ℂ, TraceInPredual e ψ ∧ ψ 1 = 1 ∧ ψ p = 1 ∧
      ∀ a : M, ψ (p * a * p) = ψ a := by
  classical
  have hex : ∃ z : X, e.symm p z ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hp0
    apply e.symm.injective
    ext z
    simpa only [map_zero, zero_apply] using hn z
  obtain ⟨z, hz⟩ := hex
  let φ := predualEmbedding e z
  let m := functionalModel φ
  let π := m.representation
  let η := m.leftVector
  let ξ := normalProjection e π m.rightVector
  have hφ : φ ∈ normalDual e := ⟨z, rfl⟩
  have hreal : coefficient π η ξ = φ := by
    exact (normalProjection_fixes_normal e π η m.rightVector
      (m.realizes.symm ▸ hφ)).trans m.realizes
  have hξ : ξ ∈ normalVectors e π := by simp [ξ, normalProjection]
  let ζ := π p ξ
  have hζ : ζ ∈ normalVectors e π := normalVectors_mul e π hξ p
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    have he := congrArg (fun f : StrongDual ℂ M => f p) hreal
    have hφp : φ p ≠ 0 := by simpa only [φ, predualEmbedding_apply, star_ne_zero] using hz
    apply hφp
    change inner ℂ η ζ = φ p at he
    rw [hzero, inner_zero_right] at he
    exact he.symm
  have hfix : π p ζ = ζ := by
    change π p (π p ξ) = π p ξ
    rw [← mul_apply_eq_comp, ← map_mul, hp.isIdempotentElem.eq]
  let w := (‖ζ‖⁻¹ : ℂ) • ζ
  have hwn : ‖w‖ = 1 := norm_smul_inv_norm hζ0
  have hw : w ∈ normalVectors e π := (normalVectors e π).smul_mem _ hζ
  have hwfix : π p w = w := by simp only [w, map_smul, hfix]
  let ψ := vectorPositiveFunctional π w
  have hψ1 : ψ 1 = 1 := by
    simp only [ψ, vectorPositiveFunctional_apply, map_one, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K, hwn]
    norm_num
  refine ⟨ψ, vectorPositiveFunctional_normal e π hw, hψ1, ?_, ?_⟩
  · simpa only [ψ, vectorPositiveFunctional_apply, hwfix, map_one, one_apply_eq_self]
      using hψ1
  · intro a
    change inner ℂ w (π (p * a * p) w) = inner ℂ w (π a w)
    rw [map_mul, map_mul]
    change inner ℂ w (π p (π a (π p w))) = inner ℂ w (π a w)
    rw [hwfix, ← ContinuousLinearMap.adjoint_inner_left]
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, hp.isSelfAdjoint.star_eq, hwfix]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteProjectionExtension
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extension of embeddings in finite corners

A partial embedding into a finite projection extends whenever an embedding
of the larger initial projection exists. This is the cancellation step used
in Ringrose, *Lectures on the trace in a finite von Neumann algebra*, Lemma 5.1.
The construction uses only the predual and finiteness, not a trace.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The unitary extending a supported partial isometry can be chosen in the
same finite corner. Its ambient initial and final projections are that corner. -/
theorem finite_partialIso_extends_in_corner (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (v : PartialIso M) (hi : v.initial ≤ q) (hf : v.final ≤ q) :
    ∃ u : M, q * u = u ∧ u * q = u ∧ star u * u = q ∧ u * star u = q ∧
      u * v.initial = v := by
  let vC : PartialIso (Corner q hq) :=
    ⟨⟨(v : M), partialIso_left_support hq v hf, partialIso_right_support hq v hi⟩,
      Subtype.ext v.mul_star_mul⟩
  obtain ⟨u, hu⟩ := finite_partialIso_extends_unitary (cornerPredualEquiv q hq e)
    ((finiteCorner_iff q hq).mp hfinite) vC
  refine ⟨((u : Corner q hq) : M), (u : Corner q hq).property.1,
    (u : Corner q hq).property.2, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val ((Unitary.mem_iff.mp u.property).1)
  · exact congrArg Subtype.val ((Unitary.mem_iff.mp u.property).2)
  · exact congrArg Subtype.val hu

/-- An embedding of a smaller projection into a finite corner extends to an
embedding of a larger projection as soon as the latter embeds in that corner. -/
theorem finite_partialIso_extension (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (v w : PartialIso M) (hvw : v.initial ≤ w.initial)
    (hvq : v.final ≤ q) (hwq : w.final ≤ q) :
    ∃ t : PartialIso M, v ≤ t ∧ t.initial = w.initial ∧ t.final ≤ q := by
  have hvp : (v : M) * w.initial = v := partialIso_right_support w.initial_proj v hvw
  have hqw : q * (w : M) = w := partialIso_left_support hq w hwq
  have hqv : q * (v : M) = v := partialIso_left_support hq v hvq
  let a : PartialIso M := ⟨(v : M) * star (w : M), by
    calc
      ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) *
          ((v : M) * star (w : M)) =
          ((v : M) * w.initial) * star (v : M) * (v : M) * star (w : M) := by
        simp only [star_mul, star_star, PartialIso.initial, mul_assoc]
      _ = (v : M) * star (w : M) := by rw [hvp, v.mul_star_mul]⟩
  have haf : a.final = v.final := by
    change ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) = v.final
    simp only [star_mul, star_star]
    calc
      _ = ((v : M) * w.initial) * star (v : M) := by
        simp only [PartialIso.initial, mul_assoc]
      _ = v.final := by rw [hvp]; rfl
  have hai : a.initial = (w : M) * v.initial * star (w : M) := by
    simp only [a, PartialIso.initial, star_mul, star_star, mul_assoc]
  have haiq : a.initial ≤ q := by
    apply (a.initial_proj.le_iff_mul_eq_right hq).mpr
    rw [hai, ← mul_assoc, ← mul_assoc, hqw]
  obtain ⟨u, hqu, huq, huu, _, hua⟩ := finite_partialIso_extends_in_corner e hq
    hfinite a haiq (by rw [haf]; exact hvq)
  have huwi : u * (w : M) * v.initial = v := by
    have h := congrArg (fun b : M => b * (w : M)) hua
    rw [hai] at h
    change u * ((w : M) * v.initial * star (w : M)) * (w : M) =
      ((v : M) * star (w : M)) * (w : M) at h
    have hiv : v.initial * w.initial = v.initial :=
      (v.initial_proj.le_iff_mul_eq_left w.initial_proj).mp hvw
    calc
      u * (w : M) * v.initial =
          u * ((w : M) * v.initial * star (w : M)) * (w : M) := by
        simp only [mul_assoc]
        change u * ((w : M) * v.initial) =
          u * ((w : M) * (v.initial * w.initial))
        rw [hiv]
      _ = (v : M) := by
        rw [h]
        simpa only [PartialIso.initial, mul_assoc] using hvp
  have hti : star (u * (w : M)) * (u * (w : M)) = w.initial := by
    calc
      _ = star (w : M) * (star u * u) * (w : M) := by
        simp only [star_mul, mul_assoc]
      _ = w.initial := by rw [huu, mul_assoc, hqw]; rfl
  let t : PartialIso M := ⟨u * (w : M), by
    rw [mul_assoc, hti]
    change u * (w : M) * w.initial = u * (w : M)
    rw [mul_assoc, w.mul_initial]⟩
  refine ⟨t, ⟨?_, huwi⟩, hti, ?_⟩
  · change v.initial ≤ star (u * (w : M)) * (u * (w : M))
    rw [hti]
    exact hvw
  · apply (t.final_proj.le_iff_mul_eq_right hq).mpr
    change q * ((u * (w : M)) * star (u * (w : M))) = _
    rw [← mul_assoc, ← mul_assoc, hqu]
    rfl

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsoProducts
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Products of composable partial isometries and comparison of complements. -/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma composePartialIso_final_le (v w : PartialIso M) (h : w.final ≤ v.initial) :
    (composePartialIso v w h).final ≤ v.final := by
  apply ((composePartialIso v w h).final_proj.le_iff_mul_eq_right v.final_proj).mpr
  change v.final * (((v : M) * w) * star ((v : M) * w)) = _
  rw [← mul_assoc, ← mul_assoc, v.final_mul]
  rfl

/-- Finiteness reverses subequivalence on complementary projections. -/
theorem finite_complement_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (v : PartialIso M)
    (hi : v.initial = p) (hf : v.final ≤ q) :
    ∃ w : PartialIso M, w.initial = 1 - q ∧ w.final ≤ 1 - p := by
  obtain ⟨u, hu⟩ := finite_partialIso_extends_unitary e hfinite v
  rw [hi] at hu
  have huunit : star (u : M) * u = 1 ∧ (u : M) * star (u : M) = 1 :=
    Unitary.mem_iff.mp u.property
  have hvq : q * (v : M) = v := partialIso_left_support hq v hf
  have hzero : (1 - q) * (u : M) * p = 0 := by
    rw [mul_assoc, hu, sub_mul, one_mul, hvq, sub_self]
  have hzero' : p * star (u : M) * (1 - q) = 0 := by
    simpa only [star_mul, star_sub, star_one, star_star, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq, star_zero, mul_assoc] using congrArg star hzero
  let a := star (u : M) * (1 - q)
  have hai : star a * a = 1 - q := by
    dsimp [a]
    rw [star_mul, star_sub, star_one, hq.isSelfAdjoint.star_eq, star_star]
    calc
      _ = (1 - q) * ((u : M) * star (u : M)) * (1 - q) := by simp only [mul_assoc]
      _ = 1 - q := by rw [huunit.2, mul_one, hq.one_sub.isIdempotentElem.eq]
  have hap : a * (1 - q) = a := by
    dsimp [a]
    rw [mul_assoc, hq.one_sub.isIdempotentElem.eq]
  let w : PartialIso M := ⟨a, by rw [mul_assoc, hai, hap]⟩
  refine ⟨w, hai, ?_⟩
  have hpa : (1 - p) * a = a := by
    change (1 - p) * (star (u : M) * (1 - q)) = _
    rw [sub_mul, one_mul, ← mul_assoc, hzero', sub_zero]
  apply (w.final_proj.le_iff_mul_eq_right hp.one_sub).mpr
  change (1 - p) * (a * star a) = a * star a
  rw [← mul_assoc, hpa]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteIncreasingComparison
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Increasing limits of subequivalent projections

Ringrose, *Lectures on the trace in a finite von Neumann algebra*, Lemma 5.1:
an increasing supremum of projections subequivalent to a fixed finite
projection is still subequivalent to it. The proof aligns successive partial
isometries inside the finite corner and then takes their chain supremum.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Increasing limits preserve subequivalence to a finite projection. -/
theorem finite_increasing_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (p : ℕ → M) (hmono : Monotone p)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q) :
    ∃ v : PartialIso M, v.final ≤ q ∧ (∀ n, p n ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ n, p n ≤ r) → v.initial ≤ r := by
  classical
  choose b hb using hembed
  let S (n : ℕ) := {v : PartialIso M // v.initial = p n ∧ v.final ≤ q}
  have hnext (n : ℕ) (v : S n) : ∃ w : S (n + 1), v.val ≤ w.val := by
    have hle : v.val.initial ≤ (b (n + 1)).initial := by
      rw [v.property.1, (hb (n + 1)).1]
      exact hmono (Nat.le_succ n)
    obtain ⟨w, hvw, hwi, hwf⟩ := finite_partialIso_extension e hq hfinite
      v.val (b (n + 1)) hle v.property.2 (hb (n + 1)).2
    exact ⟨⟨w, hwi.trans (hb (n + 1)).1, hwf⟩, hvw⟩
  choose step hstep using hnext
  let a : (n : ℕ) → S n := fun n => Nat.rec ⟨b 0, hb 0⟩ (fun n v => step n v) n
  let f : ℕ → PartialIso M := fun n => (a n).val
  have hfmono : Monotone f := monotone_nat_of_le_succ fun n => hstep n (a n)
  have hfi (n : ℕ) : (f n).initial = p n := (a n).property.1
  have hff (n : ℕ) : (f n).final ≤ q := (a n).property.2
  obtain ⟨v, hupper, _, hi, hf⟩ := exists_partialIso_chain_supremum e (Set.range f)
    hfmono.isChain_range (Set.range_nonempty f)
  refine ⟨v, hf q hq (by rintro _ ⟨n, rfl⟩; exact hff n), ?_, ?_⟩
  · intro n
    rw [← hfi n]
    exact (hupper _ ⟨n, rfl⟩).1
  · intro r hr hb
    apply hi r hr
    rintro _ ⟨n, rfl⟩
    rw [hfi n]
    exact hb n

/-- Ringrose's Lemma 5.1 with the supremum specified in advance. -/
theorem finite_subequivalence_at_supremum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q s : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (hs : IsStarProjection s) (p : ℕ → M) (hmono : Monotone p)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q)
    (hupper : ∀ n, p n ≤ s)
    (hleast : ∀ r : M, IsStarProjection r → (∀ n, p n ≤ r) → s ≤ r) :
    ∃ v : PartialIso M, v.initial = s ∧ v.final ≤ q := by
  obtain ⟨v, hvq, hvupper, hvleast⟩ := finite_increasing_subequivalence e hq hfinite
    p hmono hembed
  exact ⟨v, le_antisymm (hvleast s hs hupper)
    (hleast v.initial v.initial_proj hvupper), hvq⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TraceFreeProjectionJoins
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection joins before trace existence

The join of two projections is obtained by adding the range projection of
`(1 - p) * q` to `p`. Polar decomposition also embeds the added projection
into `q`. This is the projection comparison used in Ringrose's Lemma 5.2.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A trace-free join, with the part added to `p` equivalent to a subprojection
of `q`. The formula records the partial isometry needed in finite joins. -/
theorem exists_trace_free_projection_join (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ v : PartialIso M, v.initial ≤ q ∧ p * v.final = 0 ∧
      IsStarProjection (p + v.final) ∧ p ≤ p + v.final ∧ q ≤ p + v.final ∧
      ∀ z : M, IsStarProjection z → p ≤ z → q ≤ z → p + v.final ≤ z := by
  let b := (1 - p) * q
  have hpb : (1 - p) * b = b := by
    dsimp [b]
    rw [← mul_assoc, hp.one_sub.isIdempotentElem.eq]
  have hbq : b * q = b := by
    dsimp [b]
    rw [mul_assoc, hq.isIdempotentElem.eq]
  obtain ⟨w, r, t, hr, hwi, hwf, ht, hb, hwr, htb⟩ :=
    HochschildPolar.exists_polar_partial_isometry e b
  have hwabs : star w * b = CFC.abs b := by
    calc
      star w * b = star w * (w * CFC.abs b) := congrArg (star w * ·) hb
      _ = CFC.abs b := by rw [← mul_assoc, hwi, hr.left]
  have hw_support {z : M} (hz : IsStarProjection z) (hzb : z * b = b) : z * w = w := by
    have hzero : ((1 - z) * w) * CFC.abs b = 0 := by
      rw [mul_assoc, ← hb, sub_mul, one_mul, hzb, sub_self]
    have hzero' := HochschildPolar.support_right_annihilate hr
      (CFC.abs_nonneg b).isSelfAdjoint hzero
    rw [mul_assoc, hwr, sub_mul, one_mul, sub_eq_zero] at hzero'
    exact hzero'.symm
  have hpw : (1 - p) * w = w := hw_support hp.one_sub hpb
  let v : PartialIso M := ⟨w, by rw [mul_assoc, hwi, hwr]⟩
  have hiv : v.initial = r := hwi
  have hfv : v.final = t := hwf
  have hiq : v.initial ≤ q := by
    rw [hiv]
    apply (hr.proj.le_iff_mul_eq_left hq).mpr
    have hzero : CFC.abs b * (1 - q) = 0 := by
      rw [← hwabs, mul_assoc, mul_sub, mul_one, hbq, sub_self, mul_zero]
    have hzero' := hr.annihilate (1 - q) hzero
    simpa only [mul_sub, mul_one, sub_eq_zero, eq_comm] using hzero'
  have hfp : v.final ≤ 1 - p := by
    apply (v.final_proj.le_iff_mul_eq_right hp.one_sub).mpr
    change (1 - p) * (w * star w) = w * star w
    rw [← mul_assoc, hpw]
  have horth : p * v.final = 0 :=
    HochschildTypeII.projection_orthogonal_of_le_complement hp v.final_proj hfp
  have horth' : v.final * p = 0 := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq,
      v.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star horth
  have hj : IsStarProjection (p + v.final) := hp.add v.final_proj horth
  have hvq : v.final * q = b := by
    have h : v.final * b = b := by rw [hfv]; exact htb
    dsimp [b] at h ⊢
    rwa [← mul_assoc, mul_sub, mul_one, horth', sub_zero] at h
  refine ⟨v, hiq, horth, hj, ?_, ?_, ?_⟩
  · exact le_add_of_nonneg_right v.final_proj.nonneg
  · apply (hq.le_iff_mul_eq_right hj).mpr
    rw [add_mul, hvq]
    dsimp [b]
    noncomm_ring
  · intro z hz hpz hqz
    have hzp : z * p = p := (hp.le_iff_mul_eq_right hz).mp hpz
    have hzq : z * q = q := (hq.le_iff_mul_eq_right hz).mp hqz
    have hzb : z * b = b := by
      dsimp [b]
      rw [← mul_assoc, mul_sub, mul_one, hzp, sub_mul, hzq, sub_mul, one_mul]
    have hzw : z * w = w := hw_support hz hzb
    apply (hj.le_iff_mul_eq_right hz).mpr
    change z * (p + w * star w) = p + w * star w
    rw [mul_add, hzp, ← mul_assoc, hzw]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProjectionJoinComparison
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison bounds for joins, independent of any scalar trace. -/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- If two projections embed into orthogonal target projections, their join
embeds into the sum of those targets. -/
theorem projection_join_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p₁ p₂ q₁ q₂ : M} (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
    (hq₁ : IsStarProjection q₁) (hq₂ : IsStarProjection q₂) (hqorth : q₁ * q₂ = 0)
    (a b : PartialIso M) (hai : a.initial = p₁) (haf : a.final ≤ q₁)
    (hbi : b.initial = p₂) (hbf : b.final ≤ q₂) :
    ∃ t : PartialIso M, t.final ≤ q₁ + q₂ ∧ p₁ ≤ t.initial ∧ p₂ ≤ t.initial ∧
      ∀ r : M, IsStarProjection r → p₁ ≤ r → p₂ ≤ r → t.initial ≤ r := by
  obtain ⟨v, hvi, horth, hj, hpj, hqj, hleast⟩ :=
    exists_trace_free_projection_join e p₁ p₂ hp₁ hp₂
  have hcomp : (adjointPartialIso v).final ≤ b.initial := by simpa [hbi] using hvi
  let c := composePartialIso b (adjointPartialIso v) hcomp
  have hci : c.initial = v.final := by simp [c]
  have hcf : c.final ≤ q₂ := (composePartialIso_final_le b _ hcomp).trans hbf
  have haci : a.initial * c.initial = 0 := by rw [hai, hci]; exact horth
  have hacf : a.final * c.final = 0 :=
    projection_orthogonal_mono a.final_proj c.final_proj hq₁ hq₂ haf hcf hqorth
  let t := a.orthogonalSum c haci hacf
  have hti : t.initial = p₁ + v.final := by
    rw [show t.initial = a.initial + c.initial from PartialIso.orthogonalSum_initial _ _ _ _,
      hai, hci]
  refine ⟨t, ?_, by rw [hti]; exact hpj, by rw [hti]; exact hqj, ?_⟩
  · rw [show t.final = a.final + c.final from PartialIso.orthogonalSum_final _ _ _ _]
    exact add_le_add haf hcf
  · intro r hr hpr hqr
    rw [hti]
    exact hleast r hr hpr hqr

/-- Finite joins of projections equivalent to orthogonal projections embed
into the corresponding finite orthogonal sum. -/
theorem finite_join_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p q : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n)
    (n : ℕ) :
    ∃ v : PartialIso M, v.final ≤ ∑ i ∈ Finset.range n, q i ∧
      (∀ i < n, p i ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ i < n, p i ≤ r) → v.initial ≤ r := by
  classical
  induction n with
  | zero =>
      refine ⟨0, by simp, by simp, ?_⟩
      intro r hr _
      simpa using hr.nonneg
  | succ n ih =>
      obtain ⟨a, haf, hau, hal⟩ := ih
      obtain ⟨b, hbi, hbf⟩ := hembed n
      have hsum : IsStarProjection (∑ i ∈ Finset.range n, q i) := by
        exact orthogonal_projection_sum_range q hq horth n
      have hsumorth : (∑ i ∈ Finset.range n, q i) * q n = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro i hi
        exact horth i n (Nat.ne_of_lt (Finset.mem_range.mp hi))
      obtain ⟨t, htf, hat, hpt, hleast⟩ := projection_join_subequivalence e
        a.initial_proj (hp n) hsum (hq n) hsumorth a b rfl haf hbi hbf
      refine ⟨t, ?_, ?_, ?_⟩
      · simpa only [Finset.sum_range_succ] using htf
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hin | rfl
        · exact (hau i hin).trans hat
        · exact hpt
      · intro r hr hpr
        exact hleast r hr (hal r hr (fun i hi => hpr i (Nat.lt_succ_of_lt hi)))
          (hpr n (Nat.lt_succ_self n))

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProjectionSequenceLimits
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sequential projection suprema and infima with their actual weak-star limits. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- An increasing sequence of projections converges weak-star to its supremum. -/
theorem exists_increasing_projection_limit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : ℕ → M) (hp : ∀ n, IsStarProjection (p n)) (hm : Monotone p) :
    ∃ s : M, IsStarProjection s ∧ IsLUB (Set.range p) s ∧
      PredualTendsto e p atTop s := by
  obtain ⟨s, _, hlub, ht⟩ := HochschildSakai.exists_monotone_predual_limit e p hm
    1 zero_le_one (fun n => (hp n).norm_le _)
  have hfixed (n : ℕ) : p n * s = p n := by
    have hm' := HochschildSakai.predual_tendsto_mul_left e (p n) ht
    have heq : (fun m => p n * p m) =ᶠ[atTop] (fun _ => p n) := by
      filter_upwards [eventually_ge_atTop n] with m hnm
      exact ((hp n).le_iff_mul_eq_left (hp m)).mp (hm hnm)
    apply predual_tendsto_unique e hm'
    intro x
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a x) h.symm)
  have hmul : s * s = s := by
    have hs := HochschildSakai.predual_tendsto_mul_right e s ht
    have heq : (fun n => p n * s) = p := funext hfixed
    rw [heq] at hs
    exact predual_tendsto_unique e hs ht
  have hstar : star s = s := by
    have hs := HochschildSakai.predual_tendsto_star e ht
    have heq : (fun n => star (p n)) = p := funext fun n => (hp n).isSelfAdjoint.star_eq
    rw [heq] at hs
    exact predual_tendsto_unique e hs ht
  exact ⟨s, ⟨hmul, hstar⟩, hlub, ht⟩

/-- A decreasing sequence of projections converges weak-star to its infimum. -/
theorem exists_decreasing_projection_limit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : ℕ → M) (hp : ∀ n, IsStarProjection (p n)) (hm : Antitone p) :
    ∃ s : M, IsStarProjection s ∧ IsGLB (Set.range p) s ∧
      PredualTendsto e p atTop s := by
  obtain ⟨s, hs, _, ht⟩ := exists_increasing_projection_limit e (fun n => 1 - p n)
    (fun n => (hp n).one_sub) (fun i j hij => sub_le_sub_left (hm hij) 1)
  have ht' : PredualTendsto e p atTop (1 - s) := by
    have hh := predual_tendsto_sub e (predual_tendsto_const e 1 atTop) ht
    simpa only [sub_sub_cancel] using hh
  exact ⟨1 - s, hs.one_sub,
    HochschildSakai.isGLB_of_antitone_predual_limit e p hm ht' 1 zero_le_one
      (fun n => (hp n).norm_le _), ht'⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteCountableComparison
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable joins bounded by a finite orthogonal target. -/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Countably many projections, each embeddable into mutually orthogonal
subprojections of a finite projection, have a join embeddable there. -/
theorem countable_join_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {Q : M} (hQ : IsStarProjection Q) (hfinite : FiniteCorner Q)
    (p q : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (hqQ : ∀ n, q n ≤ Q)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n) :
    ∃ v : PartialIso M, v.final ≤ Q ∧ (∀ n, p n ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ n, p n ≤ r) → v.initial ≤ r := by
  classical
  choose a haf hau hal using finite_join_subequivalence e p q hp hq horth hembed
  have hsumQ (n : ℕ) : (∑ i ∈ Finset.range n, q i) ≤ Q := by
    apply ((orthogonal_projection_sum_range q hq horth n).le_iff_mul_eq_right hQ).mpr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ((hq i).le_iff_mul_eq_right hQ).mp (hqQ i)
  have ham : Monotone (fun n => (a n).initial) := monotone_nat_of_le_succ fun n => by
    apply hal n (a (n + 1)).initial (a (n + 1)).initial_proj
    intro i hi
    exact hau (n + 1) i (Nat.lt_succ_of_lt hi)
  have haQ (n : ℕ) : (a n).final ≤ Q := (haf n).trans (hsumQ n)
  obtain ⟨v, hvQ, hvupper, hvleast⟩ := finite_increasing_subequivalence e hQ hfinite
    (fun n => (a n).initial) ham (fun n => ⟨a n, rfl, haQ n⟩)
  refine ⟨v, hvQ, ?_, ?_⟩
  · intro n
    exact (hau (n + 1) n (Nat.lt_succ_self n)).trans (hvupper (n + 1))
  · intro r hr hpr
    apply hvleast r hr
    intro n
    exact hal n r hr (fun i _ => hpr i)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_OrthogonalProjectionTails
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-star null tails of a sequence of orthogonal projections. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The tails of an orthogonal projection sum are projections converging
weak-star to zero, and each tail dominates all of its summands. -/
theorem exists_orthogonal_projection_tails (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) :
    ∃ T : ℕ → M, (∀ n, IsStarProjection (T n)) ∧ Antitone T ∧
      (∀ n i, n ≤ i → q i ≤ T n) ∧ PredualTendsto e T atTop 0 := by
  let s (n : ℕ) : M := ∑ i ∈ Finset.range n, q i
  have hs (n : ℕ) : IsStarProjection (s n) := orthogonal_projection_sum_range q hq horth n
  have hsm : Monotone s := monotone_nat_of_le_succ fun n => by
    dsimp [s]
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hq n).nonneg
  obtain ⟨Q, hQ, hlub, ht⟩ := exists_increasing_projection_limit e s hs hsm
  have hsQ (n : ℕ) : s n ≤ Q := hlub.1 ⟨n, rfl⟩
  have hqQ (i : ℕ) : q i ≤ Q := by
    apply le_trans _ (hsQ (i + 1))
    dsimp [s]
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => (hq j).nonneg)
  refine ⟨fun n => Q - s n, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ((hs n).le_iff_sub hQ).mp (hsQ n)
  · intro i j hij
    exact sub_le_sub_left (hsm hij) Q
  · intro n i hni
    have hTail : IsStarProjection (Q - s n) := ((hs n).le_iff_sub hQ).mp (hsQ n)
    apply ((hq i).le_iff_mul_eq_right hTail).mpr
    rw [sub_mul, ((hq i).le_iff_mul_eq_right hQ).mp (hqQ i)]
    have hzero : s n * q i = 0 := by
      dsimp [s]
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth j i (Nat.ne_of_lt ((Finset.mem_range.mp hj).trans_le hni))
    rw [hzero, sub_zero]
  · simpa only [sub_self] using
      predual_tendsto_sub e (predual_tendsto_const e Q atTop) ht

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteProjectionAbsoluteContinuity
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Absolute continuity of finite projection comparison

The projection argument behind Ringrose, *Lectures on the trace in a finite
von Neumann algebra*, Lemma 5.2. Projections separately subequivalent to an
orthogonal sequence admit decreasing dominating projections with zero
weak-star limit. No tracial functional is used.
-/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- In a finite algebra, projections dominated in comparison by an orthogonal
sequence have weak-star-null decreasing projection envelopes. -/
theorem finite_subequivalent_orthogonal_tails (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (p q : ℕ → M)
    (hp : ∀ n, IsStarProjection (p n)) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n) :
    ∃ R : ℕ → M, (∀ n, IsStarProjection (R n)) ∧ Antitone R ∧
      (∀ n, p n ≤ R n) ∧ PredualTendsto e R atTop 0 := by
  classical
  obtain ⟨T, hT, hTm, hTq, hTlim⟩ := exists_orthogonal_projection_tails e q hq horth
  have hjoins (n : ℕ) : ∃ v : PartialIso M, v.final ≤ T n ∧
      (∀ i, p (n + i) ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ i, p (n + i) ≤ r) → v.initial ≤ r := by
    apply countable_join_subequivalence e (hT n)
      (finiteCorner_of_finiteAlgebra hfinite _ (hT n))
      (fun i => p (n + i)) (fun i => q (n + i))
      (fun i => hp (n + i)) (fun i => hq (n + i))
    · intro i j hij
      exact horth _ _ (fun h => hij (Nat.add_left_cancel h))
    · intro i
      exact hTq n (n + i) (Nat.le_add_right n i)
    · intro i
      exact hembed (n + i)
  choose v hvf hvu hvl using hjoins
  let R (n : ℕ) : M := (v n).initial
  have hR (n : ℕ) : IsStarProjection (R n) := (v n).initial_proj
  have hRm : Antitone R := antitone_nat_of_succ_le fun n => by
    apply hvl (n + 1) (R n) (hR n)
    intro i
    simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hvu n (i + 1)
  obtain ⟨s, hs, hglb, hRlim⟩ := exists_decreasing_projection_limit e R hR hRm
  have hsR (n : ℕ) : s ≤ (v n).initial := hglb.1 ⟨n, rfl⟩
  have hembedS (n : ℕ) : ∃ w : PartialIso M, w.initial = s ∧ w.final ≤ T n := by
    let w := (v n).restrict hs (hsR n)
    exact ⟨w, PartialIso.restrict_initial _ _ _,
      (PartialIso.final_mono (PartialIso.restrict_le _ _ _)).trans (hvf n)⟩
  have hcomp (n : ℕ) : ∃ w : PartialIso M, w.initial = 1 - T n ∧ w.final ≤ 1 - s := by
    obtain ⟨w, hwi, hwf⟩ := hembedS n
    exact finite_complement_subequivalence e hfinite hs (hT n) w hwi hwf
  have hcomplim : PredualTendsto e (fun n => 1 - T n) atTop 1 := by
    simpa only [sub_zero] using predual_tendsto_sub e
      (predual_tendsto_const e 1 atTop) hTlim
  have hcomleast (r : M) (_hr : IsStarProjection r)
      (hb : ∀ n, 1 - T n ≤ r) : (1 : M) ≤ r := by
    apply HochschildSakai.le_of_bounded_predual_limit e 1 zero_le_one
      (Eventually.of_forall fun n => (hT n).one_sub.norm_le _) ?_ hcomplim
    exact Eventually.of_forall hb
  obtain ⟨w, hwi, hwf⟩ := finite_subequivalence_at_supremum e hs.one_sub
    (finiteCorner_of_finiteAlgebra hfinite _ hs.one_sub) (IsStarProjection.one M)
    (fun n => 1 - T n) (fun i j hij => sub_le_sub_left (hTm hij) 1) hcomp
    (fun n => (hT n).one_sub.le_one) hcomleast
  have hwfull : w.final = 1 := hfinite (w : M) hwi
  have hs0 : s = 0 := by
    rw [hwfull] at hwf
    exact sub_eq_self.mp (le_antisymm hs.one_sub.le_one hwf)
  refine ⟨R, hR, hRm, ?_, ?_⟩
  · intro n
    simpa only [Nat.add_zero] using hvu n 0
  · simpa only [hs0] using hRlim

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteNormalOrbit
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform normal-state decay along unitary orbits

Ringrose, *Lectures on the trace in a finite von Neumann algebra*, Lemma 5.2,
for positive normal functionals. This is the specialization needed for the
normal-state orbit used in constructing a trace.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A normal positive functional vanishes along projections subequivalent to
an orthogonal sequence in a finite algebra. -/
theorem normal_positive_subequivalent_tendsto_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (p q : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q n) :
    Tendsto (fun n => ψ (p n)) atTop (𝓝 0) := by
  obtain ⟨R, _, _, hle, ht⟩ := finite_subequivalent_orthogonal_tails e hfinite p q
    hp hq horth hembed
  have hRt : Tendsto (fun n => ‖ψ (R n)‖) atTop (𝓝 0) := by
    simpa only [map_zero, norm_zero] using (trace_predual_tendsto e ψ hψ ht).norm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hRt
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (ψ.monotone (hle n))
    (ψ.map_nonneg (hp n).nonneg)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalOrbitHull
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The norm-closed convex orbit of a normal positive functional

This family remains normal and positive, preserves values on the center,
and satisfies the uniform orthogonal-projection decay in Ringrose Lemma 5.2.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma unitaryOrbitHull_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : StrongDual ℂ M} (hF : F ∈ normalDual e) :
    unitaryOrbitHull F ⊆ normalDual e := by
  apply closure_minimal _ (normalDual_closed e)
  apply convexHull_min _ ((normalDual e).restrictScalars ℝ).convex
  rintro _ ⟨u, rfl⟩
  apply normalDual_comp e _ _ (HochschildSakai.mul_hasPreadjoint e (u : M))
  exact normalDual_comp e hF _ ((HochschildSakai.abstract_multiplication_normal e).2 (star (u : M)))

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveNormalParts
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive normal and singular parts

The normal-vector projection splits a positive functional into positive
normal and singular parts. In particular, any positive functional dominated
by a normal positive functional is normal. This supplies the normality
criterion for order intervals in the predual compactness argument.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

section Representation
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder M] [StarOrderedRing M] in
lemma normalComplement_diagonal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    coefficient π ξ ξ - scalarNormalPart e (coefficient π ξ ξ) =
      coefficient π (ξ - normalProjection e π ξ) (ξ - normalProjection e π ξ) := by
  rw [scalarNormalPart_coefficient]
  ext a
  let P := normalProjection e π
  let δ := ξ - P ξ
  have hPP : P (P ξ) = P ξ :=
    Submodule.starProjection_eq_self_iff.mpr (by simp [P, normalProjection])
  have hPδ : P δ = 0 := by dsimp [δ]; rw [map_sub, hPP, sub_self]
  have hcomm : P (π a δ) = π a (P δ) :=
    congrArg (fun T : H →L[ℂ] H => T δ) (normalProjection_mul e π a)
  have hzero : inner ℂ (P ξ) (π a δ) = 0 := by
    calc
      _ = inner ℂ ξ (P (π a δ)) :=
        (normalVectors e π).inner_starProjection_left_eq_right ξ (π a δ)
      _ = 0 := by rw [hcomm, hPδ, map_zero, inner_zero_right]
  change inner ℂ ξ (π a ξ) - inner ℂ ξ (π a (P ξ)) = inner ℂ δ (π a δ)
  calc
    _ = inner ℂ ξ (π a δ) := by dsimp [δ]; rw [map_sub, inner_sub_right]
    _ = inner ℂ (P ξ + δ) (π a δ) := by simp only [δ, add_sub_cancel]
    _ = inner ℂ δ (π a δ) := by rw [inner_add_left, hzero, zero_add]

end Representation

/-- The remaining positive part, realized by the complementary GNS vector. -/
def positiveSingularPart (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (ψ : M →ₚ[ℂ] ℂ) :
    M →ₚ[ℂ] ℂ :=
  vectorPositiveFunctional ψ.gnsStarAlgHom
    (positiveVector ψ - normalProjection e ψ.gnsStarAlgHom (positiveVector ψ))

lemma positiveSingularPart_eq (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (ψ : M →ₚ[ℂ] ℂ) :
    positiveFunctionalCLM (positiveSingularPart e ψ) =
      positiveFunctionalCLM ψ - scalarNormalPart e (positiveFunctionalCLM ψ) := by
  have hψ : positiveFunctionalCLM ψ = coefficient ψ.gnsStarAlgHom (positiveVector ψ)
      (positiveVector ψ) := by ext a; exact (positiveVector_coefficient ψ a).symm
  rw [hψ, normalComplement_diagonal]
  rfl

/-- Domination by a positive normal functional forces normality. -/
theorem positive_normal_of_dominated (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (χ ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (hle : ∀ a : M, 0 ≤ a → χ a ≤ ψ a) : TraceInPredual e χ := by
  let θ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := ψ.toLinearMap - χ.toLinearMap
      monotone' := (monotone_iff_map_nonneg (ψ.toLinearMap - χ.toLinearMap)).mpr (fun a ha => sub_nonneg.mpr (hle a ha)) }
  have hsum : positiveFunctionalCLM χ + positiveFunctionalCLM θ = positiveFunctionalCLM ψ := by
    ext a
    change χ a + (ψ a - χ a) = ψ a
    abel
  have hψnormal : positiveFunctionalCLM ψ ∈ normalDual e := (mem_normalDual e _).mpr hψ
  have hS : positiveFunctionalCLM (positiveSingularPart e χ) +
      positiveFunctionalCLM (positiveSingularPart e θ) = 0 := by
    rw [positiveSingularPart_eq, positiveSingularPart_eq]
    calc
      _ = (positiveFunctionalCLM χ + positiveFunctionalCLM θ) -
          (scalarNormalPart e (positiveFunctionalCLM χ) +
            scalarNormalPart e (positiveFunctionalCLM θ)) := by abel
      _ = positiveFunctionalCLM ψ - scalarNormalPart e (positiveFunctionalCLM ψ) := by
        rw [← map_add, hsum]
      _ = 0 := by rw [scalarNormalPart_fixes e hψnormal, sub_self]
  have hzero : positiveFunctionalCLM (positiveSingularPart e χ) = 0 := by
    apply HochschildSakai.dual_zero_of_projection_zero e
    intro p hp
    have he := congrArg (fun F : StrongDual ℂ M => F p) hS
    change positiveSingularPart e χ p + positiveSingularPart e θ p = 0 at he
    apply le_antisymm _ ((positiveSingularPart e χ).map_nonneg hp.nonneg)
    calc
      positiveSingularPart e χ p ≤
          positiveSingularPart e χ p + positiveSingularPart e θ p :=
        le_add_of_nonneg_right ((positiveSingularPart e θ).map_nonneg hp.nonneg)
      _ = 0 := he
  rw [positiveSingularPart_eq] at hzero
  have hχnormal : positiveFunctionalCLM χ ∈ normalDual e := by
    rw [sub_eq_zero] at hzero
    rw [hzero]
    exact scalarNormalPart_mem e _
  exact (mem_normalDual e _).mp hχnormal

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_OrthogonalProjectionSums
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary orthogonal projection sums and their weak-star convergence. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {I : Type v}

/-- The net of finite partial sums of any orthogonal family converges
weak-star to its projection supremum. -/
theorem exists_orthogonal_projection_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) :
    ∃ P : M, IsStarProjection P ∧ (∀ i, p i ≤ P) ∧
      (∀ r : M, IsStarProjection r → (∀ i, p i ≤ r) → P ≤ r) ∧
      PredualTendsto e (fun s : Finset I => ∑ i ∈ s, p i) atTop P := by
  classical
  let f (s : Finset I) : M := ∑ i ∈ s, p i
  have hf (s : Finset I) : IsStarProjection (f s) := orthogonal_projection_finset_sum p hp horth s
  have hfm : Monotone f := by
    intro s t hst
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (hp i).nonneg)
  obtain ⟨P, _, hlub, ht⟩ := HochschildSakai.exists_monotone_predual_limit e f hfm
    1 zero_le_one (fun s => (hf s).norm_le _)
  have hfixed (s : Finset I) : f s * P = f s := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (f s) ht
    have heq : (fun t => f s * f t) =ᶠ[atTop] (fun _ => f s) := by
      filter_upwards [eventually_ge_atTop s] with t hst
      exact ((hf s).le_iff_mul_eq_left (hf t)).mp (hfm hst)
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a x) h.symm)
  have hP : IsStarProjection P := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e P ht
      have heq : (fun s => f s * P) = f := funext hfixed
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hm := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun s => star (f s)) = f := funext fun s => (hf s).isSelfAdjoint.star_eq
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
  refine ⟨P, hP, ?_, ?_, ht⟩
  · intro i
    have h := hlub.1 (Set.mem_range_self ({i} : Finset I))
    simpa only [f, Finset.sum_singleton] using h
  · intro r hr hpr
    apply hlub.2
    rintro _ ⟨s, rfl⟩
    apply ((hf s).le_iff_mul_eq_right hr).mpr
    change r * (∑ i ∈ s, p i) = ∑ i ∈ s, p i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ((hp i).le_iff_mul_eq_right hr).mp (hpr i)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProjectionPositivity
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positivity detected on projections

The spectral approximation step in Ringrose, *Lectures on the trace in a
finite von Neumann algebra*, Lemma 3.5. Dyadic spectral projections suffice.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma positive_contraction_eval_nonneg_of_projection_nonneg
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : StrongDual ℂ M)
    (hreal : ∀ a : M, IsSelfAdjoint a → (F a).im = 0)
    (hproj : ∀ p : M, IsStarProjection p → 0 ≤ F p)
    (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 0 ≤ F a := by
  have hbound (n : ℕ) : ∀ b : M, 0 ≤ b → b ≤ 1 →
      -((1 / 2 : ℝ) ^ n) * ‖F‖ ≤ (F b).re := by
    induction n with
    | zero =>
        intro b hb0 hb1
        have hn : ‖F b‖ ≤ ‖F‖ := (F.le_opNorm b).trans
          (mul_le_of_le_one_right (norm_nonneg _) ((CStarAlgebra.norm_le_one_iff_of_nonneg b hb0).mpr hb1))
        have hr := Complex.abs_re_le_norm (F b)
        simp only [pow_zero, neg_mul, one_mul]
        linarith [neg_le_abs (F b).re]
    | succ n ih =>
        intro b hb0 hb1
        obtain ⟨p, hp, hlow, hupp⟩ := HochschildSakai.exists_dyadic_projection e b hb0 hb1
        have hh := ih ((2 : ℝ) • b - p) hlow hupp
        have he : F ((2 : ℝ) • b - p) = (2 : ℝ) • F b - F p := by simp
        rw [he] at hh
        have hp0 : 0 ≤ (F p).re := (Complex.nonneg_iff.mp (hproj p hp)).1
        simp at hh
        have hpow : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by simp [one_div]
        rw [← hpow] at hh
        rw [pow_succ]
        nlinarith
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hreal a ha0.isSelfAdjoint).symm⟩
  have ht : Tendsto (fun n : ℕ => -((1 / 2 : ℝ) ^ n) * ‖F‖) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).neg.mul_const ‖F‖)
  exact le_of_tendsto ht (Eventually.of_forall fun n => hbound n a ha0 ha1)

/-- A bounded hermitian functional nonnegative on projections is positive. -/
theorem eval_nonneg_of_projection_nonneg (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (F : StrongDual ℂ M) (hreal : ∀ a : M, IsSelfAdjoint a → (F a).im = 0)
    (hproj : ∀ p : M, IsStarProjection p → 0 ≤ F p) :
    ∀ a : M, 0 ≤ a → 0 ≤ F a := by
  intro a ha
  let t : ℝ := ‖a‖ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let c : M := t⁻¹ • a
  have hc0 : 0 ≤ c := smul_nonneg (inv_nonneg.mpr ht.le) ha
  have hcn : ‖c‖ ≤ 1 := by
    rw [show c = t⁻¹ • a from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_one₀ ht).mpr (by dsimp [t]; linarith)
  have hc1 : c ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg c hc0).mp hcn
  have hh := smul_nonneg ht.le
    (positive_contraction_eval_nonneg_of_projection_nonneg e F hreal hproj c hc0 hc1)
  have hca : t • c = a := by
    dsimp [c]
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have he : (t : ℝ) • F c = F a := by
    calc
      (t : ℝ) • F c = F ((t : ℝ) • c) := by simp
      _ = F a := congrArg F hca
  rwa [he] at hh

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CompleteAdditivity
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete additivity on orthogonal projections

This is the complete-additivity condition of Ringrose, Section 4 (Takesaki's
normality criterion), expressed through the net of finite partial sums.
-/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A completely additive hermitian functional has a maximal positive
projection corner inside any given projection (Ringrose, Lemma 4.1). Here
positivity is first recorded on subprojections. -/
theorem exists_nonnegative_projection_corner (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (F : StrongDual ℂ M) (hF : CompletelyAdditive F) {E : M} (hE : IsStarProjection E) :
    ∃ p : M, IsStarProjection p ∧ p ≤ E ∧ (F E).re ≤ (F p).re ∧
      ∀ q : M, IsStarProjection q → q ≤ p → 0 ≤ (F q).re := by
  classical
  let A : Set (Set M) := {S | (∀ p ∈ S, IsStarProjection p ∧ p ≤ E ∧ (F p).re < 0) ∧
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p * q = 0}
  obtain ⟨S, hS⟩ := zorn_subset A (fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro p hp
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      exact (hc hs).1 p hps
    · intro p hp q hq hpq
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      obtain ⟨t, ht, hqt⟩ := Set.mem_sUnion.mp hq
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 p (hst hps) q hqt hpq
      · exact (hc hs).2 p hps q (hts hqt) hpq)
  let f : S → M := Subtype.val
  have hp (i : S) : IsStarProjection (f i) := (hS.1.1 i i.property).1
  have ho (i j : S) (hij : i ≠ j) : f i * f j = 0 :=
    hS.1.2 i i.property j j.property (fun h => hij (Subtype.ext h))
  obtain ⟨P, hP, hPu, hPl, _⟩ := exists_orthogonal_projection_sum e f hp ho
  have hPE : P ≤ E := hPl E hE (fun i => (hS.1.1 i i.property).2.1)
  have hsum := hF S f hp ho P hP hPu hPl
  have hPneg : (F P).re ≤ 0 := by
    apply le_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hsum)
    apply Eventually.of_forall
    intro s
    change (∑ i ∈ s, F (f i)).re ≤ 0
    change Complex.reCLM (∑ i ∈ s, F (f i)) ≤ 0
    rw [map_sum]
    exact Finset.sum_nonpos (fun i _ => (hS.1.1 i i.property).2.2.le)
  have hEP : IsStarProjection (E - P) := (hP.le_iff_sub hE).mp hPE
  refine ⟨E - P, hEP, ?_, ?_, ?_⟩
  · exact sub_le_self E hP.nonneg
  · rw [map_sub, Complex.sub_re]
    linarith
  · intro q hq hqEP
    by_contra hqneg
    have hqn : (F q).re < 0 := lt_of_not_ge hqneg
    have hqE : q ≤ E := hqEP.trans (sub_le_self E hP.nonneg)
    have hPq : P * q = 0 := HochschildCentralComparison.orthogonal_of_le_sub hE hP hq hPE hqEP
    have hfq (i : S) : f i * q = 0 := by
      calc
        f i * q = (f i * P) * q := by rw [((hp i).le_iff_mul_eq_left hP).mp (hPu i)]
        _ = 0 := by rw [mul_assoc, hPq, mul_zero]
    have hqf (i : S) : q * f i = 0 := by
      simpa only [star_mul, (hp i).isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        star_zero] using congrArg star (hfq i)
    have hnew : insert q S ∈ A := by
      constructor
      · intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact ⟨hq, hqE, hqn⟩
        · exact hS.1.1 a ha
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with har | ha
        · subst a
          rcases Set.mem_insert_iff.mp hb with hbr | hb
          · exact (hab hbr.symm).elim
          · exact hqf ⟨b, hb⟩
        · rcases Set.mem_insert_iff.mp hb with hbr | hb
          · subst b
            exact hfq ⟨a, ha⟩
          · exact hS.1.2 a ha b hb hab
    have hsubset : insert q S ⊆ S := hS.2 hnew (Set.subset_insert q S)
    have hqin : q ∈ S := hsubset (Set.mem_insert q S)
    have hq0 : q = 0 := by simpa only [f, hq.isIdempotentElem.eq] using hfq ⟨q, hqin⟩
    simp only [hq0, map_zero, Complex.zero_re, lt_self_iff_false] at hqn

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_AdditivePositiveSupport
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support projections for completely additive positive functionals. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Complete additivity supplies a support projection without assuming
normality in advance. This is used in proving the normality criterion. -/
theorem exists_additive_positive_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : CompletelyAdditive (positiveFunctionalCLM ψ)) :
    ∃ p : M, IsStarProjection p ∧ ψ p = ψ 1 ∧
      ∀ q : M, IsStarProjection q → q ≤ p → ψ q = 0 → q = 0 := by
  classical
  let A : Set (Set M) := {S | (∀ p ∈ S, IsStarProjection p ∧ p ≠ 0 ∧ ψ p = 0) ∧
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p * q = 0}
  obtain ⟨S, hS⟩ := zorn_subset A (fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro p hp
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      exact (hc hs).1 p hps
    · intro p hp q hq hpq
      obtain ⟨s, hs, hps⟩ := Set.mem_sUnion.mp hp
      obtain ⟨t, ht, hqt⟩ := Set.mem_sUnion.mp hq
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 p (hst hps) q hqt hpq
      · exact (hc hs).2 p hps q (hts hqt) hpq)
  let f : S → M := Subtype.val
  have hf (i : S) : IsStarProjection (f i) := (hS.1.1 i i.property).1
  have ho (i j : S) (hij : i ≠ j) : f i * f j = 0 :=
    hS.1.2 i i.property j j.property (fun h => hij (Subtype.ext h))
  obtain ⟨P, hP, hPu, hPl, _⟩ := exists_orthogonal_projection_sum e f hf ho
  have hPnull : ψ P = 0 := by
    have ht := hψ S f hf ho P hP hPu hPl
    have heq : (fun s : Finset S => ∑ i ∈ s, positiveFunctionalCLM ψ (f i)) =
        (fun _ : Finset S => (0 : ℂ)) := by
      funext s
      apply Finset.sum_eq_zero
      intro i _
      exact (hS.1.1 i i.property).2.2
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨1 - P, hP.one_sub, ?_, ?_⟩
  · rw [map_sub, hPnull, sub_zero]
  · intro q hq hqP hnull
    by_contra hq0
    have hPq : P * q = 0 :=
      HochschildTypeII.projection_orthogonal_of_le_complement hP hq hqP
    have hfq (i : S) : f i * q = 0 := by
      calc
        f i * q = (f i * P) * q := by rw [((hf i).le_iff_mul_eq_left hP).mp (hPu i)]
        _ = 0 := by rw [mul_assoc, hPq, mul_zero]
    have hqf (i : S) : q * f i = 0 := by
      simpa only [star_mul, (hf i).isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        star_zero] using congrArg star (hfq i)
    have hnew : insert q S ∈ A := by
      constructor
      · intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact ⟨hq, hq0, hnull⟩
        · exact hS.1.1 a ha
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.mp ha with har | ha
        · subst a
          rcases Set.mem_insert_iff.mp hb with hbr | hb
          · exact (hab hbr.symm).elim
          · exact hqf ⟨b, hb⟩
        · rcases Set.mem_insert_iff.mp hb with hbr | hb
          · subst b
            exact hfq ⟨a, ha⟩
          · exact hS.1.2 a ha b hb hab
    have hsubset : insert q S ⊆ S := hS.2 hnew (Set.subset_insert q S)
    have hqin : q ∈ S := hsubset (Set.mem_insert q S)
    exact hq0 (by simpa only [f, hq.isIdempotentElem.eq] using hfq ⟨q, hqin⟩)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeICentralPieces
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete finite homogeneous central corners and their matrix columns. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners HochschildComparison HochschildMatrixSystems FinitePathMain

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

theorem homogeneousCorner_of_columns {z p : M} (hz : IsStarProjection z)
    (hp : AbelianProjection p) (hpz : p ≤ z) {n : ℕ} (i : Fin n)
    (v : Fin n → PartialIso M) (hi : ∀ j, (v j).initial = p)
    (hf : ∀ j, (v j).final ≤ z)
    (ho : ∀ j k, j ≠ k → (v j).final * (v k).final = 0)
    (hs : ∑ j, (v j).final = z) : HomogeneousTypeICorner z := by
  let pC : Corner z hz := ⟨p, (hp.1.le_iff_mul_eq_right hz).mp hpz,
    (hp.1.le_iff_mul_eq_left hz).mp hpz⟩
  have hpC : IsStarProjection pC :=
    ⟨Subtype.ext hp.1.isIdempotentElem.eq, Subtype.ext hp.1.isSelfAdjoint.star_eq⟩
  let w (j : Fin n) := partialIsoInCorner hz (v j) (by rw [hi]; exact hpz) (hf j)
  have hwi (j : Fin n) : (w j).initial = pC := Subtype.ext (hi j)
  have hwo (j k : Fin n) (hjk : j ≠ k) : (w j).final * (w k).final = 0 :=
    Subtype.ext (ho j k hjk)
  have hws : ∑ j, (w j).final = 1 := by
    apply Subtype.ext
    change CentralCorner.includeMap z hz (∑ j, (w j).final) = z
    rw [map_sum]
    exact hs
  let E := matrixSystemOfColumns w hwi hwo hws
  refine ⟨hz, n, E, i, matrixSystemOfColumns_abelian w hwi hwo hws hpC ?_ i⟩
  intro a b
  apply Subtype.ext
  apply Subtype.ext
  have hcut (c : PopaCorner.algebra hpC) : p * ((c : Corner z hz) : M) * p =
      ((c : Corner z hz) : M) := by
    have hl := congrArg (fun a : Corner z hz => (a : M)) c.property.1
    have hr := congrArg (fun a : Corner z hz => (a : M)) c.property.2
    change p * ((c : Corner z hz) : M) = ((c : Corner z hz) : M) at hl
    change ((c : Corner z hz) : M) * p = ((c : Corner z hz) : M) at hr
    rw [hl, hr]
  change ((a : Corner z hz) : M) * ((b : Corner z hz) : M) =
    ((b : Corner z hz) : M) * ((a : Corner z hz) : M)
  simpa only [hcut] using (hp.2 ((a : Corner z hz) : M) ((b : Corner z hz) : M)).eq

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CentralColumnCuts
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extracting homogeneous central pieces from finite column families. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- If a central cut annihilates the residual of a finite abelian column
family, the cut is a finite homogeneous type I summand. -/
theorem homogeneousCorner_of_annihilated_residual {p z : M} (hp : AbelianProjection p)
    (hz : CentralProjection z) (hz0 : z ≠ 0) {n : ℕ}
    (v : Fin n → PartialIso M) (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hann : z * (1 - ∑ i, (v i).final) = 0) : HomogeneousTypeICorner z := by
  classical
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    exact hz0 (by simpa using hann)
  let w (i : Fin n) := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) (v i)
  have hzp : IsStarProjection (z * p) := hz.1.mul hp.1 (hz.2 p)
  have hzpp : z * p ≤ p := (hzp.le_iff_mul_eq_left hp.1).mpr
    (by rw [mul_assoc, hp.1.isIdempotentElem.eq])
  have hpz : z * p ≤ z := (hzp.le_iff_mul_eq_right hz.1).mpr
    (by rw [← mul_assoc, hz.1.isIdempotentElem.eq])
  have hwi (i : Fin n) : (w i).initial = z * p := by
    simp only [w, centralCutPartialIso_initial, hi]
  have hwf (i : Fin n) : (w i).final ≤ z := by
    apply ((w i).final_proj.le_iff_mul_eq_right hz.1).mpr
    simp only [w, centralCutPartialIso_final]
    rw [← mul_assoc, hz.1.isIdempotentElem.eq]
  have hwo (i j : Fin n) (hij : i ≠ j) : (w i).final * (w j).final = 0 := by
    simp only [w, centralCutPartialIso_final]
    rw [central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq),
      ho i j hij, mul_zero]
  have hws : ∑ i, (w i).final = z := by
    simp only [w, centralCutPartialIso_final, ← Finset.mul_sum]
    rw [mul_sub, mul_one, sub_eq_zero] at hann
    exact hann.symm
  exact homogeneousCorner_of_columns hz.1 (HochschildTypeII.abelian_of_le hp hzp hzpp)
    hpz ⟨0, hn⟩ w hwi hwf hwo hws

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.WeakInfiniteness_MatrixRepresentation
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace

namespace WeakPureInfiniteness

section MatrixOperators

variable {n H : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma matrixOperator_single [DecidableEq n] (M : CStarMatrix n n (H →L[ℂ] H)) (i j : n) (x : H) :
    matrixOperator M (PiLp.single 2 j x) i = M i j x := by
  simp [PiLp.single_apply, apply_ite]

omit [CompleteSpace H] in
lemma matrixOperator_injective : Function.Injective (matrixOperator (n := n) (H := H)) := by
  classical
  intro M N h
  ext i j x
  have he := congrArg (fun T => T (PiLp.single 2 j x) i) h
  simpa only [matrixOperator_single] using he

end MatrixOperators

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveKernelMatrices
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive finite Gram matrices and the coefficient inequality needed for
the Hilbert-space construction of completely positive maps. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

/-- Inserting any positive algebra element still gives a positive matrix. -/
lemma weighted_algebraGram_nonneg (a : I → M) (q : M) (hq : 0 ≤ q) :
    0 ≤ CStarMatrix.ofMatrix (fun i j => star (a i) * q * a j) := by
  have hs : star (CFC.sqrt q) * CFC.sqrt q = q := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg q)).star_eq]
    exact CFC.sqrt_mul_sqrt_self q hq
  have heq : algebraGram (fun i => CFC.sqrt q * a i) =
      CStarMatrix.ofMatrix (fun i j => star (a i) * q * a j) := by
    ext i j
    change star (CFC.sqrt q * a i) * (CFC.sqrt q * a j) = _
    rw [star_mul]
    calc
      _ = star (a i) * (star (CFC.sqrt q) * CFC.sqrt q) * a j := by
        simp only [mul_assoc]
      _ = _ := by rw [hs]; rfl
  rw [← heq]
  exact algebraGram_nonneg (fun i : I => CFC.sqrt q * a i)

/-- Left multiplication is bounded in every one of these positive kernels. -/
lemma algebraGram_left_le (a : I → M) (b : M) :
    algebraGram (fun i => b * a i) ≤ ‖b‖ ^ 2 • algebraGram a := by
  have hb : star b * b ≤ ‖b‖ ^ 2 • (1 : M) := by
    simpa only [star_one, one_mul, mul_one, CStarRing.norm_star_mul_self, pow_two]
      using CStarAlgebra.star_left_conjugate_le_norm_smul (a := (1 : M)) (b := star b * b)
  have hq := weighted_algebraGram_nonneg a (‖b‖ ^ 2 • (1 : M) - star b * b)
    (sub_nonneg.mpr hb)
  have heq : CStarMatrix.ofMatrix (fun i j => star (a i) * (‖b‖ ^ 2 • (1 : M) - star b * b) * a j) = ‖b‖ ^ 2 • algebraGram a - algebraGram (fun i => b * a i) := by
    ext i j
    change star (a i) * (‖b‖ ^ 2 • (1 : M) - star b * b) * a j =
      ‖b‖ ^ 2 • (star (a i) * a j) - star (b * a i) * (b * a j)
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, star_mul, mul_assoc]
  rw [heq] at hq
  exact sub_nonneg.mp hq

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CompletelyPositiveCompression
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert-space compression preserves complete positivity. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H K I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype I]

lemma operatorMatrix_nonneg_of_quadratic
    (B : CStarMatrix I I (H →L[ℂ] H))
    (hB : ∀ ξ : I → H, 0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (B i j (ξ j))) : 0 ≤ B := by
  let ρ := WeakPureInfiniteness.matrixOperatorHom (n := I) (H := H)
  apply (NonUnitalStarAlgHom.map_le_map_iff ρ
    WeakPureInfiniteness.matrixOperator_injective).mp
  rw [map_zero, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  intro ξ
  have hp : 0 ≤ inner ℂ ξ (ρ B ξ) := by
    change 0 ≤ inner ℂ ξ (WeakPureInfiniteness.matrixOperator B ξ)
    simpa only [WeakPureInfiniteness.matrixOperator_apply, PiLp.inner_apply, inner_sum]
      using hB ξ
  have hq : 0 ≤ inner ℂ (ρ B ξ) ξ := by
    rw [← inner_conj_symm (𝕜 := ℂ) (ρ B ξ) ξ]
    exact star_nonneg_iff.mpr hp
  exact ⟨Complex.ext (by simp) hq.2, hq.1⟩

def compressCompletelyPositive (φ : CompletelyPositiveMap A (K →L[ℂ] K))
    (V : H →L[ℂ] K) : CompletelyPositiveMap A (H →L[ℂ] H) where
  toFun a := V.adjoint.comp ((φ a).comp V)
  map_add' a b := by ext ξ; simp
  map_smul' z a := by ext ξ; simp
  map_cstarMatrix_nonneg' n B hB := by
    apply operatorMatrix_nonneg_of_quadratic
    intro ξ
    change 0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (V.adjoint (φ (B i j) (V (ξ j))))
    simp only [ContinuousLinearMap.adjoint_inner_right]
    exact operatorMatrix_quadratic_nonneg (B.map φ) (φ.map_cstarMatrix_nonneg B hB)
      (fun i => V (ξ i))

@[simp] lemma compressCompletelyPositive_apply
    (φ : CompletelyPositiveMap A (K →L[ℂ] K)) (V : H →L[ℂ] K) (a : A) :
    compressCompletelyPositive φ V a = V.adjoint.comp ((φ a).comp V) := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_StinespringBounds
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded left action on the positive-kernel construction. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

/-- The quadratic form of a finite operator matrix, as a positive functional. -/
def operatorMatrixVectorFunctional (ξ : I → H) :
    CStarMatrix I I (H →L[ℂ] H) →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun A := ∑ i, ∑ j, inner ℂ (ξ i) (A i j (ξ j))
      map_add' A B := by
        simp only [CStarMatrix.add_apply, add_apply,
          inner_add_right, Finset.sum_add_distrib]
      map_smul' z A := by
        simp only [CStarMatrix.smul_apply, smul_apply,
          inner_smul_right, smul_eq_mul, Finset.mul_sum, RingHom.id_apply] }
    (fun A hA => operatorMatrix_quadratic_nonneg A hA ξ)

/-- Applying a completely positive map entrywise before a vector quadratic
form yields a positive functional on the original matrix algebra. -/
def cpMatrixVectorFunctional (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : I → H) :
    CStarMatrix I I M →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((operatorMatrixVectorFunctional ξ).toLinearMap.comp (CStarMatrix.mapₗ φ.toLinearMap))
    (fun A hA => operatorMatrix_quadratic_nonneg _ (φ.map_cstarMatrix_nonneg A hA) ξ)

lemma completelyPositive_kernel_left_bound
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : I → M) (ξ : I → H) (b : M) :
    (∑ i, ∑ j, inner ℂ (ξ i) (φ (star (b * a i) * (b * a j)) (ξ j))).re ≤
      ‖b‖ ^ 2 * (∑ i, ∑ j, inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j))).re := by
  have h := (cpMatrixVectorFunctional φ ξ).monotone (algebraGram_left_le a b)
  change cpMatrixVectorFunctional φ ξ (algebraGram (fun i => b * a i)) ≤
    cpMatrixVectorFunctional φ ξ (‖b‖ ^ 2 • algebraGram a) at h
  rw [PositiveLinearMap.map_smul_of_tower] at h
  have hr := h.1
  rw [← Complex.coe_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hr
  exact hr

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_IsometryDefectColumns
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Orthogonal columns from an isometry defect

A nonunitary isometry supplies countably many equivalent, orthogonal defect
projections. This is an algebraic ingredient of the properly infinite case.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

lemma isometry_pow_cancel {v : M} (hv : star v * v = 1) (n k : ℕ) :
    star (v ^ n) * v ^ (n + k) = v ^ k := by
  rw [pow_add, ← mul_assoc, isometry_pow_initial hv, one_mul]

lemma isometryDefect_projection {v : M} (hv : star v * v = 1) :
    IsStarProjection (isometryDefect v) := by
  apply IsStarProjection.one_sub
  refine ⟨?_, IsSelfAdjoint.mul_star_self v⟩
  calc
    (v * star v) * (v * star v) = v * (star v * v) * star v := by simp only [mul_assoc]
    _ = v * star v := by rw [hv, mul_one]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_OrthogonalPartialIsoSums
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countable orthogonal sums of partial isometries

These sums supply the actual shift operators used in the properly infinite
case. Both initial and final projections are identified by their least-upper-
bound properties; no trace is used.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {I : Type*}

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIso_finset_sum_data (v : I → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (s : Finset I) :
    ∃ w : PartialIso M, (w : M) = ∑ i ∈ s, (v i : M) ∧
      w.initial = ∑ i ∈ s, (v i).initial ∧ w.final = ∑ i ∈ s, (v i).final := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | @insert i s his ih =>
      obtain ⟨w, hw, hwi, hwf⟩ := ih
      have hI : (v i).initial * w.initial = 0 := by
        rw [hwi, Finset.mul_sum]
        exact Finset.sum_eq_zero (fun j hj => hi i j (fun h => his (h ▸ hj)))
      have hF : (v i).final * w.final = 0 := by
        rw [hwf, Finset.mul_sum]
        exact Finset.sum_eq_zero (fun j hj => hf i j (fun h => his (h ▸ hj)))
      refine ⟨(v i).orthogonalSum w hI hF, ?_, ?_, ?_⟩
      · change (v i : M) + (w : M) = _
        rw [hw, Finset.sum_insert his]
      · rw [PartialIso.orthogonalSum_initial, hwi, Finset.sum_insert his]
      · rw [PartialIso.orthogonalSum_final, hwf, Finset.sum_insert his]

def partialIsoFinsetSum (v : I → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (s : Finset I) : PartialIso M :=
  (partialIso_finset_sum_data v hi hf s).choose

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_coe (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s : M) = ∑ i ∈ s, (v i : M) :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_initial (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s).initial = ∑ i ∈ s, (v i).initial :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.2.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_final (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s).final = ∑ i ∈ s, (v i).final :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.2.2

lemma partialIsoFinsetSum_mono (v : I → PartialIso M) (hi hf)
    {s t : Finset I} (hst : s ⊆ t) :
    partialIsoFinsetSum v hi hf s ≤ partialIsoFinsetSum v hi hf t := by
  classical
  constructor
  · rw [partialIsoFinsetSum_initial, partialIsoFinsetSum_initial]
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (v i).initial_proj.nonneg)
  · rw [partialIsoFinsetSum_coe, partialIsoFinsetSum_initial, Finset.mul_sum,
      partialIsoFinsetSum_coe]
    apply Finset.sum_congr rfl
    intro i his
    rw [Finset.sum_mul]
    calc
      _ = (v i : M) * (v i).initial := Finset.sum_eq_single i (fun j _ hji => ?_)
        (fun hit => (hit (hst his)).elim)
      _ = (v i : M) := (v i).mul_initial
    calc
        (v j : M) * (v i).initial = ((v j : M) * (v j).initial) * (v i).initial := by
          rw [(v j).mul_initial]
        _ = 0 := by rw [mul_assoc, hi j i hji, mul_zero]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A countable family with mutually orthogonal initial and final projections
has a sum whose initial and final projections are the respective suprema. -/
theorem exists_countable_partialIso_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (v : ℕ → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    ∃ w : PartialIso M, (∀ i, (v i).initial ≤ w.initial) ∧
      (∀ i, (v i).final ≤ w.final) ∧
      (∀ p : M, IsStarProjection p → (∀ i, (v i).initial ≤ p) → w.initial ≤ p) ∧
      (∀ p : M, IsStarProjection p → (∀ i, (v i).final ≤ p) → w.final ≤ p) := by
  classical
  let V (n : ℕ) := partialIsoFinsetSum v hi hf (Finset.range n)
  have hm : Monotone V := fun _ _ h => partialIsoFinsetSum_mono v hi hf (Finset.range_mono h)
  have hc : IsChain (· ≤ ·) (Set.range V) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact (le_total i j).imp (fun h => hm h) (fun h => hm h)
  obtain ⟨w, hw, _, hwi, hwf⟩ := exists_partialIso_chain_supremum e (Set.range V) hc
    ⟨V 0, Set.mem_range_self 0⟩
  have hsumI (p : M) (hp : IsStarProjection p) (h : ∀ i, (v i).initial ≤ p) (n : ℕ) :
      (V n).initial ≤ p := by
    apply ((V n).initial_proj.le_iff_mul_eq_right hp).mpr
    rw [partialIsoFinsetSum_initial, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => ((v i).initial_proj.le_iff_mul_eq_right hp).mp (h i))
  have hsumF (p : M) (hp : IsStarProjection p) (h : ∀ i, (v i).final ≤ p) (n : ℕ) :
      (V n).final ≤ p := by
    apply ((V n).final_proj.le_iff_mul_eq_right hp).mpr
    rw [partialIsoFinsetSum_final, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => ((v i).final_proj.le_iff_mul_eq_right hp).mp (h i))
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro i
    apply le_trans _ (hw (V (i + 1)) (Set.mem_range_self _)).1
    rw [partialIsoFinsetSum_initial]
    exact Finset.single_le_sum (fun j _ => (v j).initial_proj.nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_self i))
  · intro i
    apply le_trans _ (PartialIso.final_mono (hw (V (i + 1)) (Set.mem_range_self _)))
    rw [partialIsoFinsetSum_final]
    exact Finset.single_le_sum (fun j _ => (v j).final_proj.nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_self i))
  · intro p hp h
    apply hwi p hp
    rintro _ ⟨n, rfl⟩
    exact hsumI p hp h n
  · intro p hp h
    apply hwf p hp
    rintro _ ⟨n, rfl⟩
    exact hsumF p hp h n

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveCompression
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normality of positive functionals localized to a projection corner. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma compressionPositive_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    TraceInPredual e (compressionPositive hp ψ) := by
  apply (mem_normalDual e (positiveFunctionalCLM (compressionPositive hp ψ))).mp
  rw [compressionPositive_clm]
  apply normalDual_comp e _ _ (HochschildSakai.mul_hasPreadjoint e p)
  exact normalDual_comp e ((mem_normalDual e (positiveFunctionalCLM ψ)).mpr hψ) _
    ((HochschildSakai.abstract_multiplication_normal e).2 p)

/-- Domination on the projections of a corner suffices to make a positive
compression normal when the dominating functional is normal. -/
theorem compression_normal_of_projection_dominance (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (χ ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (hle : ∀ q : M, IsStarProjection q → q ≤ p → χ q ≤ ψ q) :
    TraceInPredual e (compressionPositive hp χ) := by
  let L := CentralCorner.includeMap p hp
  let F := (positiveFunctionalCLM ψ - positiveFunctionalCLM χ).comp L
  have hreal : ∀ a : Corner p hp, IsSelfAdjoint a → (F a).im = 0 := by
    intro a ha
    have haM : IsSelfAdjoint (a : M) := congrArg Subtype.val ha.star_eq
    have hψa : (ψ (a : M)).im = 0 :=
      (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (haM.map ψ)
    have hχa : (χ (a : M)).im = 0 :=
      (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (haM.map χ)
    change (ψ (a : M) - χ (a : M)).im = 0
    rw [Complex.sub_im, hψa, hχa, sub_self]
  have hproj : ∀ q : Corner p hp, IsStarProjection q → 0 ≤ F q := by
    intro q hq
    change 0 ≤ ψ (q : M) - χ (q : M)
    exact sub_nonneg.mpr (hle q (corner_projection_coe p hp hq) (corner_projection_le p hp hq))
  apply positive_normal_of_dominated e (compressionPositive hp χ) (compressionPositive hp ψ)
    (compressionPositive_normal e hp ψ hψ)
  intro a ha
  let c : Corner p hp := ⟨p * a * p, by
    constructor
    · rw [← mul_assoc, ← mul_assoc, hp.isIdempotentElem.eq]
    · rw [mul_assoc, hp.isIdempotentElem.eq]⟩
  have hc : 0 ≤ c := by
    change 0 ≤ p * a * p
    simpa only [hp.isSelfAdjoint.star_eq] using star_right_conjugate_nonneg ha p
  have hh := eval_nonneg_of_projection_nonneg (cornerPredualEquiv p hp e) F hreal hproj c hc
  exact sub_nonneg.mp hh

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveCompleteAdditivity
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.predualNormalEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete additivity implies normality for positive functionals

The positive-functional case of Takesaki's criterion, as proved in Ringrose,
*Lectures on the trace in a finite von Neumann algebra*, Lemmas 4.1--4.3.
Only this case is needed for the normal-state orbit in the trace construction.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma exists_normal_positive_larger_on_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {E : M} (hE : IsStarProjection E) (hE0 : E ≠ 0) (c : ℝ) :
    ∃ φ : M →ₚ[ℂ] ℂ, TraceInPredual e φ ∧ c < (φ E).re := by
  obtain ⟨ρ, hρ, _, hρE, _⟩ := exists_normal_state_on_projection e hE hE0
  let C : ℝ := max c 0 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let φ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := (C : ℂ) • ρ.toLinearMap
      monotone' := fun _ _ hab => mul_le_mul_of_nonneg_left (ρ.monotone hab)
        (Complex.zero_le_real.mpr hC) }
  refine ⟨φ, ?_, ?_⟩
  · have hφ : positiveFunctionalCLM φ = (C : ℂ) • positiveFunctionalCLM ρ := rfl
    apply (mem_normalDual e (positiveFunctionalCLM φ)).mp
    rw [hφ]
    exact (normalDual e).smul_mem _ ((mem_normalDual e (positiveFunctionalCLM ρ)).mpr hρ)
  · change c < ((C : ℂ) * ρ E).re
    rw [hρE, mul_one, Complex.ofReal_re]
    dsimp [C]
    linarith [le_max_left c 0]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UnitaryPredualAction
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The isometric unitary action on a von Neumann predual. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable [PartialOrder M] [StarOrderedRing M]

lemma unitaryPullback_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : StrongDual ℂ M} (hF : F ∈ normalDual e) (u : unitary M) :
    unitaryPullback F u ∈ normalDual e := by
  apply unitaryOrbitHull_normal e hF
  exact subset_closure (subset_convexHull ℝ _ (Set.mem_range_self u))

/-- The same action restricted to normal functionals. -/
def normalUnitaryEquiv (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (u : unitary M) :
    normalDual e ≃ₗᵢ[ℂ] normalDual e where
  toFun F := ⟨unitaryPullback F.val u, unitaryPullback_normal e F.property u⟩
  invFun F := ⟨unitaryPullback F.val (star u), unitaryPullback_normal e F.property (star u)⟩
  left_inv F := Subtype.ext ((unitaryDualEquiv u).left_inv F.val)
  right_inv F := Subtype.ext ((unitaryDualEquiv u).right_inv F.val)
  map_add' F G := Subtype.ext (by ext a; rfl)
  map_smul' c F := Subtype.ext (by ext a; rfl)
  norm_map' F := (unitaryDualEquiv u).norm_map F.val

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeIColumnArithmetic
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite orthogonal column arithmetic for the type I decomposition. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  {n : ℕ} {p : M}

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_sum_projection (v : Fin n → PartialIso M)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    IsStarProjection (∑ i, (v i).final) :=
  orthogonal_projection_finset_sum (fun i => (v i).final) (fun i => (v i).final_proj)
    ho Finset.univ

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_mul_residual (v : Fin n → PartialIso M)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (i : Fin n) :
    (v i).final * (1 - ∑ j, (v j).final) = 0 := by
  classical
  rw [mul_sub, mul_one, Finset.mul_sum, Finset.sum_eq_single i]
  · rw [(v i).final_proj.isIdempotentElem.eq, sub_self]
  · intro j _ hji
    exact ho i j hji.symm
  · simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma exists_append_columns (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (w : PartialIso M) (hwi : w.initial = p)
    (hwo : ∀ i, (v i).final * w.final = 0) :
    ∃ u : Fin (n + 1) → PartialIso M,
      (∀ i, (u i).initial = p) ∧
      (∀ i j, i ≠ j → (u i).final * (u j).final = 0) ∧
      (∑ i, (u i).final) = w.final + ∑ i, (v i).final := by
  let u : Fin (n + 1) → PartialIso M := Fin.cons w v
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i
    exact Fin.cases hwi hi i
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact (h rfl).elim
    · intro _
      exact PartialIso.orthogonal_final_symm (hwo j)
    · intro _
      exact hwo i
    · intro h
      exact ho i j (fun he => h (congrArg Fin.succ he))
  · simp only [u, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma column_count_trace_le (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (v : Fin n → PartialIso M) (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    (n : ℝ) * (τ p).re ≤ (τ 1).re := by
  have ht (i : Fin n) : τ (v i).final = τ p := by
    change τ ((v i : M) * star (v i : M)) = τ p
    rw [htr]
    exact congrArg τ (hi i)
  have h := Complex.re_le_re (τ.monotone (column_sum_projection v ho).le_one)
  change (τ.toLinearMap (∑ i, (v i).final)).re ≤ (τ 1).re at h
  rw [map_sum] at h
  change Complex.reCLM (∑ i, τ (v i).final) ≤ (τ 1).re at h
  rw [map_sum] at h
  simpa only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Complex.reCLM_apply] using h

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeIColumnExtension
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend an abelian column family unless a homogeneous central piece exists. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem extend_columns_of_no_homogeneous_piece (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : ∀ z : M, CentralProjection z → z ≠ 0 → ¬ HomogeneousTypeICorner z)
    {p : M} (hp : AbelianProjection p) (hpfull : IsCentralSupport p 1)
    {n : ℕ} (v : Fin n → PartialIso M) (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    ∃ w : PartialIso M, w.initial = p ∧ w.final ≤ 1 - ∑ i, (v i).final := by
  let r := 1 - ∑ i, (v i).final
  have hr : IsStarProjection r := (column_sum_projection v ho).one_sub
  obtain ⟨t, ht⟩ := exists_central_support e hr
  have ht1 : t = 1 := by
    by_contra ht1
    have hz : CentralProjection (1 - t) :=
      ⟨ht.1.1.one_sub, fun a => (Commute.one_left a).sub_left (ht.1.2 a)⟩
    have hz0 : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    apply hno (1 - t) hz hz0
    apply homogeneousCorner_of_annihilated_residual hp hz hz0 v hi ho
    change (1 - t) * r = 0
    rw [sub_mul, one_mul, (hr.le_iff_mul_eq_right ht.1.1).mp ht.2.1, sub_self]
  have hrfull : IsCentralSupport r 1 := by simpa only [ht1] using ht
  obtain ⟨z, u, hz, hui, huf, hzf, hzi⟩ := trace_free_central_comparison e hp.1 hr
  by_cases hz0 : z = 0
  · refine ⟨u, ?_, huf⟩
    simpa only [hz0, sub_zero, one_mul] using hzi
  exfalso
  apply hno z hz hz0
  let c := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) u
  have hci : c.initial ≤ p := by
    apply le_trans _ hui
    apply (c.initial_proj.le_iff_mul_eq_left u.initial_proj).mpr
    simp only [c, centralCutPartialIso_initial, mul_assoc, u.initial_proj.isIdempotentElem.eq]
  have hcf : c.final = z * r := by
    simpa only [c, centralCutPartialIso_final] using hzf
  have habelr : AbelianProjection (z * r) := by
    rw [← hcf]
    exact abelian_partialIso c (HochschildTypeII.abelian_of_le hp c.initial_proj hci)
  have hzp : IsStarProjection (z * p) := hz.1.mul hp.1 (hz.2 p)
  have hzple : z * p ≤ p := (hzp.le_iff_mul_eq_left hp.1).mpr
    (by rw [mul_assoc, hp.1.isIdempotentElem.eq])
  have habelp := HochschildTypeII.abelian_of_le hp hzp hzple
  obtain ⟨w, hwi, hwf⟩ := abelian_equivalent_of_central_support e habelp habelr
    (hpfull.centralCut_one hp.1 hz) (hrfull.centralCut_one hr hz)
  let a (i : Fin n) := centralCutPartialIso z hz.1 (fun b => (hz.2 b).eq) (v i)
  have hai (i : Fin n) : (a i).initial = z * p := by
    simp only [a, centralCutPartialIso_initial, hi]
  have hao (i j : Fin n) (hij : i ≠ j) : (a i).final * (a j).final = 0 := by
    simp only [a, centralCutPartialIso_final]
    rw [central_idempotent_mul z hz.1.isIdempotentElem.eq (fun b => (hz.2 b).eq),
      ho i j hij, mul_zero]
  have haw (i : Fin n) : (a i).final * w.final = 0 := by
    simp only [a, centralCutPartialIso_final, hwf]
    rw [central_idempotent_mul z hz.1.isIdempotentElem.eq (fun b => (hz.2 b).eq),
      column_mul_residual v ho i, mul_zero]
  obtain ⟨b, hbi, hbo, hbs⟩ := exists_append_columns a hai hao w hwi haw
  have hsum : ∑ i, (b i).final = z := by
    rw [hbs, hwf]
    simp only [a, centralCutPartialIso_final, ← Finset.mul_sum]
    change z * (1 - ∑ i, (v i).final) + z * ∑ i, (v i).final = z
    noncomm_ring
  apply homogeneousCorner_of_annihilated_residual habelp hz hz0 b hbi hbo
  rw [hsum]
  exact hz.1.mul_one_sub_self

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TracialTypeIHomogeneousPiece
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full abelian projection in a faithfully tracial algebra yields a
nonzero finite homogeneous central summand. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_homogeneous_piece_of_full_abelian_trace
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hfaith : ∀ a : M, τ (star a * a) = 0 → a = 0)
    {p : M} (hp : AbelianProjection p) (hp0 : p ≠ 0) (hfull : IsCentralSupport p 1) :
    ∃ z : M, CentralProjection z ∧ z ≠ 0 ∧ HomogeneousTypeICorner z := by
  classical
  by_contra hfail
  push Not at hfail
  have hno : ∀ z : M, CentralProjection z → z ≠ 0 → ¬ HomogeneousTypeICorner z := hfail
  have hpτ : τ p ≠ 0 := by
    intro hzero
    apply hp0
    apply hfaith p
    simpa only [hp.1.isSelfAdjoint.star_eq, hp.1.isIdempotentElem.eq] using hzero
  have hpτpos : 0 < (τ p).re := by
    have hn := Complex.nonneg_iff.mp (τ.map_nonneg hp.1.nonneg)
    have hne : (τ p).re ≠ 0 := by
      intro hzero
      apply hpτ
      apply Complex.ext
      · exact hzero
      · exact hn.2.symm
    exact lt_of_le_of_ne hn.1 (Ne.symm hne)
  obtain ⟨N, hN⟩ := exists_nat_gt ((τ 1).re / (τ p).re)
  have hbound : (τ 1).re < (N : ℝ) * (τ p).re := (div_lt_iff₀ hpτpos).mp hN
  have hcolumns (n : ℕ) : ∃ v : Fin n → PartialIso M,
      (∀ i, (v i).initial = p) ∧
      (∀ i j, i ≠ j → (v i).final * (v j).final = 0) := by
    induction n with
    | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ n ih =>
      obtain ⟨v, hi, ho⟩ := ih
      obtain ⟨w, hwi, hwf⟩ := extend_columns_of_no_homogeneous_piece e hno hp hfull v hi ho
      have hcross (i : Fin n) : (v i).final * w.final = 0 := by
        have he := (w.final_proj.le_iff_mul_eq_right (column_sum_projection v ho).one_sub).mp hwf
        calc
          _ = (v i).final * ((1 - ∑ j, (v j).final) * w.final) := by rw [he]
          _ = 0 := by rw [← mul_assoc, column_mul_residual v ho i, zero_mul]
      obtain ⟨u, hui, huo, _⟩ := exists_append_columns v hi ho w hwi hcross
      exact ⟨u, hui, huo⟩
  obtain ⟨v, hi, ho⟩ := hcolumns N
  exact (not_le_of_gt hbound) (column_count_trace_le τ htr v hi ho)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_HomogeneousCornerTransport
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of the homogeneous pieces used in the finite type I partition. -/

noncomputable section

namespace HochschildMatrixSystems.MatrixSystem

variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N] {n : ℕ}

def mapEquiv (E : HochschildMatrixSystems.MatrixSystem M n) (φ : M ≃⋆ₐ[ℂ] N) :
    HochschildMatrixSystems.MatrixSystem N n where
  entry i j := φ (E.entry i j)
  star_entry i j := by rw [← map_star, E.star_entry]
  entry_mul i j k l := by rw [← map_mul, E.entry_mul]; split_ifs <;> simp
  sum_diagonal := by rw [← map_sum, E.sum_diagonal, map_one]

end HochschildMatrixSystems.MatrixSystem

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners HochschildMatrixSystems FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma abelian_map_equiv {N : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
    (φ : M ≃⋆ₐ[ℂ] N) {p : M} (hp : AbelianProjection p) : AbelianProjection (φ p) :=
  finitePath_abelian_of_popa (hp.1.map φ)
    (abelianProjection_map_equiv φ hp.1 (popa_abelian_of_finitePath hp))

def projectionInCorner {z p : M} (hz : IsStarProjection z) (hp : IsStarProjection p)
    (hpz : p ≤ z) : Corner z hz := ⟨p, projection_mem_corner hz hp hpz⟩

lemma projectionInCorner_abelian {z p : M} (hz : IsStarProjection z)
    (hp : AbelianProjection p) (hpz : p ≤ z) :
    AbelianProjection (projectionInCorner hz hp.1 hpz) := by
  refine ⟨⟨Subtype.ext hp.1.isIdempotentElem.eq, Subtype.ext hp.1.isSelfAdjoint.star_eq⟩, ?_⟩
  intro a b
  exact Subtype.ext (hp.2 (a : M) (b : M)).eq

lemma centralSupport_in_corner {z p : M} (hz : IsStarProjection z)
    (hzc : ∀ a : M, z * a = a * z) (hp : IsStarProjection p) (h : IsCentralSupport p z) :
    IsCentralSupport (projectionInCorner hz hp h.2.1) (1 : Corner z hz) := by
  refine ⟨⟨IsStarProjection.one _, fun _ => Commute.one_left _⟩, ?_, ?_⟩
  · exact (show IsStarProjection (projectionInCorner hz hp h.2.1) from
      ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩).le_one
  · intro c hc hcp
    have hcM : CentralProjection (c : M) :=
      ⟨corner_projection_coe z hz hc.1,
        fun a => centralCorner_central hz hzc c (fun b => (hc.2 b).eq) a⟩
    have hcpM : (c : M) * p = 0 := congrArg Subtype.val hcp
    have hcz := h.2.2 (c : M) hcM hcpM
    have hc0 : c = 0 := by
      apply Subtype.ext
      change (c : M) = 0
      simpa only [c.property.2] using hcz
    simp only [hc0, zero_mul]

lemma homogeneousCorner_to_ambient {z : M} (hz : IsStarProjection z)
    (q : Corner z hz) (hq : HomogeneousTypeICorner q) :
    HomogeneousTypeICorner (q : M) := by
  obtain ⟨hqp, n, E, i, hi⟩ := hq
  let φ := nestedCornerEquiv hz q hqp
  exact ⟨corner_projection_coe z hz hqp, n, E.mapEquiv φ, i, abelian_map_equiv φ hi⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteTypeIPieces
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence of finite homogeneous central pieces in finite type I algebras. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners FinitePathMain

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_homogeneous_piece_of_abelian_trace
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hfaith : ∀ a : M, τ (star a * a) = 0 → a = 0)
    {p : M} (hp : AbelianProjection p) (hp0 : p ≠ 0) :
    ∃ z : M, CentralProjection z ∧ z ≠ 0 ∧ HomogeneousTypeICorner z := by
  obtain ⟨c, hc⟩ := exists_central_support e hp.1
  have hc0 : c ≠ 0 := fun h => hp0 ((hc.eq_zero_iff hp.1).mpr h)
  let eC := cornerPredualEquiv c hc.1.1 e
  let τC := cornerTrace c hc.1.1 τ
  have hpC := projectionInCorner_abelian hc.1.1 hp hc.2.1
  have hpC0 : projectionInCorner hc.1.1 hp.1 hc.2.1 ≠ 0 :=
    fun h => hp0 (congrArg Subtype.val h)
  obtain ⟨q, hq, hq0, hhom⟩ := exists_homogeneous_piece_of_full_abelian_trace eC τC
    (cornerTrace_tracial c hc.1.1 τ htr) (cornerTrace_faithful c hc.1.1 τ hfaith hc0)
    hpC hpC0 (centralSupport_in_corner hc.1.1 (fun a => (hc.1.2 a).eq) hp.1 hc)
  exact ⟨(q : M), ⟨corner_projection_coe c hc.1.1 hq.1,
    fun a => centralCorner_central hc.1.1 (fun a => (hc.1.2 a).eq) q
      (fun b => (hq.2 b).eq) a⟩,
    (fun h => hq0 (Subtype.ext h)), homogeneousCorner_to_ambient hc.1.1 q hhom⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PaulsenExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the two-by-two operator-system map into operators on the doubled
Hilbert space, using the proved positive extension theorem. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev doubleMatrixHom : Mat (H →L[ℂ] H) →⋆ₙₐ[ℂ]
    (HilbertDouble H →L[ℂ] HilbertDouble H) :=
  WeakPureInfiniteness.matrixOperatorHom (n := Fin 2) (H := H)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_DoubleCoordinates
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate isometries in the doubled Hilbert space and extraction of
operator matrix entries. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def doubleCoordinate (i : Fin 2) : H →ₗᵢ[ℂ] HilbertDouble H where
  toFun ξ := PiLp.single 2 i ξ
  map_add' ξ η := PiLp.single_add 2 i
  map_smul' z ξ := by
    apply PiLp.ext
    intro j
    simp [PiLp.single_apply]
  norm_map' ξ := by simp

end BoundedHochschild.KadisonRingrose

end

end OAI
end


