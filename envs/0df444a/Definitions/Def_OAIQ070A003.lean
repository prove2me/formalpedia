-- Prove2me | Definitions.Def_OAIQ070A003
-- name    : OAIQ070A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:16:53.911394+00:00
-- url     : https://prove2.me/theorems/e9f11bfc-5fc1-4774-87f0-6878314c71ee
-- title:
--   Definitions bundle OAIQ070A003 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 155 declarations of OpenAI's Lean: 92 definitions, 5 instances and 58 theorems. The definitions and types are `OAI.YauCounterexamples.ThreeAmbient`, `OAI.YauCounterexamples.ThreeManifold`, `OAI.YauCounterexamples.ThreeModel`, `OAI.YauCounterexamples.ThreeProductModel`, `OAI.YauCounterexamples.ThreeRegular`, `OAI.YauCounterexamples.UniformJetBounds`, `OAI.YauCounterexamples.VanishTo`, `OAI.YauCounterexamples.actualDualNorm`, `OAI.YauCounterexamples.actualDualSpace`, `OAI.YauCounterexamples.ambientPowerGradient`, `OAI.YauCounterexamples.anisotropicConstant`, `OAI.YauCounterexamples.anisotropicHalfResolventSymbol`, `OAI.YauCounterexamples.anisotropicResolventSymbol`, `OAI.YauCounterexamples.bilinearCoordinateMatrix`, `OAI.YauCounterexamples.bilinearPinning`, `OAI.YauCounterexamples.bilinearTransverse`, `OAI.YauCounterexamples.boundedDegreeMonomials`, `OAI.YauCounterexamples.bundleExp`, `OAI.YauCounterexamples.bundleMetricInner`, `OAI.YauCounterexamples.bundlePullbackMetric`, `OAI.YauCounterexamples.bundleRankOne`, `OAI.YauCounterexamples.bundleTransverse`, `OAI.YauCounterexamples.chartTangentBasis`, `OAI.YauCounterexamples.chartTensorCoordLocal1`, `OAI.YauCounterexamples.chartTensorCoordLocal10`, `OAI.YauCounterexamples.chartTensorCoordLocal2`, `OAI.YauCounterexamples.chartTensorCoordLocal9`, `OAI.YauCounterexamples.chartTensorNeighborhoodInst1`, `OAI.YauCounterexamples.chartTensorNeighborhoodInst2`, `OAI.YauCounterexamples.clmMatrixAlgHom`, `OAI.YauCounterexamples.compactSmoothContinuityInst1`, `OAI.YauCounterexamples.compactSmoothContinuityInst2`, `OAI.YauCounterexamples.compactSmoothJetMap`, `OAI.YauCounterexamples.compactSmoothMetricSpace`, `OAI.YauCounterexamples.complexCoordinateMetricLaplacian`, `OAI.YauCounterexamples.complexGaussianRealValue`, `OAI.YauCounterexamples.complexGramTrace`, `OAI.YauCounterexamples.complexPhaseVector`, `OAI.YauCounterexamples.complexRealResponse`, `OAI.YauCounterexamples.complexValueVector` and 52 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_DifferentialEq_MfderivReModelTarget`, `SmoothYau_Estimates_ClmMatrixAlgHom`, `SmoothYau_Estimates_ComplexGaussianRealValue`, `SmoothYau_Estimates_ComplexGramTrace`, `SmoothYau_Estimates_FixedRadialChoice`, `SmoothYau_Estimates_GeneratedCutoffWaveEndpointRatio`, `SmoothYau_Estimates_PhaseFormMatrix`, `SmoothYau_Estimates_TransportCorrection`, `SmoothYau_Geometry_AnnularRelativeMargin`, `SmoothYau_Geometry_ChartTensorNeighborhoodInst1`, `SmoothYau_Geometry_ConformalMetric`, `SmoothYau_Geometry_MetricGradient`, `SmoothYau_Geometry_PinnedMetricJointGradientPair`, `SmoothYau_Geometry_RadialFiniteDualNorm`, `SmoothYau_Geometry_RoundMetricExists`, `SmoothYau_Geometry_SymmLChartTrivialization`, `SmoothYau_Limits_ManifoldChartPush`, `SmoothYau_Smoothness_BoundedDegreeMonomials`, `SmoothYau_Smoothness_BundleMetricInner`, `SmoothYau_Smoothness_BundleRankOne`, `SmoothYau_Smoothness_ChartTensorCoordLocal1`, `SmoothYau_Smoothness_CompactSmoothJetMap`, `SmoothYau_Smoothness_ComplexPolarWeight`, `SmoothYau_Smoothness_ContinuousCompactSmoothJets`, `SmoothYau_Smoothness_CoordinateMetricFlux`, `SmoothYau_Smoothness_MultilinearPolynomial`, `SmoothYau_Smoothness_NormIteratedFDerivScalarDirection`, `SmoothYau_Smoothness_PolynomialFiniteWave`, `SmoothYau_Smoothness_ProfilePeriodizeEventuallyZero`, `SmoothYau_Smoothness_PulledGradient`, `SmoothYau_Smoothness_SmoothFiniteWaveSum`, `SmoothYau_Smoothness_TorusAmbient`, `SmoothYau_Smoothness_WaveDeriv`, `SmoothYau_Spectrum_AnisotropicConstant`, `SmoothYau_Spectrum_BilinearCoordinateMatrixPosDef`, `SmoothYau_Spectrum_BilinearTransverse`, `SmoothYau_Spectrum_JointLocalLaplacian`, `SmoothYau_Spectrum_SphereProjection`, `SmoothYau_Spectrum_ThreeCoupledNormedSpace`, `SmoothYau_SphereMetric_ComplexRealResponse`, `SmoothYau_SphereMetric_FourThree`, `SmoothYau_SphereMetric_ThreeFixedFormNorm`, `SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A006`, `OAIQ070A007` and `OAIQ070A008`; the statements `OAI.YauCounterexamples.common_near_wave_sign_probability`, `OAI.YauCounterexamples.finite_near_far_sign_probability`, `OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ`, `OAI_YauCounterexamples_laplaceBeltrami_self_any_basis`, `OAI_YauCounterexamples_productSphere_fstPower_trace`, `OAI.YauCounterexamples.productSphere_power_trace`, `OAI.YauCounterexamples.productSphere_sndPower_trace`, `OAI.YauCounterexamples.three_cutoff_control_bounds` and `OAI_YauCounterexamples_three_cutoff_raw_bounded_by_near_one`; the proofs of `OAI.YauCounterexamples.common_near_wave_sign_probability`, `OAI.YauCounterexamples.finite_near_far_sign_probability`, `OAI_YauCounterexamples_productSphere_fstPower_trace`, `OAI.YauCounterexamples.productSphere_power_trace`, `OAI.YauCounterexamples.productSphere_sndPower_trace`, `OAI.YauCounterexamples.three_cutoff_control_bounds` and `OAI_YauCounterexamples_three_cutoff_raw_bounded_by_near_one`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau

section
-- module Solutions.OAIQ070_YAU.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_MfderivReModelTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace F M]

@[instance_reducible]
def reModelChartedSpace (L : F ≃L[ℝ] E) : ChartedSpace E M where
  atlas := (fun e : OpenPartialHomeomorph M F => e.trans L.toHomeomorph.toOpenPartialHomeomorph) '' atlas F M
  chartAt x := (chartAt F x).trans L.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt F x,chart_mem_atlas _ _,rfl⟩

lemma reModel_isManifold (L : F ≃L[ℝ] E) [IsManifold 𝓘(ℝ,F) ∞ M] :
    @IsManifold ℝ _ E _ _ E _ 𝓘(ℝ,E) ∞ M _ (reModelChartedSpace (M:=M) L) := by
  let := reModelChartedSpace (M:=M) L
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨e,he,rfl⟩ ⟨f,hf,rfl⟩
  have h := (contDiffGroupoid ∞ 𝓘(ℝ,F)).compatible he hf
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  have h₁ : ContDiffOn ℝ ∞ ((e.symm.trans f) : F → F) (e.symm.trans f).source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      range_id, preimage_id, inter_univ, id_comp, comp_id] using h.1
  have hh := L.contDiff.comp_contDiffOn (h₁.comp L.symm.contDiff.contDiffOn
    (mapsTo_preimage _ _))
  have hc : (L.toHomeomorph.toOpenPartialHomeomorph : F → E) = L := rfl
  have hcs : (L.toHomeomorph.toOpenPartialHomeomorph.symm : E → F) = L.symm := rfl
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, preimage_id, inter_univ, id_comp, comp_id,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_target,
    hc, hcs, preimage_univ, preimage_inter, preimage_comp, univ_inter, comp_assoc] using hh

end


section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace F M]
  [TopologicalSpace N] [ChartedSpace G N]

lemma contMDiff_reModel_source (L : F ≃L[ℝ] E) {f : M → N}
    (hf : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,G) ∞ f) :
    letI := reModelChartedSpace (M:=M) L
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,G) ∞ f := by
  let := reModelChartedSpace (M:=M) L
  intro x
  have h := (contMDiffAt_iff.mp (hf x))
  rw [contMDiffAt_iff]
  refine ⟨h.1,?_⟩
  simp only [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] at h ⊢
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id] at h ⊢
  have hh := (show ContDiffAt ℝ ∞ _ (L.symm (L (chartAt F x x))) from by simpa using h.2).comp
    (L (chartAt F x x)) L.symm.contDiff.contDiffAt
  have hc : (chartAt E x : M → E) = L ∘ (chartAt F x) := rfl
  have hcs : ((chartAt E x).symm : E → M) = (chartAt F x).symm ∘ L.symm := rfl
  rw [hc,hcs]
  simpa only [comp_assoc,comp_apply] using hh

end


section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace F M]
  [TopologicalSpace N] [ChartedSpace G N]
lemma mfderiv_reModel_source (L : F ≃L[ℝ] E) {f : M → N}
    (hf : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,G) ∞ f) (x : M) :
    let D : F →L[ℝ] G := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,G) f x
    letI := reModelChartedSpace (M:=M) L
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) f x = D.comp L.symm.toContinuousLinearMap := by
  let D : F →L[ℝ] G := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,G) f x
  have hd := (hf.mdifferentiable (by simp) x).hasMFDerivAt
  rw [HasMFDerivAt] at hd
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, hasFDerivWithinAt_univ,
    id_comp, comp_id] at hd
  change ContinuousAt f x ∧ HasFDerivWithinAt (↑(chartAt G (f x)) ∘ f ∘ ↑(chartAt F x).symm) D Set.univ (chartAt F x x) at hd
  rw [hasFDerivWithinAt_univ] at hd
  let := reModelChartedSpace (M:=M) L
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,G) f x = D.comp L.symm.toContinuousLinearMap
  apply HasMFDerivAt.mfderiv
  change ContinuousAt f x ∧ HasFDerivWithinAt _ _ _ _
  refine ⟨hd.1,?_⟩
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, hasFDerivWithinAt_univ,
    id_comp, comp_id]
  change HasFDerivWithinAt (↑(chartAt G (f x)) ∘ f ∘ ↑(chartAt E x).symm)
    (D.comp L.symm.toContinuousLinearMap : E →L[ℝ] G) Set.univ (chartAt E x x)
  rw [hasFDerivWithinAt_univ]
  have hc : (chartAt E x : M → E) = L ∘ (chartAt F x) := rfl
  have hcs : ((chartAt E x).symm : E → M) = (chartAt F x).symm ∘ L.symm := rfl
  rw [hc,hcs]
  have hh := (show HasFDerivAt _ D (L.symm (L (chartAt F x x))) from by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hd.2).comp
      (L (chartAt F x x)) L.symm.toContinuousLinearMap.hasFDerivAt
  simpa only [comp_assoc,comp_apply] using hh
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ClmMatrixAlgHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open scoped Matrix.Norms.Operator
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def clmMatrixAlgHom (b : Module.Basis ι ℝ E) : (E →L[ℝ] E) →ₐ[ℝ] Matrix ι ι ℝ where
  toFun K := LinearMap.toMatrix b b K.toLinearMap
  map_one' := by simp
  map_mul' A B := by simp [LinearMap.toMatrix_mul]
  map_zero' := by simp
  map_add' A B := by simp
  commutes' r := by
    change LinearMap.toMatrix b b (r • LinearMap.id) = _
    simp [Algebra.algebraMap_eq_smul_one]


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MultilinearPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

open MvPolynomial
variable {σ : Type*}

def realPolyEval (p : MvPolynomial σ ℂ) (x : σ → ℝ) : ℂ :=
  MvPolynomial.eval (fun i => (x i : ℂ)) p

@[simp] theorem realPolyEval_C (c : ℂ) (x : σ → ℝ) : realPolyEval (C c) x = c := by
  simp [realPolyEval]
@[simp] theorem realPolyEval_X (i : σ) (x : σ → ℝ) :
    realPolyEval (X i) x = (x i : ℂ) := by simp [realPolyEval]
@[simp] theorem realPolyEval_add (p q : MvPolynomial σ ℂ) (x : σ → ℝ) :
    realPolyEval (p + q) x = realPolyEval p x + realPolyEval q x := by simp [realPolyEval]
@[simp] theorem realPolyEval_mul (p q : MvPolynomial σ ℂ) (x : σ → ℝ) :
    realPolyEval (p * q) x = realPolyEval p x * realPolyEval q x := by simp [realPolyEval]
@[simp] theorem realPolyEval_zero (x : σ → ℝ) :
    realPolyEval (0 : MvPolynomial σ ℂ) x = 0 := by simp [realPolyEval]
@[simp] theorem realPolyEval_one (x : σ → ℝ) :
    realPolyEval (1 : MvPolynomial σ ℂ) x = 1 := by simp [realPolyEval]


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def multilinearPolynomial {n : ℕ} (B : (σ → ℝ) [×n]→L[ℝ] ℂ) : MvPolynomial σ ℂ :=
  ∑ a : Fin n → σ, C (B fun i => Pi.single (a i) 1) * ∏ i, X (a i)

def realTaylorPolynomial (f : (σ → ℝ) → ℂ) (N : ℕ) : MvPolynomial σ ℂ :=
  ∑ j ∈ Finset.range N,
    C ((j.factorial : ℂ)⁻¹) * multilinearPolynomial (iteratedFDeriv ℝ j f 0)



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BoundedDegreeMonomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
section PolynomialWaves
open MvPolynomial
variable {σ : Type*} [Fintype σ]

def waveDirectionalDerivative (z : σ → ℂ) :
    Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  ∑ i, z i • pderiv i

@[simp] theorem waveDirectionalDerivative_apply (z : σ → ℂ) (f : MvPolynomial σ ℂ) :
    waveDirectionalDerivative z f = ∑ i, z i • pderiv i f := by
  classical
  unfold waveDirectionalDerivative
  have h (s : Finset σ) : (∑ i ∈ s, z i • pderiv i) f =
      ∑ i ∈ s, z i • pderiv i f := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, Derivation.add_apply, Derivation.smul_apply, ih]
  exact h Finset.univ

@[simp] theorem waveDirectionalDerivative_X (z : σ → ℂ) (i : σ) :
    waveDirectionalDerivative z (X i) = C (z i) := by
  classical
  simp [waveDirectionalDerivative_apply, pderiv_X, Pi.single_apply,
    Algebra.smul_def]

@[simp] theorem waveDirectionalDerivative_C (z : σ → ℂ) (c : ℂ) :
    waveDirectionalDerivative z (C c) = 0 := by
  exact MvPolynomial.derivation_C _ _

def wavePrimitiveTerm (z : σ → ℂ) (ℓ : MvPolynomial σ ℂ) :
    ℕ → ℕ → MvPolynomial σ ℂ → MvPolynomial σ ℂ
  | 0, j, f => ((j + 1 : ℕ) : ℂ)⁻¹ • (ℓ ^ (j + 1) * f)
  | d + 1, j, f => ((j + 1 : ℕ) : ℂ)⁻¹ •
      (ℓ ^ (j + 1) * f - wavePrimitiveTerm z ℓ d (j + 1)
        (waveDirectionalDerivative z f))

def waveNormSq (z : σ → ℂ) : ℝ := ∑ i, Complex.normSq (z i)

def waveLinearCoordinate (z : σ → ℂ) : MvPolynomial σ ℂ :=
  ∑ i, (star (z i) / (waveNormSq z : ℂ)) • X i

end PolynomialWaves

section FiniteJets
open MvPolynomial
variable {σ R : Type*} [CommRing R]

def VanishTo (p : MvPolynomial σ R) (N : ℕ) : Prop :=
  ∀ m : σ →₀ ℕ, m.degree < N → p.coeff m = 0

variable [Fintype σ] [DecidableEq σ]

def waveQuadratic (G : σ → σ → MvPolynomial σ R) (u : σ → MvPolynomial σ R) :
    MvPolynomial σ R := ∑ i, ∑ j, G i j * u i * u j

end FiniteJets

section FiniteEikonal
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def eikonalResidual (G : σ → σ → MvPolynomial σ ℂ) (S : MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ := 1 + waveQuadratic G (fun i => pderiv i S)

end FiniteEikonal

section FiniteTransport
open MvPolynomial
variable {σ : Type*} [Fintype σ]

def waveTransport (A : σ → MvPolynomial σ ℂ) (B V : MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ := (∑ i, A i * pderiv i V) + B * V

end FiniteTransport
section QuadraticSeed
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def wavePhaseSeed (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) : MvPolynomial σ ℂ :=
  C c + (∑ i, C (z i) * X i) +
    (2 : ℂ)⁻¹ • (∑ i, ∑ j, C (Q i j) * X i * X j)

omit [DecidableEq σ] in
@[simp] theorem wavePhaseSeed_constantCoeff (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) :
    constantCoeff (wavePhaseSeed c z Q) = c := by
  simp [wavePhaseSeed]

@[simp] theorem wavePhaseSeed_gradient (c : ℂ) (z : σ → ℂ)
    (Q : σ → σ → ℂ) (k : σ) :
    constantCoeff (pderiv k (wavePhaseSeed c z Q)) = z k := by
  simp [wavePhaseSeed, Pi.single_apply, Finset.sum_add_distrib]

@[simp] theorem wavePhaseSeed_hessian (c : ℂ) (z : σ → ℂ)
    (Q : σ → σ → ℂ) (hQ : ∀ i j, Q i j = Q j i) (k l : σ) :
    constantCoeff (pderiv k (pderiv l (wavePhaseSeed c z Q))) = Q k l := by
  simp [wavePhaseSeed, Pi.single_apply, Finset.sum_add_distrib, hQ l k]
  ring

end QuadraticSeed

open MvPolynomial
variable {σ : Type*} [Fintype σ]

def wavePrimitive (z : σ → ℂ) (d : ℕ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  wavePrimitiveTerm z (waveLinearCoordinate z) d 0 p

def eikonalCorrection (G : σ → σ → MvPolynomial σ ℂ) (z : σ → ℂ)
    (N : ℕ) (S : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  wavePrimitive z N (-((2 : ℂ)⁻¹) • homogeneousComponent N (eikonalResidual G S))

variable [DecidableEq σ]

def eikonalIter (G : σ → σ → MvPolynomial σ ℂ) (z : σ → ℂ)
    (S₀ : MvPolynomial σ ℂ) : ℕ → MvPolynomial σ ℂ
  | 0 => S₀
  | k + 1 => eikonalIter G z S₀ k +
      eikonalCorrection G z (k + 2) (eikonalIter G z S₀ k)



end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section ActualEikonal
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem realPolyEval_at_zero (p : MvPolynomial σ ℂ) :
    realPolyEval p 0 = constantCoeff p := by
  simp [realPolyEval]

end ActualEikonal



end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ]

def boundedDegreeMonomials (N : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (σ:=σ) N).toFinset



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_TransportCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
namespace YauCounterexamples
variable {σ : Type*} [Fintype σ]

def transportCorrection (A : σ → MvPolynomial σ ℂ) (B V F : MvPolynomial σ ℂ)
    (z : σ → ℂ) (N : ℕ) : MvPolynomial σ ℂ :=
  wavePrimitive z N (-((2:ℂ)⁻¹) • homogeneousComponent N (waveTransport A B V + F))

def transportIter (A : σ → MvPolynomial σ ℂ) (B F : MvPolynomial σ ℂ)
    (z : σ → ℂ) (c : ℂ) : ℕ → MvPolynomial σ ℂ
  | 0 => C c
  | N+1 => transportIter A B F z c N +
      transportCorrection A B (transportIter A B F z c N) F z N

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_WaveDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

section WaveDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

def waveDeriv (v : E) (f : E → ℂ) (x : E) : ℂ := fderiv ℝ f x v

end WaveDifferentiation


end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PolynomialFiniteWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def smoothPolynomialLaplacian (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (P : MvPolynomial σ ℂ) : (σ → ℝ) → ℂ :=
  fun x => (∑ i, ∑ j, g i j x * realPolyEval (pderiv i (pderiv j P)) x) +
    ∑ i, b i x * realPolyEval (pderiv i P) x

def smoothPhaseTransportVector (g : σ → σ → (σ → ℝ) → ℂ)
    (S : MvPolynomial σ ℂ) (i : σ) : (σ → ℝ) → ℂ :=
  fun x => ∑ j, (g i j x + g j i x) * realPolyEval (pderiv j S) x

def smoothPhaseTransportScalar (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) : (σ → ℝ) → ℂ :=
  fun x => smoothPolynomialLaplacian g b S x + 2

def smoothTransportPolynomial (a : σ → (σ → ℝ) → ℂ)
    (b f : (σ → ℝ) → ℂ) (z : σ → ℂ) (c : ℂ) (N : ℕ) : MvPolynomial σ ℂ :=
  transportIter (fun i => realTaylorPolynomial (a i) N)
    (realTaylorPolynomial b N) (realTaylorPolynomial f N) z c N

def smoothPhasePolynomial (g : σ → σ → (σ → ℝ) → ℂ)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (L : ℕ) : MvPolynomial σ ℂ :=
  eikonalIter (fun i j => realTaylorPolynomial (g i j) L) z
    (wavePhaseSeed c z Q) (L - 2)

def smoothWaveAmplitudes (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (K J : ℕ) : ℕ → MvPolynomial σ ℂ
  | 0 => smoothTransportPolynomial (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S) 0 z 1 (K + J)
  | j + 1 => smoothTransportPolynomial (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S)
      (smoothPolynomialLaplacian g b (smoothWaveAmplitudes g b S z K J j)) z 0
      (K + J - (j + 1))



end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [TopologicalSpace X]

def formalPolynomialLaplacian (G : σ → σ → MvPolynomial σ ℂ)
    (B : σ → MvPolynomial σ ℂ) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  (∑ i, ∑ j, G i j * pderiv i (pderiv j P)) + ∑ i, B i * pderiv i P

def formalPhaseTransportVector (G : σ → σ → MvPolynomial σ ℂ)
    (S : MvPolynomial σ ℂ) (i : σ) : MvPolynomial σ ℂ :=
  ∑ j, (G i j + G j i) * pderiv j S

def formalPhaseTransportScalar (G : σ → σ → MvPolynomial σ ℂ)
    (B : σ → MvPolynomial σ ℂ) (S : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  formalPolynomialLaplacian G B S + 2

def symbolWaveAmplitudes (G : σ → σ → MvPolynomial σ ℂ)
    (B : σ → MvPolynomial σ ℂ) (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (K J : ℕ) : ℕ → MvPolynomial σ ℂ
  | 0 => transportIter (formalPhaseTransportVector G S) (formalPhaseTransportScalar G B S) 0 z 1 (K+J)
  | j+1 => transportIter (formalPhaseTransportVector G S) (formalPhaseTransportScalar G B S)
      (formalPolynomialLaplacian G B (symbolWaveAmplitudes G B S z K J j)) z 0 (K+J-(j+1))

def uniformSmoothWaveAmplitudes (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S : MvPolynomial σ ℂ) (z : σ → ℂ) (K J : ℕ) :=
  symbolWaveAmplitudes (fun i j => realTaylorPolynomial (g i j) (K+J))
    (fun i => realTaylorPolynomial (b i) (K+J)) S z K J


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PhaseFormMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def phaseProjection (z : ι → ℂ) : Matrix ι ι ℂ :=
  1 + vecMulVec z z


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
open Matrix Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexPhaseVector (a b : EuclideanSpace ℝ ι) : ι → ℂ :=
  fun i => (a i : ℂ) + Complex.I * (b i : ℂ)




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmoothFiniteWaveSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section UniformJetBounds
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def UniformJetBounds (f : X → E → ℂ) (K : Set X) (B : Set E) : Prop :=
  ∀ k : ℕ, ∃ C > 0, ∀ p ∈ K, ∀ x ∈ B, ‖iteratedFDeriv ℝ k (f p) x‖ ≤ C

end UniformJetBounds

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def smoothFiniteWave (S : E → ℂ) (V : ℕ → E → ℂ) (J : ℕ) (n : ℝ) (x : E) : ℂ :=
  Complex.exp ((n : ℂ)*S x) * ∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * V j x

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProfilePeriodizeEventuallyZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

theorem exists_radial_derivative {a b : ℝ} (hab : a < b) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Ioo a b ∧ (∀ t, β t ∈ Icc 0 1) ∧ β ((a+b)/2) = 1 := by
  obtain ⟨β,hsub,hcompact,hs,hr,hc⟩ := exists_contDiff_tsupport_subset
    (n:=⊤) (isOpen_Ioo.mem_nhds (show (a+b)/2 ∈ Ioo a b by constructor <;> linarith))
  exact ⟨β,hs,hcompact,hsub,fun t => hr (mem_range_self t),hc⟩


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_MetricGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI





noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def metricGradient (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    TangentSpace 𝓘(ℝ,E) x := by
  letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) :=
    show FiniteDimensional ℝ E from inferInstance
  exact (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,E) x)).symm
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def localMetricFlat (g : SmoothMetric E M) (p x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ,E)) (E →L[ℝ] ℝ)
    (fun x => TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) p x p x (g.inner x)

omit [FiniteDimensional ℝ E] in
lemma localMetricFlat_pairing (g : SmoothMetric E M) (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet) (v w : E) :
    localMetricFlat g p x v w = g.inner x
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm x v)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm x w) := by
  unfold localMetricFlat
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp

omit [FiniteDimensional ℝ E] in
lemma contMDiffAt_localMetricFlat (g : SmoothMetric E M) (p : M) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ (localMetricFlat g p) p := by
  have hg := g.contMDiff p
  rw [contMDiffAt_section p] at hg
  simp only [hom_trivializationAt_apply] at hg
  convert! hg using 1
  all_goals try with_reducible_and_instances rfl

end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance actualDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance actualDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ComplexPolarWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

def complexWaveJet (n : ℝ) (e : ℂ) (u : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) :
    (Fin 1 ⊕ Fin 3) → ℂ :=
  Sum.elim (fun _ => e⁻¹*u x)
    (fun i => (n : ℂ)⁻¹*e⁻¹*waveDeriv (Pi.single i 1) u x)


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ENNReal Matrix.Norms.Elementwise


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_GeneratedCutoffWaveEndpointRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

variable {I : Type*} [Fintype I]

def complexValueVector (z : I → ℂ) : EuclideanSpace ℝ (I ⊕ I) :=
  WithLp.toLp 2 (Sum.elim (fun i => (z i).re) (fun i => (z i).im))

end



open Set Filter
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ComplexGaussianRealValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
variable {I : Type*} [Fintype I]

def complexGaussianRealValue (z : I → ℂ) (γ : I → ℂ) : ℝ :=
  ∑ i, (γ i*z i).re


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ComplexGramTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped InnerProductSpace Matrix
namespace YauCounterexamples
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
def complexGramTrace (b : Basis ι ℝ E) (H : E → E → ℂ) : ℂ :=
  ∑ i, ∑ j, ((Matrix.gram ℝ b)⁻¹ i j : ℂ)*H (b i) (b j)
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ManifoldChartPush
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def manifoldChartPush (p : M) (f : E → V) : M → V :=
  (chartAt E p).source.indicator (f ∘ chartAt E p)

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma manifoldChartPush_support (p : M) (f : E → V) :
    Function.support (manifoldChartPush p f) ⊆ (chartAt E p).symm '' tsupport f := by
  intro x hx
  have hs : x ∈ (chartAt E p).source := by
    by_contra hh
    exact hx (by simp [manifoldChartPush, hh])
  refine ⟨chartAt E p x, subset_closure ?_, (chartAt E p).left_inv hs⟩
  simpa only [manifoldChartPush, Set.indicator_of_mem hs, Function.comp_apply,
    Function.mem_support] using hx

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma manifoldChartPush_tsupport (p : M) {f : E → V}
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt E p).target) :
    tsupport (manifoldChartPush p f) ⊆ (chartAt E p).symm '' tsupport f := by
  apply closure_minimal (manifoldChartPush_support p f)
  exact (hc.image_of_continuousOn ((chartAt E p).continuousOn_symm.mono hs)).isClosed

lemma contMDiff_manifoldChartPush (p : M) {f : E → V}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt E p).target) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ (manifoldChartPush p f) := by
  intro x
  by_cases hx : x ∈ (chartAt E p).source
  · have he : manifoldChartPush p f =ᶠ[𝓝 x] f ∘ chartAt E p := by
      filter_upwards [(chartAt E p).open_source.mem_nhds hx] with z hz
      exact Set.indicator_of_mem hz _
    apply ((contMDiff_iff_contDiff.mpr hf).contMDiffAt.comp x
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hx)).congr_of_eventuallyEq he
  · have hn : x ∉ (chartAt E p).symm '' tsupport f := by
      rintro ⟨y, hy, rfl⟩
      exact hx ((chartAt E p).map_target (hs hy))
    have ht : x ∉ tsupport (manifoldChartPush p f) :=
      fun h => hn (manifoldChartPush_tsupport p hc hs h)
    exact contMDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp ht)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
variable {n : ℕ}

section Planar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def planarLinear (a b : E) : E →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerSL ℝ a) + Complex.I • (Complex.ofRealCLM.comp (innerSL ℝ b))

end Planar



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_SymmLChartTrivialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance tensorTangentDualAdd (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  inferInstance
local instance tensorTangentDualSmul (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma symmL_chart_trivialization (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symmL ℝ ((chartAt E p).symm y) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y := by
  have h := TangentBundle.symmL_trivializationAt (I:=𝓘(ℝ,E)) ((chartAt E p).map_target hy)
  have h' : (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symmL ℝ ((chartAt E p).symm y) =
      (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm
        ((chartAt E p) ((chartAt E p).symm y))) := by
    simpa [extChartAt] using h
  exact h'.trans (congrArg (fun z : E => (show E →L[ℝ] E from
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm z)) ((chartAt E p).right_inv hy))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTensorCoordLocal1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Compacts E)
lemma compactSmooth_uniformity_countable : IsCountablyGenerated (uniformity 𝓓_{K}(E,F)) := by
  rw [← (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
    (𝕜:=ℝ) (n:=⊤) (K:=K) (F:=F)).toIsUniformInducing.comap_uniformity]
  infer_instance
lemma compactSmooth_t2 : T2Space 𝓓_{K}(E,F) := by
  let : MetricSpace (E →ᵇ (E [×0]→L[ℝ] F)) := inferInstance
  apply T2Space.of_injective_continuous
    (f := (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0 : 𝓓_{K}(E,F) → E →ᵇ (E [×0]→L[ℝ] F)))
  · exact ContDiffMapSupportedIn.structureMapCLM_zero_injective ℝ
  · exact (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0).continuous

@[instance_reducible] def compactSmoothMetricSpace : MetricSpace 𝓓_{K}(E,F) := by
  letI := compactSmooth_uniformity_countable (F:=F) K
  letI := compactSmooth_t2 (F:=F) K
  exact UniformSpace.metricSpace _

end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance instIsTopologicalAddGroupContinuousLinearMapRealIdTangentSpaceModelWithCornersSelf_solutions (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapId_solutions_1 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
section ChartTensorCoordinate
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance chartTensorCoordLocal1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal2 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end ChartTensorCoordinate

variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

local instance chartTensorCoordLocal9 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal10 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousCompactSmoothJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance hmsDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance


end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance compactSmoothContinuityInst1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance compactSmoothContinuityInst2 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RadialFiniteDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section


section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff

lemma circle_ball_round {s q ρ : ℝ} (h : (s : UnitAddCircle) ∈ ball (q : UnitAddCircle) ρ) :
    |s-q-(round (s-q) : ℝ)| < ρ := by
  simpa only [mem_ball,dist_eq_norm,←AddCircle.coe_sub,AddCircle.norm_eq,
    inv_one,one_mul,mul_one] using h

end


open Set Function Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ENNReal InnerProductSpace ContDiff

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_FixedRadialChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples

theorem exists_fixed_radial_constants (K S c : ℝ) (hc : 0 < c) :
    ∃ δ g₀ : ℝ, 0 < δ ∧ 0 < g₀ ∧ g₀ ≤ 1 ∧
      9216*K*S*δ^2 ≤ 1 ∧ g₀ = Real.sqrt (1+δ^2*c^2/16)-1 := by
  have h1 : Tendsto (fun δ : ℝ => 9216*K*S*δ^2) (𝓝 0) (𝓝 0) := by
    convert (show Continuous (fun δ : ℝ => 9216*K*S*δ^2) by fun_prop).tendsto 0 using 1; norm_num
  have h2 : Tendsto (fun δ : ℝ => δ^2*c^2/16) (𝓝 0) (𝓝 0) := by
    convert (show Continuous (fun δ : ℝ => δ^2*c^2/16) by fun_prop).tendsto 0 using 1; norm_num
  have hs : ∀ᶠ δ : ℝ in 𝓝 0, 9216*K*S*δ^2 < 1 ∧ δ^2*c^2/16 < 3 :=
    (h1.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))).and
      (h2.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 3)))
  have hs' : ∀ᶠ δ : ℝ in 𝓝[>] 0, 9216*K*S*δ^2 < 1 ∧ δ^2*c^2/16 < 3 :=
    hs.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hj : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ 9216*K*S*δ^2 < 1 ∧ δ^2*c^2/16 < 3 :=
    Filter.Eventually.and hpos hs'
  obtain ⟨δ,hδ,ha,hb⟩ := Filter.Eventually.exists hj
  have hp : 0 < δ^2*c^2/16 := by positivity
  have hgt : 1 < Real.sqrt (1+δ^2*c^2/16) := by
    have hh := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (show (1:ℝ) < 1+δ^2*c^2/16 by linarith)
    simpa using hh
  have hle : Real.sqrt (1+δ^2*c^2/16) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by nlinarith⟩
  exact ⟨δ,Real.sqrt (1+δ^2*c^2/16)-1,hδ,sub_pos.mpr hgt,by linarith,ha.le,rfl⟩
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_AnisotropicConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
namespace YauCounterexamples

variable (E F : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {E F}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma inverse_quadratic_hasTemperateGrowth {α : ℝ} (hα : 0 < α) :
    (fun x : E => (α + ‖x‖ ^ 2)⁻¹).HasTemperateGrowth := by
  have h : (fun x : E => α⁻¹ *
      (1 + ‖(Real.sqrt α)⁻¹ • x‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth := by
    exact (Function.HasTemperateGrowth.const (α⁻¹)).mul
      ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-1)).comp
        (((Real.sqrt α)⁻¹) • ContinuousLinearMap.id ℝ E).hasTemperateGrowth)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  have hn : ‖(Real.sqrt α)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / α := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hα.le]
    ring
  rw [hn, Real.rpow_neg_one]
  have hd : α + ‖x‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hd' : 1 + ‖x‖ ^ 2 / α ≠ 0 := ne_of_gt (by positivity)
  field_simp

end YauCounterexamples

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
open scoped Real

lemma halfResolvent_scalar_bound (α t : ℝ) (hα : 1 ≤ α) (ht : 0 ≤ t) :
    (1 + t) ^ (1 / 2 : ℝ) / (α + t) ≤ (Real.sqrt α)⁻¹ := by
  have hαp : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.2 hαp
  rw [← Real.sqrt_eq_rpow, div_le_iff₀ (by positivity : 0 < α + t),
    ← div_eq_inv_mul, le_div_iff₀ hs]
  have ha := Real.sq_sqrt hαp.le
  have ht' := Real.sq_sqrt (by positivity : 0 ≤ 1 + t)
  have hsq : (Real.sqrt (1 + t) * Real.sqrt α) ^ 2 ≤ (α + t) ^ 2 := by
    rw [mul_pow, ha, ht']
    nlinarith [sq_nonneg t, mul_nonneg hαp.le ht, mul_nonneg hαp.le (sub_nonneg.mpr hα)]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

end YauCounterexamples

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
open MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform ContDiff
variable {E G F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def anisotropicConstant (L : E ≃L[ℝ] G) : ℝ := max 1 (‖L.symm.toContinuousLinearMap‖ ^ 2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma anisotropic_norm_bound (L : E ≃L[ℝ] G) (x : E) :
    1 + ‖x‖ ^ 2 ≤ anisotropicConstant L * (1 + ‖L x‖ ^ 2) := by
  have hx : ‖x‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖L x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] using
      L.symm.toContinuousLinearMap.le_opNorm (L x)
  have hx2 := mul_self_le_mul_self (norm_nonneg x) hx
  have hC1 : 1 ≤ anisotropicConstant L := by
    unfold anisotropicConstant
    exact le_max_left 1 _
  have hCL : ‖L.symm.toContinuousLinearMap‖ ^ 2 ≤ anisotropicConstant L := le_max_right _ _
  have hb := mul_le_mul_of_nonneg_right hCL (sq_nonneg ‖L x‖)
  nlinarith

def anisotropicResolventSymbol (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖L x‖ ^ 2)))
    (by have hp : 0 < α := lt_of_lt_of_le zero_lt_one hα
        have hd : ∀ x : E, α + ‖L x‖ ^ 2 ≠ 0 := fun x => ne_of_gt (by positivity)
        fun_prop) (anisotropicConstant L) (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ (by positivity : 0 < α + ‖L x‖ ^ 2)).mpr
      exact (anisotropic_norm_bound L x).trans
        (mul_le_mul_of_nonneg_left (by linarith) ((show 0 ≤ anisotropicConstant L from le_trans zero_le_one (le_max_left 1 (‖L.symm.toContinuousLinearMap‖ ^ 2))))))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_anisotropicResolventSymbol_le (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) :
    ‖anisotropicResolventSymbol L α hα‖ ≤ anisotropicConstant L := by
  apply (BoundedContinuousFunction.norm_le ((show 0 ≤ anisotropicConstant L from le_trans zero_le_one (le_max_left 1 (‖L.symm.toContinuousLinearMap‖ ^ 2))))).mpr
  intro x
  change ‖Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖L x‖ ^ 2))‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (by positivity : 0 < α + ‖L x‖ ^ 2)).mpr
  exact (anisotropic_norm_bound L x).trans
    (mul_le_mul_of_nonneg_left (by linarith) ((show 0 ≤ anisotropicConstant L from le_trans zero_le_one (le_max_left 1 (‖L.symm.toContinuousLinearMap‖ ^ 2)))))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma anisotropic_half_scalar_bound (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) (x : E) :
    (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2) ≤
      anisotropicConstant L * (Real.sqrt α)⁻¹ := by
  have hC : 1 ≤ anisotropicConstant L := le_max_left _ _
  have hCp : 0 ≤ anisotropicConstant L := le_trans zero_le_one hC
  have hb := anisotropic_norm_bound L x
  have hs : Real.sqrt (1 + ‖x‖ ^ 2) ≤
      anisotropicConstant L * Real.sqrt (1 + ‖L x‖ ^ 2) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have hc2 : anisotropicConstant L ≤ anisotropicConstant L ^ 2 := by nlinarith
    exact hb.trans (mul_le_mul_of_nonneg_right hc2 (by positivity))
  rw [← Real.sqrt_eq_rpow]
  calc
    Real.sqrt (1 + ‖x‖ ^ 2) / (α + ‖L x‖ ^ 2) ≤
        (anisotropicConstant L * Real.sqrt (1 + ‖L x‖ ^ 2)) / (α + ‖L x‖ ^ 2) :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ = anisotropicConstant L * ((1 + ‖L x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2)) := by
      rw [Real.sqrt_eq_rpow, mul_div_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (halfResolvent_scalar_bound α _ hα (sq_nonneg _)) hCp

def anisotropicHalfResolventSymbol (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2)))
    (by
      have hh : (fun x : E => Complex.ofReal
          ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2))).HasTemperateGrowth := by
        simp only [div_eq_mul_inv]
        exact Complex.hasTemperateGrowth_ofReal.comp
          ((by fun_prop : (fun x : E => (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)).HasTemperateGrowth).mul
            ((inverse_quadratic_hasTemperateGrowth (E := G) (lt_of_lt_of_le zero_lt_one hα)).comp L.toContinuousLinearMap.hasTemperateGrowth))
      exact hh.1.continuous)
    (anisotropicConstant L * (Real.sqrt α)⁻¹) (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact anisotropic_half_scalar_bound L α hα x)

end YauCounterexamples

open Set Filter
open scoped SchwartzMap ContDiff Topology

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormIteratedFDerivScalarDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

def coordinateFlux (e : ι → E) (a : E → Matrix ι ι ℝ) (U : E → ℝ)
    (i : ι) (x : E) : ℝ :=
  ∑ j, a x i j * fderiv ℝ U x (e j)


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ConformalMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def conformalMetric (g : SmoothMetric E M) (b : M → ℝ)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (hpos : ∀ x, 0 < b x) : SmoothMetric E M where
  inner x := (b x) ^ 2 • g.inner x
  symm x v w := by change (b x) ^ 2 * g.inner x v w = (b x) ^ 2 * g.inner x w v; rw [g.symm]
  pos x v hv := mul_pos (sq_pos_of_pos (hpos x)) (g.pos x v hv)
  isVonNBounded x := by
    apply ((g.isVonNBounded x).image ((b x)⁻¹ •
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x))).subset
    intro v hv
    refine ⟨b x • v, ?_, ?_⟩
    · change (b x) ^ 2 * g.inner x v v < 1 at hv
      simpa only [Set.mem_ofPred_eq, map_smul, _root_.smul_apply,
        smul_eq_mul, pow_two, mul_assoc] using hv
    · simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
      exact inv_smul_smul₀ (ne_of_gt (hpos x)) v
  contMDiff := (hb.pow 2).smul_section g.contMDiff

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CoordinateMetricFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def coordinateMetricFlux (b : Module.Basis ι ℝ E) (G : E → Matrix ι ι ℝ)
    (u : E → ℝ) (x : E) (i : ι) : ℝ :=
  Real.sqrt (G x).det * ∑ j, (G x)⁻¹ i j * fderiv ℝ u x (b j)

def coordinateMetricLaplacian (b : Module.Basis ι ℝ E) (G : E → Matrix ι ι ℝ)
    (u : E → ℝ) (x : E) : ℝ :=
  (Real.sqrt (G x).det)⁻¹ * ∑ i, fderiv ℝ (fun y => coordinateMetricFlux b G u y i) x (b i)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ComplexRealResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal Topology Matrix.Norms.Elementwise
namespace YauCounterexamples

def complexRealResponse {ι : Type*} (J : Fin 3 → ι → ℂ) (γ : Fin 3 → ℂ) : ι → ℝ :=
  fun i => ∑ ℓ, (γ ℓ*J ℓ i).re

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_BilinearCoordinateMatrixPosDef
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix Manifold
open scoped Topology ContDiff
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def bilinearCoordinateMatrix (b : Module.Basis ι ℝ E) (T : E →L[ℝ] E →L[ℝ] ℝ) :
    Matrix ι ι ℝ := fun i j => T (b i) (b j)


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
section ComplexCoordinate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def complexCoordinateMetricLaplacian (b : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) (u : E → ℂ) (x : E) : ℂ :=
  ⟨coordinateMetricLaplacian b G (Complex.re ∘ u) x,
    coordinateMetricLaplacian b G (Complex.im ∘ u) x⟩

end ComplexCoordinate

end


open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

section JointPartialTime
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma contDiffAt_partial_time_deriv {f : ℝ × E → F} {t : ℝ} {y : E}
    (hf : ContDiffAt ℝ ∞ f (t,y)) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => deriv (fun r => f (r,z.2)) z.1) (t,y) := by
  have hh : ContDiffAt ℝ ∞ (fun w : (ℝ × E) × ℝ => f (w.2,w.1.2)) ((t,y),t) := by
    simpa only [Function.comp_def] using hf.comp ((t,y),t)
      (show ContDiffAt ℝ ∞ (fun w : (ℝ × E) × ℝ => (w.2,w.1.2)) ((t,y),t) from
        contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact (hh.fderiv contDiffAt_fst (by simp)).clm_apply contDiffAt_const
end JointPartialTime

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundMetricExists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
section Pullback
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def pullbackInner {T : Type*} [AddCommGroup T] [Module ℝ T] [TopologicalSpace T]
    (D : T →L[ℝ] F) : T →L[ℝ] T →L[ℝ] ℝ :=
  (D.precomp ℝ).comp ((innerSL ℝ).comp D)

omit [FiniteDimensional ℝ E] in
@[simp] theorem pullbackInner_apply (D : E →L[ℝ] F) (v w : E) :
    pullbackInner D v w = inner ℝ (D v) (D w) := rfl

theorem pullbackInner_bounded (D : E →L[ℝ] F) (hD : Function.Injective D) :
    Bornology.IsVonNBounded ℝ {v : E | pullbackInner D v v < 1} := by
  obtain ⟨K, _, hK⟩ := D.toLinearMap.injective_iff_antilipschitz.mp hD
  rw [NormedSpace.isVonNBounded_iff ℝ]
  apply (hK.isBounded_preimage (Metric.isBounded_ball (x := (0 : F)) (r := 1))).subset
  intro v hv
  change dist (D v) 0 < 1
  rw [dist_zero_right]
  rw [← sq_lt_one_iff₀ (norm_nonneg (D v)), ← real_inner_self_eq_norm_sq]
  exact hv

omit [FiniteDimensional ℝ E] in
theorem contMDiff_pullbackInner (f : M → F)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        (pullbackInner (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))) := by
  intro x₀
  rw [contMDiffAt_section x₀]
  have hd := (hf x₀).mfderiv_const (m := ∞) (by simp)
  let L : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞
      (fun _ : M => L) x₀ := contMDiffAt_const
  have h := hd.clm_precomp (F₃ := ℝ) |>.clm_comp (hc.clm_comp hd)
  apply h.congr_of_eventuallyEq
  have hn := (trivializationAt (E →L[ℝ] ℝ)
      (fun x => TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt (E →L[ℝ] ℝ) _ x₀)
  filter_upwards [hn] with x hx
  ext v w
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.comp_apply]
  simp [pullbackInner, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, TangentBundle.continuousLinearMapAt_model_space]
  rw [Trivialization.coe_linearMapAt_of_mem _ hx]
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
  rfl

end Pullback


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_AnnularRelativeMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
variable {d : ℕ}

def ambientPowerGradient (a b : Euclidean (d+1)) (k : ℕ) (x : Euclidean (d+1)) : Euclidean (d+1) :=
  (k:ℝ) • (((planarLinear a b x)^(k-1)).re • a - ((planarLinear a b x)^(k-1)).im • b)


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ChartTensorNeighborhoodInst1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance chartTensorNeighborhoodInst1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartTensorNeighborhoodInst2 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BundleMetricInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def bundleMetricInner (g : SmoothMetric E M)
    (D : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ :=
  ((D x).precomp ℝ).comp ((g.inner x).comp (D x))

omit [FiniteDimensional ℝ E] in
lemma bundleMetricInner_apply (g : SmoothMetric E M)
    (D : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    bundleMetricInner g D x v w = g.inner x (D x v) (D x w) := rfl

omit [FiniteDimensional ℝ E] in
lemma bundleMetricInner_smooth (g : SmoothMetric E M)
    (D : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hD : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (D x))) :
    ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (bundleMetricInner g D x)) := by
  intro x₀
  have hd := hD x₀
  have hg := g.contMDiff x₀
  rw [contMDiffAt_section x₀] at hd hg ⊢
  have hh := hd.clm_precomp (F₃ := ℝ) |>.clm_comp (hg.clm_comp hd)
  apply hh.congr_of_eventuallyEq
  have hn := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  filter_upwards [hn] with x hx
  ext v w
  simp only [hom_trivializationAt_apply,ContinuousLinearMap.comp_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  rw [ContinuousLinearMap.inCoordinates_eq hx hx]
  simp only [ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp [bundleMetricInner_apply,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply,
    Trivialization.symm_apply_apply_mk _ hx]

def bundlePullbackMetric (g : SmoothMetric E M)
    (D : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hD : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (D x)))
    (hi : ∀ x, Function.Injective (D x)) : SmoothMetric E M where
  inner := bundleMetricInner g D
  symm x v w := g.symm x (D x v) (D x w)
  pos x v hv := g.pos x (D x v) (fun hz => hv (hi x (by simpa using hz)))
  isVonNBounded x := by
    change Bornology.IsVonNBounded ℝ {v : E | g.inner x (D x v) (D x v) < 1}
    have hd : Function.Injective (show E →L[ℝ] E from D x) := hi x
    obtain ⟨K,_,hK⟩ := (show E →L[ℝ] E from D x).toLinearMap.injective_iff_antilipschitz.mp hd
    rw [NormedSpace.isVonNBounded_iff ℝ]
    have hb := (NormedSpace.isVonNBounded_iff ℝ).mp (show Bornology.IsVonNBounded ℝ
      {v : E | g.inner x v v < 1} from g.isVonNBounded x)
    exact hK.isBounded_preimage hb
  contMDiff := bundleMetricInner_smooth g D hD

def bundleExp (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (x : M) : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  show E →L[ℝ] E from NormedSpace.exp (show E →L[ℝ] E from K x)

lemma bundleExp_coordinates (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (x₀ x : M) (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x₀).baseSet) :
    ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ,E)) E
      (TangentSpace 𝓘(ℝ,E)) x₀ x x₀ x (bundleExp K x) = NormedSpace.exp
      (ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ,E)) E
        (TangentSpace 𝓘(ℝ,E)) x₀ x x₀ x (K x)) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  let e : E ≃L[ℝ] E := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x₀).continuousLinearEquivAt ℝ x hx
  have hh := NormedSpace.map_exp e.conjContinuousAlgEquiv
    (e.arrowCongr e).continuous (show E →L[ℝ] E from K x)
  simp only [bundleExp]
  erw [ContinuousLinearMap.inCoordinates_eq hx hx, ContinuousLinearMap.inCoordinates_eq hx hx]
  convert hh using 1 <;> rfl

lemma bundleExp_smooth (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) :
    ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (bundleExp K x)) := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
    (show AnalyticOnNhd ℝ NormedSpace.exp Set.univ from
      fun x _ => NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiff
  intro x₀
  have hk := hK x₀
  rw [contMDiffAt_section x₀] at hk ⊢
  have hh := he.contMDiff.contMDiffAt.comp x₀ hk
  apply hh.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)] with x hx
  simp only [Function.comp_def,hom_trivializationAt_apply]
  exact bundleExp_coordinates K x₀ x hx

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma bundleExp_injective (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (x : M) : Function.Injective (bundleExp K x) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp (NormedSpace.isUnit_exp
    (show E →L[ℝ] E from K x))).1

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PinnedMetricJointGradientPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma contMDiffAt_smul_along {f : D → M}
    (K : ∀ z, TangentSpace 𝓘(ℝ,E) (f z) →L[ℝ] TangentSpace 𝓘(ℝ,E) (f z)) {z₀ : D}
    (hk : ContMDiffAt 𝓘(ℝ,D) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun z => (⟨f z, K z⟩ : TotalSpace (E →L[ℝ] E)
        (fun x : M => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x))) z₀)
    {a : D → ℝ} (ha : ContMDiffAt 𝓘(ℝ,D) 𝓘(ℝ,ℝ) ∞ a z₀) :
    ContMDiffAt 𝓘(ℝ,D) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun z => (⟨f z, a z • K z⟩ : TotalSpace (E →L[ℝ] E)
        (fun x : M => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x))) z₀ := by
  rw [contMDiffAt_totalSpace] at hk ⊢
  refine ⟨hk.1, (ha.smul hk.2).congr_of_eventuallyEq ?_⟩
  have hn := (trivializationAt (E →L[ℝ] E)
    (fun x => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) (f z₀)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ (f z₀))
  filter_upwards [hk.1.continuousAt.preimage_mem_nhds hn] with z hz
  change f z ∈ (trivializationAt (E →L[ℝ] E)
    (fun x => TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) (f z₀)).baseSet at hz
  exact (Trivialization.linear ℝ _ hz).2 _ _

end


section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def chartTangentBasis (p : M) (y : E) (hy : y ∈ (chartAt E p).target) :
    Module.Basis (CoordIndex E) ℝ E := by
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y
  have he : (chartAt E p).MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) :=
    ⟨(contMDiffOn_chart (I := 𝓘(ℝ,E)) (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart_symm (I := 𝓘(ℝ,E)) (n := ∞)).mdifferentiableOn (by simp)⟩
  have hi : Function.Bijective D := he.symm.mfderiv_bijective hy
  exact (Module.finBasis ℝ E).map (LinearEquiv.ofBijective D.toLinearMap hi)


end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff Matrix BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BundleRankOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def bundleRankOne (g : SmoothMetric E M) (V : ∀ x : M, TangentSpace 𝓘(ℝ,E) x) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  (g.inner x (V x)).smulRight (V x)

def bundleTransverse (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  ContinuousLinearMap.id ℝ _ -
    (g.inner x (metricGradient g u x) (metricGradient g u x))⁻¹ •
      bundleRankOne g (metricGradient g u) x

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactSmoothJetMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Compacts E)

def compactSmoothJetMap : 𝓓_{K}(E,F) →L[ℝ] ((m : ℕ) → E →ᵇ (E [×m]→L[ℝ] F)) :=
  ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤)



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_TorusAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E F A B M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
def productImmersion (f : M → A) (g : N → B) (x : M×N) : WithLp 2 (A×B) :=
  WithLp.toLp 2 (f x.1,g x.2)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma productImmersion_smooth {f : M → A} {g : N → B}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,B) ∞ g) :
    ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,WithLp 2 (A×B)) ∞ (productImmersion f g) := by
  have h : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,A×B) ∞
      (fun x : M×N => (f x.1,g x.2)) :=
    ((hf.comp contMDiff_fst).prodMk_space (hg.comp contMDiff_snd))
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.contDiff.contMDiff.comp
    h)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma productImmersion_derivative {f : M → A} {g : N → B}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,B) ∞ g) (x : M×N) :
    mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,WithLp 2 (A×B)) (productImmersion f g) x =
      (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap.comp
        ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) f x.1).prodMap
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,B) g x.2)) := by
  let L := (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap
  have hp : HasMFDerivAt (𝓘(ℝ,E).prod 𝓘(ℝ,F)) (𝓘(ℝ,A).prod 𝓘(ℝ,B))
      (fun x : M×N => (f x.1,g x.2)) x
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) f x.1).prodMap
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,B) g x.2)) :=
    ((hf.mdifferentiable (by simp) x.1).hasMFDerivAt.prodMap
      (hg.mdifferentiable (by simp) x.2).hasMFDerivAt)
  have hp' : HasMFDerivAt (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,A×B)
      (fun x : M×N => (f x.1,g x.2)) x
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) f x.1).prodMap
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,B) g x.2)) := by
    rw [modelWithCornersSelf_prod, ←chartedSpaceSelf_prod]
    exact hp
  exact ((L.hasFDerivAt.hasMFDerivAt).comp x hp').mfderiv

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma productImmersion_injective_derivative {f : M → A} {g : N → B}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,B) ∞ g)
    (hfi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) f x))
    (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,B) g x)) (x : M×N) :
    Function.Injective (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,F)) 𝓘(ℝ,WithLp 2 (A×B)) (productImmersion f g) x) := by
  rw [productImmersion_derivative hf hg]
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.injective.comp
    (Prod.map_injective.mpr ⟨hfi x.1,hgi x.2⟩)

end


open Set Filter Manifold Bundle
open scoped Topology ContDiff

lemma circle_immersion_smooth :
    ContMDiff 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,ℂ) ∞ (fun x : Circle => (x : ℂ)) := by
  let : Fact (Module.finrank ℝ ℂ = 1+1) := ⟨by simp⟩
  exact contMDiff_coe_sphere

lemma circle_immersion_injective (x : Circle) :
    Function.Injective (mfderiv 𝓘(ℝ,Euclidean 1) 𝓘(ℝ,ℂ) (fun x : Circle => (x : ℂ)) x) := by
  let : Fact (Module.finrank ℝ ℂ = 1+1) := ⟨by simp⟩
  exact injective_mvfderiv_subtypeVal_sphere x

lemma sphere_two_immersion_smooth :
    ContMDiff 𝓘(ℝ,Euclidean 2) 𝓘(ℝ,Euclidean 3) ∞ (fun x : Sphere 2 => (x : Euclidean 3)) := by
  let : Fact (Module.finrank ℝ (Euclidean 3) = 2+1) := ⟨by simp [Euclidean]⟩
  exact contMDiff_coe_sphere

lemma sphere_two_immersion_injective (x : Sphere 2) :
    Function.Injective (mfderiv 𝓘(ℝ,Euclidean 2) 𝓘(ℝ,Euclidean 3)
      (fun x : Sphere 2 => (x : Euclidean 3)) x) := by
  let : Fact (Module.finrank ℝ (Euclidean 3) = 2+1) := ⟨by simp [Euclidean]⟩
  exact injective_mvfderiv_subtypeVal_sphere x


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_BilinearTransverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def bilinearTransverse (G : E →L[ℝ] E →L[ℝ] ℝ) (a : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (G a a)⁻¹ • (G a).smulRight a
def bilinearPinning (G : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) : E →L[ℝ] E :=
  let p := bilinearTransverse G a b
  (G p).smulRight p - (G p p / 2) • bilinearTransverse G a
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
abbrev ThreeManifold := Sphere 2 × Circle
abbrev ThreeProductModel := Euclidean 2 × Euclidean 1
abbrev ThreeModel := WithLp 2 ThreeProductModel
abbrev ThreeAmbient := WithLp 2 (Euclidean 3 × ℂ)
instance threeProductChartedSpace : ChartedSpace ThreeProductModel ThreeManifold :=
  prodChartedSpace (Euclidean 2) (Sphere 2) (Euclidean 1) Circle
instance threeProductIsManifold : IsManifold 𝓘(ℝ,ThreeProductModel) ∞ ThreeManifold := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (Sphere 2) Circle
abbrev threeModelEquiv : ThreeProductModel ≃L[ℝ] ThreeModel :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Euclidean 2) (Euclidean 1)).symm
instance threeChartedSpace : ChartedSpace ThreeModel ThreeManifold :=
  reModelChartedSpace threeModelEquiv
instance threeIsManifold : IsManifold 𝓘(ℝ,ThreeModel) ∞ ThreeManifold :=
  reModel_isManifold threeModelEquiv

def threeImmersion : ThreeManifold → ThreeAmbient :=
  productImmersion (fun x : Sphere 2 => (x : Euclidean 3)) (fun z : Circle => (z : ℂ))
lemma threeImmersion_product_smooth :
    ContMDiff 𝓘(ℝ,ThreeProductModel) 𝓘(ℝ,ThreeAmbient) ∞ threeImmersion := by
  rw [modelWithCornersSelf_prod]
  exact productImmersion_smooth sphere_two_immersion_smooth circle_immersion_smooth
lemma threeImmersion_smooth : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) ∞ threeImmersion :=
  contMDiff_reModel_source threeModelEquiv threeImmersion_product_smooth
lemma threeImmersion_injective (x : ThreeManifold) :
    Function.Injective (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion x) := by
  rw [mfderiv_reModel_source threeModelEquiv threeImmersion_product_smooth]
  change Function.Injective ((mfderiv 𝓘(ℝ,ThreeProductModel) 𝓘(ℝ,ThreeAmbient) threeImmersion x : ThreeProductModel → ThreeAmbient) ∘ (threeModelEquiv.symm : ThreeModel → ThreeProductModel))
  apply Function.Injective.comp
  · rw [modelWithCornersSelf_prod]
    exact productImmersion_injective_derivative sphere_two_immersion_smooth circle_immersion_smooth
      sphere_two_immersion_injective circle_immersion_injective x
  · exact threeModelEquiv.symm.injective

lemma threeModel_finrank : Module.finrank ℝ ThreeModel = 3 := by
  rw [(threeModelEquiv.symm.toLinearEquiv).finrank_eq]
  simp [ThreeProductModel,Euclidean]
end


section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
instance circle_dimension_fact : Fact (Module.finrank ℝ ℂ = 1+1) := ⟨by simp⟩
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
def fourToCircle (q : FourManifold) : Circle := q.2.2

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ThreeCoupledNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
abbrev productAxis (i : Fin 3) : Euclidean 3 := EuclideanSpace.single i 1
def productA (x : Euclidean 3) : ℂ := planarLinear (productAxis 0) (productAxis 1) x
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace

def threeProfilePoint : Sphere 2 :=
  ⟨(WithLp.toLp 2 ![(3/5:ℝ),0,4/5] : Euclidean 3), by
    rw [Metric.mem_sphere,dist_zero_right]
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)
      (WithLp.toLp 2 ![(3/5:ℝ),0,4/5] : Euclidean 3)
    norm_num [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs] at h
    rcases h with h | h
    · exact h
    · nlinarith [norm_nonneg (WithLp.toLp 2 ![(3/5:ℝ),0,4/5] : Euclidean 3)]⟩
def threeProfileCenter : ThreeManifold := (threeProfilePoint,1)
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
local instance threeTransportContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal
def ThreeRegular (u : ThreeManifold → ℝ) : Prop :=
  ∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt ThreeModel q).symm) (chartAt ThreeModel q q)≠0
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end


