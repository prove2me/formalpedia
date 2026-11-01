-- Prove2me | Definitions.Def_OAIQ075A005
-- name    : OAIQ075A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T07:56:36.65461+00:00
-- url     : https://prove2.me/theorems/fb120b17-ad9f-4f3e-8d21-f310e81490b3
-- title:
--   Definitions bundle OAIQ075A005 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 252 declarations of OpenAI's Lean: 102 definitions, 5 inductive types or structures, 8 instances and 137 theorems. The definitions and types are `OAI.KadisonSimilarity.CentralProjection`, `OAI.KadisonSimilarity.CountableCopies`, `OAI.KadisonSimilarity.CycleConstantLabelings`, `OAI.KadisonSimilarity.CycleMembers`, `OAI.KadisonSimilarity.CyclicStarRepresentation`, `OAI.KadisonSimilarity.DihedralCornerWords.alternatingProduct`, `OAI.KadisonSimilarity.DihedralCornerWords.blockLetters`, `OAI.KadisonSimilarity.DihedralCornerWords.pairLetters`, `OAI.KadisonSimilarity.DihedralCornerWords.positiveCornerPowers`, `OAI.KadisonSimilarity.DihedralCornerWords.productLetters`, `OAI.KadisonSimilarity.DihedralWordAlgebra.spanStarAlgebra`, `OAI.KadisonSimilarity.DihedralWordAlgebra.wordSet`, `OAI.KadisonSimilarity.EndpointLetters`, `OAI.KadisonSimilarity.EndpointPairing`, `OAI.KadisonSimilarity.FiniteMatrixFactorModel`, `OAI.KadisonSimilarity.FiniteOrthogonalColumns`, `OAI.KadisonSimilarity.HasInternalIsometryRows`, `OAI.KadisonSimilarity.HasNormalGNS`, `OAI.KadisonSimilarity.IsCrossPairing`, `OAI.KadisonSimilarity.IsOperatorForm`, `OAI.KadisonSimilarity.IsSourcePairClass`, `OAI.KadisonSimilarity.IsTestPairClass`, `OAI.KadisonSimilarity.LittleGrothendieckInput`, `OAI.KadisonSimilarity.MatchingRepresentatives`, `OAI.KadisonSimilarity.OrthogonalSummandDecomposition`, `OAI.KadisonSimilarity.PerfectMatching`, `OAI.KadisonSimilarity.PermutationCycles`, `OAI.KadisonSimilarity.RealTracialSequence`, `OAI.KadisonSimilarity.ScalarHilbertCoordinates`, `OAI.KadisonSimilarity.SchurWeylMultilinearSpanning`, `OAI.KadisonSimilarity.SeparableTwoVectorKaplanskyInput`, `OAI.KadisonSimilarity.SeparableUniformCommutatorEstimate`, `OAI.KadisonSimilarity.SourcePairClasses`, `OAI.KadisonSimilarity.SpectralProjectionRoundingInput`, `OAI.KadisonSimilarity.SpectralStepApproximation`, `OAI.KadisonSimilarity.TestPairClasses`, `OAI.KadisonSimilarity.TracialCommutationInput`, `OAI.KadisonSimilarity.TracialRightAction`, `OAI.KadisonSimilarity.TracialRightSupportInput`, `OAI.KadisonSimilarity.TwoVectorKaplanskyInput` and 67 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonSimilarity_Derivation_CommonCyclicEmbedding`, `KadisonSimilarity_Derivation_CyclicApproximation`, `KadisonSimilarity_Derivation_CyclicCommutativeModel`, `KadisonSimilarity_Derivation_CyclicSpectralIsometry`, `KadisonSimilarity_Derivation_CyclicSummandColumns`, `KadisonSimilarity_Derivation_DiagonalMatrixNorm`, `KadisonSimilarity_Derivation_DicksonRow`, `KadisonSimilarity_Derivation_TracialCornerCyclicity`, `KadisonSimilarity_FreeProduct_DihedralCornerDensity`, `KadisonSimilarity_FreeProduct_DihedralCornerWords`, `KadisonSimilarity_FreeProduct_DihedralWordAlgebra`, `KadisonSimilarity_FreeProduct_FreeMatrixExtension`, `KadisonSimilarity_FreeProduct_GeneratedCompression`, `KadisonSimilarity_FreeProduct_TracialCompression`, `KadisonSimilarity_FreeProduct_TracialPropagationEndgame`, `KadisonSimilarity_FreeProduct_WordPrefixRealization`, `KadisonSimilarity_Representation_AEColumnOperator`, `KadisonSimilarity_Representation_AmplifiedNormalRange`, `KadisonSimilarity_Representation_CentralDecomposition`, `KadisonSimilarity_Representation_CentralSymmetrization`, `KadisonSimilarity_Representation_CommonSpectralMeasure`, `KadisonSimilarity_Representation_CompressedBicommutant`, `KadisonSimilarity_Representation_ConcretePredualRestriction`, `KadisonSimilarity_Representation_ContinuousL2Multiplication`, `KadisonSimilarity_Representation_ConullFieldExtension`, `KadisonSimilarity_Representation_CountableAmplification`, `KadisonSimilarity_Representation_CountableLpSubsequence`, `KadisonSimilarity_Representation_DecomposableColumns`, `KadisonSimilarity_Representation_DenseLinearOperator`, `KadisonSimilarity_Representation_DiagonalFieldAlgebra`, `KadisonSimilarity_Representation_FactorAssembly`, `KadisonSimilarity_Representation_FieldWeakClosure`, `KadisonSimilarity_Representation_IntertwinerExtension`, `KadisonSimilarity_Representation_KaplanskySelfAdjoint`, `KadisonSimilarity_Representation_KaplanskyStrongSequence`, `KadisonSimilarity_Representation_KaplanskyTransform`, `KadisonSimilarity_Representation_L2HilbertSum`, `KadisonSimilarity_Representation_L2Localization`, `KadisonSimilarity_Representation_LocalizedL2Bound`, `KadisonSimilarity_Representation_NonseparableReduction`, `KadisonSimilarity_Representation_NonunitalRangeRepresentation`, `KadisonSimilarity_Representation_NormalFactorGeneration`, `KadisonSimilarity_Representation_ProjectionFieldReduction`, `KadisonSimilarity_Representation_ProperlyInfiniteEstimate`, `KadisonSimilarity_Representation_ScalarKaplansky`, `KadisonSimilarity_Representation_SelfAdjointStrongDensity`, `KadisonSimilarity_Representation_SeparableContractionTests`, `KadisonSimilarity_Representation_SpectralIntertwining`, `KadisonSimilarity_Representation_SpectralRoundingDischarge`, `KadisonSimilarity_Representation_SpectralStepDischarge`, `KadisonSimilarity_Representation_SpectralSteps`, `KadisonSimilarity_Representation_UnitalizedExtension`, `KadisonSimilarity_Representation_UnitaryNormalRange`, `KadisonSimilarity_Representation_UnitizationProjection`, `KadisonSimilarity_Representation_VectorL2Multiplication`, `KadisonSimilarity_Representation_VectorL2Representation`, `KadisonSimilarity_Representation_VectorSpectralMeasure`, `KadisonSimilarity_Representation_WeakOperatorCompactness`, `KadisonSimilarity_Representation_WeakOperatorIntegral`, `KadisonSimilarity_Representation_WeakOperatorLimits`, `KadisonSimilarity_Tensor_EndpointDensity`, `KadisonSimilarity_Tensor_EndpointPairings`, `KadisonSimilarity_Tensor_InvariantCycles`, `KadisonSimilarity_Tensor_InvariantTensors`, `KadisonSimilarity_Tensor_PairingLabels`, `KadisonSimilarity_Tracial_CofinalMatrixTowers`, `KadisonSimilarity_Tracial_ConcreteGNSNormality`, `KadisonSimilarity_Tracial_ConjugateMomentCriterion`, `KadisonSimilarity_Tracial_FullColumnTheorem`, `KadisonSimilarity_Tracial_IntegerMomentScaling`, `KadisonSimilarity_Tracial_MatrixArrayFlattening`, `KadisonSimilarity_Tracial_MatrixCornerFrames`, `KadisonSimilarity_Tracial_MatrixDiagonalEmbedding`, `KadisonSimilarity_Tracial_MatrixRelativeCommutant`, `KadisonSimilarity_Tracial_MatrixSubfactorTransfer`, `KadisonSimilarity_Tracial_MatrixTraceUniqueness`, `KadisonSimilarity_Tracial_MatrixUnitCoordinates`, `KadisonSimilarity_Tracial_MatrixVonNeumannRange`, `KadisonSimilarity_Tracial_TracialInputTransport`, `KadisonSimilarity_Tracial_TracialMatrixCovariance`, `KadisonSimilarity_Tracial_TracialMatrixRealization`, `KadisonSimilarity_Tracial_TracialMatrixTower`, `KadisonSimilarity_Tracial_TracialProjectionLifting`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A010`, `OAIQ075A011` and `OAIQ075A012`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity

section
-- module Solutions.OAIQ075_KS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_VectorSpectralMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar spectral measure of a vector in a representation of C(X). -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace KadisonSimilarity.VectorSpectralMeasure
variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
def realCM (f : C(X,ℝ)) : C(X,ℂ) := ⟨fun x => (f x : ℂ),by fun_prop⟩
@[simp] lemma realCM_apply (f : C(X,ℝ)) (x : X) : realCM f x = (f x : ℂ) := rfl
@[simp] lemma realCM_add (f g : C(X,ℝ)) : realCM (f+g) = realCM f+realCM g := by ext; simp
@[simp] lemma realCM_sub (f g : C(X,ℝ)) : realCM (f-g) = realCM f-realCM g := by ext; simp
@[simp] lemma realCM_smul (c : ℝ) (f : C(X,ℝ)) : realCM (c • f) = (c:ℂ) • realCM f := by ext; simp
@[simp] lemma realCM_one : realCM (1:C(X,ℝ)) = 1 := by ext; simp
variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma real_nonneg (f : C(X,ℝ)) (hf : 0 ≤ f) : 0 ≤ (⟪v, Φ (realCM f) v⟫_ℂ).re := by
  let g : C(X,ℂ) := realCM ⟨fun x => Real.sqrt (f x),by fun_prop⟩
  have he : star g * g = realCM f := by
    ext x
    simp only [ContinuousMap.mul_apply,ContinuousMap.star_apply,realCM_apply,g,ContinuousMap.coe_mk,Complex.star_def,Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    exact congrArg Complex.ofReal (Real.mul_self_sqrt (show 0 ≤ f x from hf x))
  rw [← he,map_mul,map_star]
  change 0 ≤ (⟪v, (star (Φ g)) ((Φ g) v)⟫_ℂ).re
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (x := (Φ g) v)

def functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := (⟪v,Φ (realCM f.toContinuousMap) v⟫_ℂ).re
  map_add' f g := by
    change (⟪v,Φ (realCM (f.toContinuousMap+g.toContinuousMap)) v⟫_ℂ).re = _
    simp [inner_add_right]
  map_smul' c f := by
    change (⟪v,Φ (realCM (c • f.toContinuousMap)) v⟫_ℂ).re = c * _
    rw [realCM_smul,map_smul]
    simp only [FunLike.coe_smul,Pi.smul_apply,inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  monotone' f g hfg := by
    have he := real_nonneg Φ v (g.toContinuousMap-f.toContinuousMap) (sub_nonneg.mpr hfg)
    simpa [inner_sub_right] using he

def measure : Measure X := RealRMK.rieszMeasure (functional Φ v)
instance instIsFiniteMeasureMeasure : IsFiniteMeasure (measure Φ v) := by dsimp [measure]; infer_instance
instance instRegularMeasure : (measure Φ v).Regular := by dsimp [measure]; infer_instance
lemma integral_real (f : C(X,ℝ)) : ∫ x, f x ∂measure Φ v = (⟪v,Φ (realCM f) v⟫_ℂ).re := by
  exact RealRMK.integral_rieszMeasure (functional Φ v) (CompactlySupportedContinuousMap.continuousMapEquiv f)
lemma integral_complex (f : C(X,ℂ)) : ∫ x, f x ∂measure Φ v = ⟪v,Φ f v⟫_ℂ := by
  let fr : C(X,ℝ) := ⟨fun x => (f x).re,by fun_prop⟩
  let fi : C(X,ℝ) := ⟨fun x => (f x).im,by fun_prop⟩
  have he : f = realCM fr + Complex.I • realCM fi := by
    ext x
    simpa [fr,fi,smul_eq_mul,mul_comm] using (Complex.re_add_im (f x)).symm
  have hi_real (g : C(X,ℝ)) : (⟪v,Φ (realCM g) v⟫_ℂ).im = 0 := by
    have hs : star (Φ (realCM g)) = Φ (realCM g) := by
      rw [← map_star]; congr 1; ext x; simp
    have ht := inner_conj_symm (𝕜 := ℂ) v (Φ (realCM g) v)
    rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,hs] at ht
    have hh := congrArg Complex.im ht
    simp only [Complex.conj_im] at hh
    linarith
  have hb (g : C(X,ℝ)) : ∫ x, (g x : ℂ) ∂measure Φ v = ⟪v,Φ (realCM g) v⟫_ℂ := by
    rw [integral_complex_ofReal,integral_real]
    exact Complex.ext (by simp) (by simp [hi_real])
  rw [he,map_add,map_smul]
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,realCM_apply,add_apply,
    smul_apply,inner_add_right,inner_smul_right]
  have hir : Integrable (fun x => (fr x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fr.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hii : Integrable (fun x => (fi x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fi.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = (∫ x, (fr x : ℂ) ∂measure Φ v) +
        (∫ x, Complex.I • (fi x : ℂ) ∂measure Φ v) := integral_add hir (hii.smul Complex.I)
    _ = _ := by rw [integral_smul,hb,hb]; rfl
end KadisonSimilarity.VectorSpectralMeasure

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicSpectralIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cyclic spectral isometry gives scalar L² coordinates for the closed
cyclic orbit, as required for central cyclic decomposition. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace KadisonSimilarity.VectorSpectralMeasure
variable {X H : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
lemma inner_toLp (f g : C(X,ℂ)) :
    ⟪ContinuousMap.toLp 2 (measure Φ v) ℂ f, ContinuousMap.toLp 2 (measure Φ v) ℂ g⟫_ℂ =
      ⟪Φ f v,Φ g v⟫_ℂ := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, (star f*g) x ∂measure Φ v := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (μ := measure Φ v) (p := 2) (𝕜 := ℂ) f,
        ContinuousMap.coeFn_toLp (μ := measure Φ v) (p := 2) (𝕜 := ℂ) g] with x hx hy
      simp only [hx,hy,RCLike.inner_apply,ContinuousMap.mul_apply,ContinuousMap.star_apply,Complex.star_def]
      ring
    _ = ⟪v,Φ (star f*g) v⟫_ℂ := integral_complex Φ v _
    _ = _ := by
      rw [map_mul,map_star]
      change ⟪v,star (Φ f) (Φ g v)⟫_ℂ = _
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
def vectorLinear : C(X,ℂ) →ₗ[ℂ] H where
  toFun f := Φ f v
  map_add' f g := by simp
  map_smul' c f := by simp
lemma norm_toLp (f : C(X,ℂ)) :
    ‖ContinuousMap.toLp 2 (measure Φ v) ℂ f‖ = ‖vectorLinear Φ v f‖ := by
  have he := congrArg Complex.re (inner_toLp Φ v f f)
  change RCLike.re (⟪ContinuousMap.toLp 2 (measure Φ v) ℂ f,ContinuousMap.toLp 2 (measure Φ v) ℂ f⟫_ℂ) =
    RCLike.re (⟪Φ f v,Φ f v⟫_ℂ) at he
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he
def cyclicMap : Lp ℂ 2 (measure Φ v) →L[ℂ] H :=
  (vectorLinear Φ v).extendOfNorm (ContinuousMap.toLp 2 (measure Φ v) ℂ).toLinearMap
lemma cyclicMap_toLp (f : C(X,ℂ)) :
    cyclicMap Φ v (ContinuousMap.toLp 2 (measure Φ v) ℂ f) = Φ f v := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)
  · exact ⟨1,fun g => by simp only [one_mul]; exact le_of_eq (norm_toLp Φ v g).symm⟩
lemma norm_cyclicMap (f : Lp ℂ 2 (measure Φ v)) : ‖cyclicMap Φ v f‖ = ‖f‖ := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)).induction
    (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) f
  obtain ⟨g,rfl⟩ := hy
  rw [cyclicMap_toLp]
  exact (norm_toLp Φ v g).symm
def cyclicIsometry : Lp ℂ 2 (measure Φ v) →ₗᵢ[ℂ] H :=
  ⟨(cyclicMap Φ v).toLinearMap,norm_cyclicMap Φ v⟩

/-- The scalar spectral map identifies L² with exactly the closed cyclic orbit. -/
lemma cyclicMap_range : Set.range (cyclicMap Φ v) =
    closure (Set.range (fun f : C(X, ℂ) => Φ f v)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨ξ, rfl⟩
    have hξ := (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
      (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)) ξ
    exact map_mem_closure (cyclicMap Φ v).continuous hξ (by
      rintro _ ⟨f, rfl⟩
      exact ⟨f, (cyclicMap_toLp Φ v f).symm⟩)
  · apply closure_minimal
    · rintro _ ⟨f, rfl⟩
      exact ⟨ContinuousMap.toLp 2 (measure Φ v) ℂ f, cyclicMap_toLp Φ v f⟩
    · exact (cyclicIsometry Φ v).isometry.isClosedEmbedding.isClosed_range

end KadisonSimilarity.VectorSpectralMeasure

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicCommutativeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar spectral coordinates for one cyclic subspace of a commutative
representation. These are the components of the central Hilbert model. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance spectralMeasurableSpace : MeasurableSpace (WeakDual.characterSpace ℂ A) :=
  borel (WeakDual.characterSpace ℂ A)
local instance spectralBorelSpace : BorelSpace (WeakDual.characterSpace ℂ A) := ⟨rfl⟩

def commutativeSpectralCalculus (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    C(WeakDual.characterSpace ℂ A, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  π.comp (gelfandStarTransform A).symm.toStarAlgHom

def commutativeVectorMeasure (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Measure (WeakDual.characterSpace ℂ A) :=
  VectorSpectralMeasure.measure (commutativeSpectralCalculus π) ξ

instance commutativeVectorMeasure_finite (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    IsFiniteMeasure (commutativeVectorMeasure π ξ) :=
  inferInstanceAs (IsFiniteMeasure (VectorSpectralMeasure.measure (commutativeSpectralCalculus π) ξ))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicSummandColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite column implementers from an actual orthogonal decomposition into
reducing summands. The finite projections converge strongly by density. -/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology

variable {I : Type*} {K : I → Type*} {H : Type*}
  [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
  [∀ i, CompleteSpace (K i)]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Isometric summand inclusions with mutually orthogonal ranges and dense
linear span. The summands may have different Hilbert spaces. -/
structure OrthogonalSummandDecomposition (K : I → Type*)
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  inclusion : ∀ i, K i →ₗᵢ[ℂ] H
  orthogonal : ∀ i j, i ≠ j → ∀ x y,
    inner ℂ (inclusion i x) (inclusion j y) = 0
  dense_span : (Submodule.span ℂ (⋃ i, Set.range (inclusion i))).topologicalClosure = ⊤

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Approximate cyclic columns

Standard-form vector realization and matrix Kaplansky density with quotient
norm lifting give uniformly bounded approximating columns.
-/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology Pointwise

variable {A K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [PartialOrder A] [StarOrderedRing A]

/-- The commutant of an operator star subalgebra, bundled as a von Neumann
algebra by the elementary triple-commutant identity. -/
def starSubalgebraCommutant (N : StarSubalgebra ℂ (K →L[ℂ] K)) : VonNeumannAlgebra K where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (N : Set (K →L[ℂ] K))
  centralizer_centralizer' := Set.centralizer_centralizer_centralizer _

@[simp] theorem coe_starSubalgebraCommutant (N : StarSubalgebra ℂ (K →L[ℂ] K)) :
    (starSubalgebraCommutant N : Set (K →L[ℂ] K)) = Set.centralizer (N : Set (K →L[ℂ] K)) := by
  change Set.centralizer ((N : Set (K →L[ℂ] K)) ∪ star (N : Set (K →L[ℂ] K))) = _
  rw [StarMemClass.star_coe_eq, Set.union_self]

/-- The bicommutant σ(A)″ of the represented C-star algebra. -/
def representationVonNeumannAlgebra (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : VonNeumannAlgebra K :=
  (starSubalgebraCommutant σ.range).commutant

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem coe_representationVonNeumannAlgebra (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    (representationVonNeumannAlgebra σ : Set (K →L[ℂ] K)) =
      Set.centralizer (Set.centralizer (σ.range : Set (K →L[ℂ] K))) := by
  simp [representationVonNeumannAlgebra]

omit [PartialOrder A] [StarOrderedRing A] in
theorem mem_representationVonNeumannAlgebra (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : A) :
    σ a ∈ representationVonNeumannAlgebra σ := by
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra]
  exact Set.subset_centralizer_centralizer ⟨a, rfl⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FullColumnTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The full-column implementation argument

The corner commutator is constructed here, corrected by the proved cyclic
implementation theorem, and extended through finite matrix coordinates with
exactly the same norm. Extension by zero and the tracial commutation theorem
then identify the resulting intertwiner as a right multiplier.

The finite-factor realization of the corner and its matrix coordinates remains
explicit geometric data; the full-column conclusion is not an input.
-/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

section RightMultipliers

variable {P H D : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

/-- The right multiplication convention, including faithfulness. Composition
has the opposite order: `R_b ∘ R_a = R_(a*b)`. -/
structure TracialRightAction where
  right : P → (H →L[ℂ] H)
  injective : Function.Injective right
  mul : ∀ a b, right (a * b) = (right b).comp (right a)

/-- The finite-trace specialization of the tracial commutation theorem:
Hiai, Theorem 2.2 and Example 2.4 (`JMJ = M′`); equivalently every bounded
left-module endomorphism of `L²(P,τ)` is right multiplication by an element
of `P`. This remains an explicit published input. -/
def TracialCommutationInput (L : P →⋆ₐ[ℂ] (H →L[ℂ] H))
    (R : TracialRightAction (P := P) (H := H)) : Prop :=
  ∀ Z : H →L[ℂ] H, (∀ a, Z.comp (L a) = (L a).comp Z) →
    ∃ b : P, R.right b = Z

end RightMultipliers

section CyclicCornerData

variable {P C K Q : Type*} [CStarAlgebra P] [CStarAlgebra C]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- A representation has a vector whose algebra orbit is dense. Because the
representation is linear in the algebra variable, no additional span is needed. -/
def CyclicStarRepresentation (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∃ ζ : K, DenseRange (fun a : C => σ a ζ)

end CyclicCornerData

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm estimates and commutation identities used in symmetrization
persist under weak-operator limits. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMapWOT
open scoped Topology

variable {H K ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A homogeneous bound on all Hilbert matrix coefficients bounds the
operator norm with the same constant. -/
theorem norm_le_of_matrix_coefficients (T : H →L[ℂ] K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x y, ‖inner ℂ y (T x)‖ ≤ c * ‖y‖ * ‖x‖) : ‖T‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have hx := h x (T x)
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq] at hx
  by_cases hz : ‖T x‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖T x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantTensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix-unit isolation of invariant-tensor coefficients

The permutation contractions are given by their coordinate sums. Their
normalization is the number of cycles, including fixed points. We prove the
matrix-unit isolation and uniqueness steps in the invariant-intertwiner
argument. Schur--Weyl spanning is expressed as a multilinear-form property.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The coordinate formula for the trace contraction of a permutation tensor.
Each index follows the successor convention in the manuscript. -/
def permutationContraction (π : Equiv.Perm ι) (v : ι → Matrix α α ℂ) : ℂ :=
  ∑ f : ι → α, ∏ i, v i (f i) (f (π i))

/-- The number of cycles of a permutation, with singleton cycles included. -/
def permutationCycleCount (π : Equiv.Perm ι) : ℕ :=
  Nat.card (Quotient (Equiv.Perm.SameCycle.setoid π))

/-- Normalizing each cycle trace by the matrix dimension gives the coordinate
formula for the normalized cycle-trace form `Φ_π` in the paper. -/
def normalizedPermutationContraction (π : Equiv.Perm ι)
    (v : ι → Matrix α α ℂ) : ℂ :=
  (Fintype.card α : ℂ)⁻¹ ^ permutationCycleCount π * permutationContraction π v

/-- Invariance under simultaneous conjugation of all matrix arguments. -/
def UnitaryConjugationInvariant
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ) : Prop :=
  ∀ (u : Matrix.unitaryGroup α ℂ) (v : ι → Matrix α α ℂ),
    F (fun i => (u : Matrix α α ℂ) * v i * star (u : Matrix α α ℂ)) = F v

/-- The finite-dimensional consequence of Schur--Weyl duality used in the
paper. Source: Grinko--Ozols, *Linear programming with unitary-equivariant
constraints*, Comm. Math. Phys. 405 (2024), article 278, Theorem 3.1, combined
with the nondegenerate matrix trace pairing. Matrix-unit isolation and
uniqueness establish independence in the stable range. -/
def SchurWeylMultilinearSpanning (ι α : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : Prop :=
  ∀ F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ,
    UnitaryConjugationInvariant F →
    ∃ c : Equiv.Perm ι → ℂ, ∀ v,
      F v = ∑ π, c π * normalizedPermutationContraction π v

section BlockAmplification

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Labels constant along each cycle are exactly functions on the cycle
quotient. This is the counting mechanism behind trace normalization. -/
abbrev CycleConstantLabelings (π : Equiv.Perm ι) (β : Type*) :=
  {f : ι → β // ∀ i, f (π i) = f i}

end BlockAmplification

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing centered singleton cycles

A fixed point contributes the trace of its matrix argument. Factorization
of the coordinate contraction shows that vanishing on
centered singleton tails does not require an additional invariant-theory input.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- The finite set of cycles of a permutation, including fixed points. -/
abbrev PermutationCycles (π : Equiv.Perm ι) :=
  Quotient (Equiv.Perm.SameCycle.setoid π)

/-- The vertices in one cycle. -/
abbrev CycleMembers (π : Equiv.Perm ι) (q : PermutationCycles π) :=
  {i : ι // (⟦i⟧ : PermutationCycles π) = q}

/-- The cycle structure remaining after the endpoint and centering estimates. -/
def EndpointPairing (π : Equiv.Perm ι) (i₀ : ι) : Prop :=
  π i₀ = i₀ ∧ Function.Involutive π ∧ ∀ i, π i = i → i = i₀

/-- Every tail pair joins one source slot to one test slot. -/
def IsCrossPairing {k l : ℕ} (π : Equiv.Perm (Fin k ⊕ Fin l)) : Prop :=
  (∀ i, ∃ j, π (Sum.inl i) = Sum.inr j) ∧
    (∀ j, ∃ i, π (Sum.inr j) = Sum.inl i)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_PairingLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Disjoint labels for the pairing test

The cycle classes of one perfect matching index disjoint label pools. This
isolates that matching while allowing the labels of same-side pairs to vary.
-/

noncomputable section
namespace KadisonSimilarity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A perfect matching represented by its fixed-point-free involution. -/
abbrev PerfectMatching (ι : Type*) :=
  {π : Equiv.Perm ι // Function.Involutive π ∧ ∀ i, π i ≠ i}

instance perfectMatchingFintype : Fintype (PerfectMatching ι) := Fintype.ofFinite _

/-- On orthonormal labels, a pairing contraction is the product of equality
indicators along its pairs. Repeating an indicator has no effect. -/
def pairingLabelKernel {J : Type*} [DecidableEq J]
    (P : PerfectMatching ι) (labels : ι → J) : ℂ :=
  ∏ i, if labels i = labels (P.1 i) then 1 else 0

variable {k l : ℕ}

/-- A pair is entirely in the source precisely when its cycle contains no test slot. -/
def IsSourcePairClass (P : PerfectMatching (Fin k ⊕ Fin l))
    (q : PermutationCycles P.1) : Prop :=
  ∀ j : Fin l, (⟦Sum.inr j⟧ : PermutationCycles P.1) ≠ q

/-- A pair is entirely in the test precisely when its cycle contains no source slot. -/
def IsTestPairClass (P : PerfectMatching (Fin k ⊕ Fin l))
    (q : PermutationCycles P.1) : Prop :=
  ∀ i : Fin k, (⟦Sum.inl i⟧ : PermutationCycles P.1) ≠ q

abbrev SourcePairClasses (P : PerfectMatching (Fin k ⊕ Fin l)) :=
  {q : PermutationCycles P.1 // IsSourcePairClass P q}

abbrev TestPairClasses (P : PerfectMatching (Fin k ⊕ Fin l)) :=
  {q : PermutationCycles P.1 // IsTestPairClass P q}

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorization of matrix contractions along pairs

This is the finite combinatorial bridge between the cycle expansion and the
bilinear pairing polynomials: each two-cycle contributes exactly one trace of
a product. The normalization uses the actual number of matching orbits.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Choose the lower-ranked vertex in each pair. -/
abbrev MatchingRepresentatives (rank : ι → ℕ) (P : PerfectMatching ι) :=
  {i : ι // rank i < rank (P.1 i)}

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix stages inside an actual tracial Hilbert representation

A trace-preserving matrix embedding supplies the normalized Hilbert--Schmidt
geometry, the corner left action, and the centered projection used by the
invariant-intertwiner argument. No invariant-theory conclusion is an input.
-/

noncomputable section
namespace KadisonSimilarity

variable {R E α : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [Fintype α] [DecidableEq α]

omit [CompleteSpace E] in
/-- A normalized trace gives the required unit trace vector. -/
theorem norm_tracialTraceVector (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b)) (hτ : τ 1 = 1) :
    ‖V 1‖ = 1 := by
  have hs : ‖V 1‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinner, star_one, one_mul, hτ]
    rfl
  nlinarith [norm_nonneg (V 1)]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_TracialCornerCyclicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cyclicity of finite tracial corners from dense algebra vectors and
partial-isometry transport. No corner cyclicity or density is assumed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The range projection of an algebraic partial isometry is a projection. -/
theorem range_projection_of_initial_projection (r v : P) (hr : IsStarProjection r)
    (hv : star v * v = r) : IsStarProjection (v * star v) := by
  have hvr : v * r = v := by
    apply sub_eq_zero.mp
    apply (CStarRing.star_mul_self_eq_zero_iff (v * r - v)).mp
    calc
      star (v * r - v) * (v * r - v) =
          r * (star v * v) * r - r * (star v * v) - (star v * v) * r + star v * v := by
        rw [star_sub, star_mul, hr.isSelfAdjoint.star_eq]
        noncomm_ring
      _ = 0 := by simp only [hv, hr.isIdempotentElem.eq]; abel
  constructor
  · change (v * star v) * (v * star v) = v * star v
    calc
      _ = (v * (star v * v)) * star v := by noncomm_ring
      _ = _ := by rw [hv, hvr]
  · exact IsSelfAdjoint.mul_star_self v

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixArrayFlattening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening nested matrix and Hilbert-array coordinates -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder


section MatrixFlattening

variable {A : Type*} [CStarAlgebra A]

theorem sum_cstarMatrix_apply {p q : ℕ}
    (f : Fin p → CStarMatrix (Fin q) (Fin q) A) (k l : Fin q) :
    (∑ s : Fin p, f s) k l = ∑ s : Fin p, f s k l := by
  have hs (s : Finset (Fin p)) : (∑ i ∈ s, f i) k l = ∑ i ∈ s, f i k l := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, CStarMatrix.add_apply, ih]
  exact hs Finset.univ

/-- First flatten block matrices to a product index. -/
def blockMatrixProductEquiv (p q : ℕ) :
    CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin p × Fin q) (Fin p × Fin q) A where
  toFun X := CStarMatrix.ofMatrix fun i j => X i.1 j.1 i.2 j.2
  invFun X := CStarMatrix.ofMatrix fun i j =>
    CStarMatrix.ofMatrix fun k l => X (i, k) (j, l)
  left_inv X := by ext i j k l; rfl
  right_inv X := by ext i j; rfl
  map_add' X Y := by ext i j; rfl
  map_smul' c X := by ext i j; rfl
  map_star' X := by ext i j; rfl
  map_mul' X Y := by
    ext i j
    rcases i with ⟨i, k⟩
    rcases j with ⟨j, l⟩
    change (∑ s : Fin p, X i s * Y s j) k l =
      ∑ s : Fin p × Fin q, X i s.1 k s.2 * Y s.1 j s.2 l
    rw [sum_cstarMatrix_apply]
    simp only [CStarMatrix.mul_apply, Fintype.sum_prod_type]

@[simp] theorem blockMatrixProductEquiv_apply (p q : ℕ)
    (X : CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A))
    (i j : Fin p) (k l : Fin q) :
    blockMatrixProductEquiv (A := A) p q X (i, k) (j, l) = X i j k l := rfl

/-- Flatten square blocks using the standard product enumeration. -/
def blockMatrixFlatten (p q : ℕ) :
    CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin (p * q)) (Fin (p * q)) A :=
  (blockMatrixProductEquiv p q).trans (CStarMatrix.reindexₐ ℂ A finProdFinEquiv)

@[simp] theorem blockMatrixFlatten_apply (p q : ℕ)
    (X : CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A))
    (i j : Fin p) (k l : Fin q) :
    blockMatrixFlatten (A := A) p q X (finProdFinEquiv (i, k))
      (finProdFinEquiv (j, l)) = X i j k l := by
  change blockMatrixProductEquiv p q X
    ((finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm (finProdFinEquiv (i, k)))
    ((finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm (finProdFinEquiv (j, l))) = _
  simp only [Equiv.symm_apply_apply, blockMatrixProductEquiv_apply]

variable [PartialOrder A] [StarOrderedRing A]

@[simp] theorem norm_blockMatrixFlatten (p q : ℕ)
    (X : CStarMatrix (Fin p) (Fin p) (CStarMatrix (Fin q) (Fin q) A)) :
    ‖blockMatrixFlatten p q X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (blockMatrixFlatten (A := A) p q).toNonUnitalStarAlgHom
    (blockMatrixFlatten p q).injective X

end MatrixFlattening

section EntrywiseEquivalence

variable {B C : Type*} [Semiring B] [Semiring C] [StarRing B] [StarRing C]
  [SMul ℂ B] [SMul ℂ C]

/-- An equivalence of coefficient algebras induces the entrywise matrix equivalence. -/
def entrywiseCStarMatrixEquiv (n : ℕ) (e : B ≃⋆ₐ[ℂ] C) :
    CStarMatrix (Fin n) (Fin n) B ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) C where
  toFun X := X.map e
  invFun X := X.map e.symm
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp
  map_add' X Y := by ext i j; simp
  map_smul' c X := by ext i j; simp
  map_star' X := by
    ext i j
    change e (star (X j i)) = star (e (X j i))
    exact map_star e _
  map_mul' X Y := by
    ext i j
    change e (∑ k : Fin n, X i k * Y k j) = ∑ k : Fin n, e (X i k) * e (Y k j)
    simp only [map_sum, map_mul]

@[simp] theorem entrywiseCStarMatrixEquiv_apply (n : ℕ) (e : B ≃⋆ₐ[ℂ] C)
    (X : CStarMatrix (Fin n) (Fin n) B) (i j : Fin n) :
    entrywiseCStarMatrixEquiv n e X i j = e (X i j) := rfl

end EntrywiseEquivalence

section TripleMatrices

variable {A : Type*} [CStarAlgebra A]

/-- Flatten three matrix indices, retaining the outer-to-inner order. -/
def tripleMatrixFlatten (p q t : ℕ) :
    CStarMatrix (Fin p) (Fin p)
      (CStarMatrix (Fin q) (Fin q) (CStarMatrix (Fin t) (Fin t) A)) ≃⋆ₐ[ℂ]
    CStarMatrix (Fin (p * (q * t))) (Fin (p * (q * t))) A :=
  (entrywiseCStarMatrixEquiv p (blockMatrixFlatten q t)).trans
    (blockMatrixFlatten p (q * t))

@[simp] theorem tripleMatrixFlatten_apply (p q t : ℕ)
    (X : CStarMatrix (Fin p) (Fin p)
      (CStarMatrix (Fin q) (Fin q) (CStarMatrix (Fin t) (Fin t) A)))
    (i j : Fin p) (k l : Fin q) (a b : Fin t) :
    tripleMatrixFlatten p q t X
      (finProdFinEquiv (i, finProdFinEquiv (k, a)))
      (finProdFinEquiv (j, finProdFinEquiv (l, b))) = X i j k l a b := by
  simp [tripleMatrixFlatten]

/-- The four-by-four dilation's flattened matrix has size `4 * n`. -/
def fourfoldMatrixFlatten (n : ℕ) :
    CStarMatrix (Fin 2) (Fin 2)
      (CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin n) (Fin n) A)) ≃⋆ₐ[ℂ]
    CStarMatrix (Fin (4 * n)) (Fin (4 * n)) A :=
  (tripleMatrixFlatten 2 2 n).trans
    (CStarMatrix.reindexₐ ℂ A (finCongr (by omega : 2 * (2 * n) = 4 * n)))

/-- The common enumeration of the three finite indices. -/
def fourfoldIndexEquiv (n : ℕ) : (Fin 2 × (Fin 2 × Fin n)) ≃ Fin (4 * n) :=
  ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (by omega : 2 * (2 * n) = 4 * n))

@[simp] theorem fourfoldMatrixFlatten_apply (n : ℕ)
    (X : CStarMatrix (Fin 2) (Fin 2)
      (CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin n) (Fin n) A)))
    (i j k l : Fin 2) (a b : Fin n) :
    fourfoldMatrixFlatten n X (fourfoldIndexEquiv n (i, (k, a)))
      (fourfoldIndexEquiv n (j, (l, b))) = X i j k l a b := by
  change tripleMatrixFlatten 2 2 n X
    ((finCongr (by omega : 2 * (2 * n) = 4 * n)).symm
      (finCongr (by omega : 2 * (2 * n) = 4 * n)
        (finProdFinEquiv (i, finProdFinEquiv (k, a)))))
    ((finCongr (by omega : 2 * (2 * n) = 4 * n)).symm
      (finCongr (by omega : 2 * (2 * n) = 4 * n)
        (finProdFinEquiv (j, finProdFinEquiv (l, b))))) = _
  simp only [Equiv.symm_apply_apply, tripleMatrixFlatten_apply]

end TripleMatrices

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite standard multiplicities exhaust the countable standard
representation.  The first-coordinate projections and all intertwining
identities below are constructed on the actual Hilbert direct sum. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMap
open scoped ENNReal Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The countable Hilbert direct sum of a fixed Hilbert space. -/
abbrev CountableCopies (H : Type*) [NormedAddCommGroup H] := lp (fun _ : ℕ => H) 2

def countableOperatorValue (T : H →L[ℂ] H) (x : CountableCopies H) :
    CountableCopies H :=
  ⟨fun i => T (x i), ((lp.memℓp x).norm.const_smul ‖T‖).mono
    (fun i => T.le_opNorm (x i))⟩

theorem countableOperatorValue_norm (T : H →L[ℂ] H) (x : CountableCopies H) :
    ‖countableOperatorValue T x‖ ≤ ‖T‖ * ‖x‖ := by
  have h := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (x := countableOperatorValue T x) (y := (‖T‖ : ℝ) • x) (fun i => by
      change ‖T (x i)‖ ≤ ‖(‖T‖ : ℝ) • x i‖
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)]
        using T.le_opNorm (x i))
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)] using h

/-- The actual coordinatewise countable amplification of an operator. -/
def countableAmplify (T : H →L[ℂ] H) : CountableCopies H →L[ℂ] CountableCopies H :=
  LinearMap.mkContinuous
    { toFun := countableOperatorValue T
      map_add' x y := by apply Subtype.ext; funext i; exact map_add T (x i) (y i)
      map_smul' c x := by apply Subtype.ext; funext i; exact map_smul T c (x i) }
    ‖T‖ (countableOperatorValue_norm T)

@[simp] theorem countableAmplify_apply (T : H →L[ℂ] H) (x : CountableCopies H) (i : ℕ) :
    countableAmplify T x i = T (x i) := rfl

variable [CompleteSpace H]

theorem countableAmplify_adjoint (T : H →L[ℂ] H) :
    (countableAmplify T).adjoint = countableAmplify T.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum, countableAmplify_apply, adjoint_inner_left]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_LocalizedL2Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localized L² estimates recover pointwise bounds. This is the norm
argument for the columns of an operator commuting with diagonal projections. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped ENNReal Topology

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma l2_norm_sq_eq_integral (f : Lp H 2 μ) :
    ‖f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  congr 1
  funext a
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (f a)).symm

variable [IsFiniteMeasure μ]

omit [CompleteSpace H] in
/-- Bounds on every localized square norm imply an almost-everywhere bound.
The localized vector is allowed to be any representative of the indicator. -/
theorem ae_norm_le_of_localized_square_bound (f : Lp H 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ (s : Set Ω), MeasurableSet s →
      ∃ g : Lp H 2 μ, g =ᵐ[μ] s.indicator f ∧ ‖g‖ ^ 2 ≤ C ^ 2 * μ.real s) :
    ∀ᵐ a ∂μ, ‖f a‖ ≤ C := by
  have hf : Integrable (fun a => ‖f a‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hsquares : ∀ᵐ a ∂μ, ‖f a‖ ^ 2 ≤ C ^ 2 := by
    apply ae_le_of_forall_setIntegral_le hf (integrable_const (C ^ 2))
    intro s hs _
    obtain ⟨g, hg, hbound⟩ := hlocal s hs
    have he : ‖g‖ ^ 2 = ∫ a in s, ‖f a‖ ^ 2 ∂μ := by
      rw [l2_norm_sq_eq_integral]
      have heq : (fun a => ‖g a‖ ^ 2) =ᵐ[μ] s.indicator (fun a => ‖f a‖ ^ 2) := by
        filter_upwards [hg] with a ha
        rw [ha]
        by_cases h : a ∈ s <;> simp [h]
      rw [integral_congr_ae heq, integral_indicator hs]
    rw [← he]
    simpa [measureReal_def, mul_comm] using hbound
  filter_upwards [hsquares] with a ha
  exact (sq_le_sq₀ (norm_nonneg _) hC).mp ha

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_L2HilbertSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Hilbert sum of scalar L² spaces over one measure is the L² space
of the coordinate Hilbert space. The construction uses actual L² maps. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {ι : Type*} [DecidableEq ι]

abbrev ScalarHilbertCoordinates (ι : Type*) : Type _ := lp (fun _ : ι => ℂ) 2

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ContinuousL2Multiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous scalar multiplication on L², with the exact pointwise formula
and continuous-function coordinates used in spectral assembly. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)

theorem continuousL2Mul_memLp (f : C(X, ℂ)) (ξ : Lp ℂ 2 μ) :
    MemLp (fun x => f x * ξ x) 2 μ := by
  apply (Lp.memLp ξ).of_le_mul (c := ‖f‖)
  · exact f.continuous.measurable.aestronglyMeasurable.mul (Lp.aestronglyMeasurable ξ)
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _)

def continuousL2MulVector (f : C(X, ℂ)) (ξ : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (continuousL2Mul_memLp μ f ξ).toLp (fun x => f x * ξ x)

theorem continuousL2MulVector_ae (f : C(X, ℂ)) (ξ : Lp ℂ 2 μ) :
    continuousL2MulVector μ f ξ =ᵐ[μ] (fun x => f x * ξ x) := MemLp.coeFn_toLp _

def continuousL2MulLinear (f : C(X, ℂ)) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := continuousL2MulVector μ f
  map_add' ξ η := by
    apply Lp.ext
    filter_upwards [continuousL2MulVector_ae μ f (ξ + η),
      continuousL2MulVector_ae μ f ξ, continuousL2MulVector_ae μ f η,
      Lp.coeFn_add ξ η, Lp.coeFn_add (continuousL2MulVector μ f ξ)
        (continuousL2MulVector μ f η)] with x hsum hξ hη hin hout
    rw [hsum, hout]
    simp only [Pi.add_apply]
    rw [hξ, hη, hin]
    simp only [Pi.add_apply, mul_add]
  map_smul' c ξ := by
    apply Lp.ext
    filter_upwards [continuousL2MulVector_ae μ f (c • ξ),
      continuousL2MulVector_ae μ f ξ, Lp.coeFn_smul c ξ,
      Lp.coeFn_smul c (continuousL2MulVector μ f ξ)] with x hsmul hξ hin hout
    change continuousL2MulVector μ f (c • ξ) x = (c • continuousL2MulVector μ f ξ) x
    rw [hsmul, hout]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hξ, hin]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem continuousL2MulVector_norm (f : C(X, ℂ)) (ξ : Lp ℂ 2 μ) :
    ‖continuousL2MulVector μ f ξ‖ ≤ ‖f‖ * ‖ξ‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [continuousL2MulVector_ae μ f ξ] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _)

def continuousL2Mul (f : C(X, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (continuousL2MulLinear μ f).mkContinuous ‖f‖ (continuousL2MulVector_norm μ f)

theorem continuousL2Mul_ae (f : C(X, ℂ)) (ξ : Lp ℂ 2 μ) :
    continuousL2Mul μ f ξ =ᵐ[μ] (fun x => f x * ξ x) := continuousL2MulVector_ae μ f ξ

variable [IsFiniteMeasure μ]

theorem continuousL2Mul_toLp (f g : C(X, ℂ)) :
    continuousL2Mul μ f (ContinuousMap.toLp 2 μ ℂ g) =
      ContinuousMap.toLp 2 μ ℂ (f * g) := by
  apply Lp.ext
  filter_upwards [continuousL2Mul_ae μ f (ContinuousMap.toLp 2 μ ℂ g),
    ContinuousMap.coeFn_toLp (μ := μ) (p := 2) (𝕜 := ℂ) g,
    ContinuousMap.coeFn_toLp (μ := μ) (p := 2) (𝕜 := ℂ) (f * g)] with x hm hg hfg
  rw [hm, hg, hfg, ContinuousMap.mul_apply]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both spectral coordinate maps intertwine the continuous scalar action.
The identities are proved first on continuous functions and extended by density. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

namespace VectorSpectralMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)

theorem cyclicMap_intertwines (f : C(X, ℂ)) (ξ : Lp ℂ 2 (measure Φ v)) :
    cyclicMap Φ v (continuousL2Mul (measure Φ v) f ξ) = Φ f (cyclicMap Φ v ξ) := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
    (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)).induction
      (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) ξ
  obtain ⟨g, rfl⟩ := hy
  rw [continuousL2Mul_toLp, cyclicMap_toLp, cyclicMap_toLp, map_mul]
  rfl

end VectorSpectralMeasure

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_VectorL2Multiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous scalar multiplication on vector-valued L² spaces. -/

noncomputable section
namespace KadisonSimilarity.VectorL2
open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem continuousL2Mul_memLp (f : C(X, ℂ)) (ξ : Lp H 2 μ) :
    MemLp (fun x => f x • ξ x) 2 μ := by
  apply (Lp.memLp ξ).of_le_mul (c := ‖f‖)
  · exact f.continuous.measurable.aestronglyMeasurable.smul (Lp.aestronglyMeasurable ξ)
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _)

def continuousL2MulVector (f : C(X, ℂ)) (ξ : Lp H 2 μ) : Lp H 2 μ :=
  (continuousL2Mul_memLp μ f ξ).toLp (fun x => f x • ξ x)

theorem continuousL2MulVector_ae (f : C(X, ℂ)) (ξ : Lp H 2 μ) :
    continuousL2MulVector μ f ξ =ᵐ[μ] (fun x => f x • ξ x) := MemLp.coeFn_toLp _

def continuousL2MulLinear (f : C(X, ℂ)) : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ where
  toFun := continuousL2MulVector μ f
  map_add' ξ η := by
    apply Lp.ext
    filter_upwards [continuousL2MulVector_ae μ f (ξ + η),
      continuousL2MulVector_ae μ f ξ, continuousL2MulVector_ae μ f η,
      Lp.coeFn_add ξ η, Lp.coeFn_add (continuousL2MulVector μ f ξ)
        (continuousL2MulVector μ f η)] with x hsum hξ hη hin hout
    rw [hsum, hout]
    simp only [Pi.add_apply]
    rw [hξ, hη, hin]
    simp only [Pi.add_apply, smul_add]
  map_smul' c ξ := by
    apply Lp.ext
    filter_upwards [continuousL2MulVector_ae μ f (c • ξ),
      continuousL2MulVector_ae μ f ξ, Lp.coeFn_smul c ξ,
      Lp.coeFn_smul c (continuousL2MulVector μ f ξ)] with x hsmul hξ hin hout
    change continuousL2MulVector μ f (c • ξ) x = (c • continuousL2MulVector μ f ξ) x
    rw [hsmul, hout]
    simp only [Pi.smul_apply]
    rw [hξ, hin]
    simp only [Pi.smul_apply]
    exact smul_comm _ _ _

theorem continuousL2MulVector_norm (f : C(X, ℂ)) (ξ : Lp H 2 μ) :
    ‖continuousL2MulVector μ f ξ‖ ≤ ‖f‖ * ‖ξ‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [continuousL2MulVector_ae μ f ξ] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _)

def continuousL2Mul (f : C(X, ℂ)) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  (continuousL2MulLinear μ f).mkContinuous ‖f‖ (continuousL2MulVector_norm μ f)

theorem continuousL2Mul_ae (f : C(X, ℂ)) (ξ : Lp H 2 μ) :
    continuousL2Mul μ f ξ =ᵐ[μ] (fun x => f x • ξ x) := continuousL2MulVector_ae μ f ξ

end KadisonSimilarity.VectorL2

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonSpectralMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One finite measure dominates every member of a countable family of
finite spectral measures. The Radon–Nikodym densities give common coordinates. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (ν : ι → Measure Ω)
  [∀ n, IsFiniteMeasure (ν n)]

def commonSpectralMeasure : Measure Ω := (Measure.sum ν).toFinite

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CommonCyclicEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embed the original separable Hilbert space into a single L² space by
placing its cyclic spectral coordinates over one finite dominating measure. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*}
  [CommCStarAlgebra A]
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))

local instance commonCyclicMeasurable : MeasurableSpace (WeakDual.characterSpace ℂ A) :=
  borel (WeakDual.characterSpace ℂ A)
local instance commonCyclicBorel : BorelSpace (WeakDual.characterSpace ℂ A) := ⟨rfl⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralSteps
attribute [-instance] _root_.OAI.KadisonSimilarity.perfectMatchingFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The spectral-step part of the hyperreflexivity deduction

`SpectralStepApproximation` isolates exactly the norm approximation by spectral
projections that the manuscript uses. It is the step-function specialization of
Blackadar, *Operator Algebras* (2006; revised manuscript February 8, 2017),
I.6.1.3--4, with membership of spectral projections from I.9.2.1(iv).
The scalar offset is essential: summation by parts gives a total variation of
the remaining coefficients at most twice the operator norm.

The spectral approximation and the uniform commutator estimate together imply
the hyperreflexivity bound.
-/

noncomputable section

namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A scalar offset plus a finite linear combination of spectral projections. -/
def spectralStep {n : ℕ} (r : ℝ) (c : Fin n → ℝ) (e : Fin n → H →L[ℂ] H) :
    H →L[ℂ] H := (r : ℂ) • 1 + ∑ i, (c i : ℂ) • e i

/-- Spectral approximation with a bound on the sum of absolute coefficients. -/
def SpectralStepApproximation (P : VonNeumannAlgebra H) : Prop :=
  ∀ A : H →L[ℂ] H, A ∈ P → star A = A → ∀ δ : ℝ, 0 < δ →
    ∃ (n : ℕ) (r : ℝ) (c : Fin n → ℝ) (e : Fin n → H →L[ℂ] H),
      (∀ i, e i ∈ P ∧ star (e i) = e i ∧ e i * e i = e i) ∧
      (∑ i, |c i|) ≤ 2 * ‖A‖ ∧ ‖A - spectralStep r c e‖ ≤ δ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralStepDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete spectral cut projections

We construct the spectral cuts from the closed range of the positive part.
The construction takes place in the represented Hilbert space; bicommutant
closure proves membership in the given von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The prescribed geometric error radius. -/
def binarySpectralRadius (A : H →L[ℂ] H) (k : ℕ) : ℝ := ‖A‖ * (1 / 2 : ℝ) ^ k

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_KaplanskyTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded rational transform for Kaplansky approximation

The function `2t/(1+t²)` maps the real line into the unit interval. Its
operator difference is controlled on two fixed vectors without a bound on
the approximating selfadjoint operators. This is the bounded-transform
step in Kaplansky approximation.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap
open scoped CStarAlgebra

variable {B : Type*} [CStarAlgebra B]

def kaplanskyReciprocal (A : B) : B :=
  cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) A

def kaplanskyTransform (A : B) : B :=
  (2 : ℝ) • (A * kaplanskyReciprocal A)

theorem reciprocal_continuous : Continuous (fun t : ℝ => (1 + t ^ 2)⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro t
    positivity

theorem kaplanskyReciprocal_norm_le (A : B) :
    ‖kaplanskyReciprocal A‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t _
  have ht : 0 < 1 + t ^ 2 := by positivity
  simp only [Real.norm_eq_abs, abs_inv, abs_of_pos ht]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])

theorem kaplanskyReciprocal_mul_norm_le (A : B) (hA : IsSelfAdjoint A) :
    ‖A * kaplanskyReciprocal A‖ ≤ 1 / 2 := by
  have hf := reciprocal_continuous.continuousOn (s := spectrum ℝ A)
  change ‖A * cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) A‖ ≤ _
  conv_lhs => arg 1; arg 1; rw [← cfc_id' ℝ A hA]
  rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (1 + t ^ 2)⁻¹) A continuousOn_id hf]
  apply norm_cfc_le (by norm_num)
  intro t _
  have ht : 0 < 1 + t ^ 2 := by positivity
  have habs : |t| ≤ (1 + t ^ 2) / 2 := by
    nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht]
  change |t| / (1 + t ^ 2) ≤ 1 / 2
  apply (div_le_iff₀ ht).mpr
  linarith

theorem kaplanskyTransform_norm_le (A : B) (hA : IsSelfAdjoint A) :
    ‖kaplanskyTransform A‖ ≤ 1 := by
  rw [kaplanskyTransform, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [kaplanskyReciprocal_mul_norm_le A hA]

theorem kaplanskyReciprocal_right_inverse (A : B) (hA : IsSelfAdjoint A) :
    kaplanskyReciprocal A * (1 + A ^ 2) = 1 := by
  have hf := reciprocal_continuous.continuousOn (s := spectrum ℝ A)
  have hg : ContinuousOn (fun t : ℝ => 1 + t ^ 2) (spectrum ℝ A) := by fun_prop
  have he : cfc (fun t : ℝ => 1 + t ^ 2) A = 1 + A ^ 2 := by
    rw [cfc_add A (fun _ : ℝ => 1) (fun t : ℝ => t ^ 2) continuousOn_const (by fun_prop),
      cfc_const_one ℝ A hA, cfc_pow (fun t : ℝ => t) 2 A continuousOn_id hA, cfc_id' ℝ A hA]
  rw [kaplanskyReciprocal, ← he, ← cfc_mul _ _ A hf hg]
  have hone : (fun t : ℝ => (1 + t ^ 2)⁻¹ * (1 + t ^ 2)) = fun _ => 1 := by
    funext t
    exact inv_mul_cancel₀ (by positivity : (1 + t ^ 2 : ℝ) ≠ 0)
  rw [hone, cfc_const_one ℝ A hA]

theorem kaplanskyReciprocal_commute (A : B) :
    Commute (kaplanskyReciprocal A) A :=
  (Commute.refl A).cfc_real _

theorem kaplanskyReciprocal_left_inverse (A : B) (hA : IsSelfAdjoint A) :
    (1 + A ^ 2) * kaplanskyReciprocal A = 1 := by
  calc
    (1 + A ^ 2) * kaplanskyReciprocal A = kaplanskyReciprocal A * (1 + A ^ 2) := by
      calc
        _ = kaplanskyReciprocal A + A ^ 2 * kaplanskyReciprocal A := by noncomm_ring
        _ = kaplanskyReciprocal A + kaplanskyReciprocal A * A ^ 2 := by
          rw [((kaplanskyReciprocal_commute A).symm.pow_left 2).eq]
        _ = _ := by noncomm_ring
    _ = 1 := kaplanskyReciprocal_right_inverse A hA

/-- The two error vectors are tested after fixed functions of B. No norm
bound on A occurs in the resulting strong approximation argument. -/
theorem kaplanskyReciprocal_difference (A D : B)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint D) :
    A * kaplanskyReciprocal A - D * kaplanskyReciprocal D =
      kaplanskyReciprocal A *
        ((A - D) - A * (A - D) * D) * kaplanskyReciprocal D := by
  let G := kaplanskyReciprocal A
  let F := kaplanskyReciprocal D
  have hG : G * (1 + A ^ 2) = 1 := kaplanskyReciprocal_right_inverse A hA
  have hF : (1 + D ^ 2) * F = 1 := kaplanskyReciprocal_left_inverse D hB
  have hGA : G * A = A * G := (kaplanskyReciprocal_commute A).eq
  change A * G - D * F = G * ((A - D) - A * (A - D) * D) * F
  calc
    A * G - D * F = (G * A) * ((1 + D ^ 2) * F) -
        (G * (1 + A ^ 2)) * (D * F) := by rw [hF, hG, mul_one, one_mul, hGA]
    _ = G * ((A - D) - A * (A - D) * D) * F := by noncomm_ring

/-- The scalar transform used in bounded approximation. -/
def kaplanskyFunction (t : ℝ) : ℝ := 2 * (t * (1 + t ^ 2)⁻¹)

theorem kaplanskyFunction_continuous : Continuous kaplanskyFunction := by
  exact continuous_const.mul (continuous_id.mul reciprocal_continuous)

theorem kaplanskyTransform_eq_cfc (A : B) (hA : IsSelfAdjoint A) :
    kaplanskyTransform A = cfc kaplanskyFunction A := by
  change kaplanskyTransform A = cfc (fun t : ℝ => 2 * (t * (1 + t ^ 2)⁻¹)) A
  rw [cfc_const_mul (2 : ℝ) (fun t : ℝ => t * (1 + t ^ 2)⁻¹) A
    (continuous_id.mul reciprocal_continuous).continuousOn,
    cfc_mul (fun t : ℝ => t) (fun t : ℝ => (1 + t ^ 2)⁻¹) A
      continuousOn_id reciprocal_continuous.continuousOn,
    cfc_id' ℝ A hA]
  rfl

def kaplanskyInverseFunction (t : ℝ) : ℝ :=
  t / (1 + Real.sqrt (1 - t ^ 2))

theorem kaplanskyInverseFunction_continuous :
    Continuous kaplanskyInverseFunction := by
  apply Continuous.div continuous_id
  · fun_prop
  · intro t
    positivity

theorem kaplanskyFunction_inverse (t : ℝ) (ht : |t| ≤ 1) :
    kaplanskyFunction (kaplanskyInverseFunction t) = t := by
  have hts := abs_le.mp ht
  have hs : 0 ≤ 1 - t ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - t) (by linarith : 0 ≤ 1 + t)]
  have he := Real.sq_sqrt hs
  have hp : 0 < 1 + Real.sqrt (1 - t ^ 2) := by positivity
  have hq : 0 < 1 + (t / (1 + Real.sqrt (1 - t ^ 2))) ^ 2 := by positivity
  unfold kaplanskyFunction kaplanskyInverseFunction
  field_simp
  nlinarith

/-- The bounded inverse branch, defined by functional calculus. -/
def kaplanskyPreimage (T : B) : B := cfc kaplanskyInverseFunction T

theorem kaplanskyPreimage_selfAdjoint (T : B) : IsSelfAdjoint (kaplanskyPreimage T) :=
  cfc_predicate _ T

theorem kaplanskyPreimage_mem (S : StarSubalgebra ℂ B) (hS : IsClosed (S : Set B))
    (T : B) (hT : T ∈ S) : kaplanskyPreimage T ∈ S := by
  let := hS
  exact cfc_mem (𝕜' := ℂ) (s := S) kaplanskyInverseFunction hT

/-- Every selfadjoint contraction is a bounded transform of a selfadjoint
member of its own generated C-star algebra. -/
theorem kaplanskyTransform_preimage (T : B) (hT : IsSelfAdjoint T)
    (hn : ‖T‖ ≤ 1) : kaplanskyTransform (kaplanskyPreimage T) = T := by
  let D := kaplanskyPreimage T
  have hD : IsSelfAdjoint D := kaplanskyPreimage_selfAdjoint T
  change kaplanskyTransform D = T
  rw [kaplanskyTransform_eq_cfc D hD]
  change cfc kaplanskyFunction (cfc kaplanskyInverseFunction T) = T
  rw [← cfc_comp _ _ T hT kaplanskyFunction_continuous.continuousOn
    kaplanskyInverseFunction_continuous.continuousOn]
  calc
    cfc (kaplanskyFunction ∘ kaplanskyInverseFunction) T = cfc id T := by
      apply cfc_congr
      intro t ht
      apply kaplanskyFunction_inverse
      by_cases hnt : Nontrivial B
      · let : Nontrivial B := hnt
        exact (show |t| ≤ ‖T‖ from spectrum.norm_le_norm_of_mem ht).trans hn
      · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp hnt
        have he : spectrum ℝ T = ∅ := spectrum.of_subsingleton T
        exact False.elim ((Set.notMem_empty t) (he ▸ ht))
    _ = T := cfc_id' ℝ T hT

theorem map_kaplanskyTransform {C : Type*} [CStarAlgebra C]
    (σ : B →⋆ₐ[ℂ] C) (A : B) (hA : IsSelfAdjoint A) :
    σ (kaplanskyTransform A) = kaplanskyTransform (σ A) := by
  rw [kaplanskyTransform_eq_cfc A hA,
    σ.map_cfc kaplanskyFunction A kaplanskyFunction_continuous.continuousOn,
    kaplanskyTransform_eq_cfc (σ A) (hA.map σ)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kaplanskyReciprocal_difference_apply_le (A B : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (x : H) :
    ‖(A * kaplanskyReciprocal A - B * kaplanskyReciprocal B) x‖ ≤
      ‖(A - B) (kaplanskyReciprocal B x)‖ +
        (1 / 2) * ‖(A - B) (B (kaplanskyReciprocal B x))‖ := by
  rw [kaplanskyReciprocal_difference A B hA hB]
  have he : (kaplanskyReciprocal A *
      ((A - B) - A * (A - B) * B) * kaplanskyReciprocal B) x =
      kaplanskyReciprocal A ((A - B) (kaplanskyReciprocal B x)) -
        (kaplanskyReciprocal A * A) ((A - B) (B (kaplanskyReciprocal B x))) := by
    simp only [mul_apply_eq_comp, sub_apply, map_sub]
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact (le_opNorm _ _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (kaplanskyReciprocal_norm_le A) (norm_nonneg _))
  · exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (by simpa only [(kaplanskyReciprocal_commute A).eq] using
        kaplanskyReciprocal_mul_norm_le A hA) (norm_nonneg _))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SelfAdjointStrongDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selfadjoint strong density in the bicommutant. The real orbit is tested
against its orthogonal complement; adjoints only occur in scalar products. -/
noncomputable section
namespace KadisonSimilarity
open Filter ContinuousLinearMap
open scoped Topology BigOperators

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype ι]

def symmetrize (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 / 2 : ℝ) • (A + star A)

theorem symmetrize_selfAdjoint (A : H →L[ℂ] H) :
    IsSelfAdjoint (symmetrize A) := (IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.add_star_self A)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_KaplanskySelfAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selfadjoint unit ball of the source algebra is strongly dense in
the selfadjoint unit ball of the represented bicommutant. -/
noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem lift_selfAdjoint_range (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (b : σ.range) (hb : IsSelfAdjoint b.val) :
    ∃ a : A, IsSelfAdjoint a ∧ σ a = b.val := by
  obtain ⟨c, hc⟩ := b.property
  change σ c = b.val at hc
  refine ⟨(1 / 2 : ℝ) • (c + star c),
    (IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.add_star_self c), ?_⟩
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_add, map_star, hc, hb.star_eq]
  norm_num only [map_div₀, map_one]
  module

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ScalarKaplansky
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-test-vector specialization of matrix Kaplansky density and
C*-quotient norm lifting is enough for the scalar commutator closure used
in the final derivation and separability reductions. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Blackadar, I.9.1.3, specialized to two vectors, followed by quotient norm
lifting. This precise published input contains no commutator estimate. -/
def TwoVectorKaplanskyInput (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (P : VonNeumannAlgebra H) : Prop :=
  ∀ b ∈ P, ∀ x y : H, ∀ ε : ℝ, 0 < ε → ∃ a : A,
    ‖a‖ ≤ ‖b‖ + ε ∧ ‖σ a x - b x‖ ≤ ε ∧ ‖σ a y - b y‖ ≤ ε

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixVonNeumannRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete von Neumann algebra of finite operator matrices

The commutant of the diagonally amplified commutant consists exactly of
operator matrices with entries in the original von Neumann algebra. This
constructs the normal matrix realization used by spectral rounding.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Represented
variable {A : Type*} [CStarAlgebra A]

/-- Taking the scalar bicommutant does not change its commutant. -/
theorem mem_representation_commutant_iff (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (B : H →L[ℂ] H) :
    B ∈ (representationVonNeumannAlgebra σ).commutant ↔
      B ∈ Set.centralizer (σ.range : Set (H →L[ℂ] H)) := by
  change B ∈ (starSubalgebraCommutant σ.range).commutant.commutant ↔ _
  rw [VonNeumannAlgebra.commutant_commutant]
  rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]


end Represented

section Concrete
variable (P : VonNeumannAlgebra H)

theorem subtype_range_eq : P.toStarSubalgebra.subtype.range = P.toStarSubalgebra := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

end Concrete
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-operator compactness of a norm ball, obtained from compact scalar
matrix-coefficient discs and the Hilbert-space representation of bounded forms. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Algebraic identities for a matrix coefficient function, conjugate-linear
in the operator's argument and linear in the test vector. -/
def IsOperatorForm (f : H → H → ℂ) : Prop :=
  (∀ x y z, f (x + y) z = f x z + f y z) ∧
  (∀ c x y, f (c • x) y = star c * f x y) ∧
  (∀ x y z, f x (y + z) = f x y + f x z) ∧
  (∀ c x y, f x (c • y) = c * f x y)

def operatorFormLinear (f : H → H → ℂ) (hf : IsOperatorForm f) :
    H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := f x
      map_add' := hf.2.2.1 x
      map_smul' := fun c y => hf.2.2.2 c x y }
  map_add' x y := by ext z; exact hf.1 x y z
  map_smul' c x := by ext y; exact hf.2.1 c x y

/-- Reconstruct an operator from a bounded sesquilinear matrix coefficient. -/
def operatorOfForm (f : H → H → ℂ) (hf : IsOperatorForm f) (R : ℝ)
    (hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖) : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin
    ((operatorFormLinear f hf).mkContinuous₂ R hb)

@[simp] theorem operatorOfForm_inner (f : H → H → ℂ) (hf : IsOperatorForm f) (R : ℝ)
    (hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖) (x y : H) :
    inner ℂ (operatorOfForm f hf R hb x) y = f x y := by
  apply InnerProductSpace.continuousLinearMapOfBilin_apply

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SeparableContractionTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable weak-operator contraction tests

On a separable Hilbert space, the weak-operator unit ball embeds in a countable
product of copies of `ℂ`, by its coefficients on a dense sequence of vectors.
Compactness makes this an embedding. Thus each von Neumann algebra has a
countable weakly dense family of contractions.
-/

noncomputable section

namespace KadisonSimilarity

open ContinuousLinearMapWOT
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- The operator unit ball, with the topology induced by the weak-operator
topology. -/
abbrev WeakOperatorUnitBall (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] :=
  {T : H →WOT[ℂ] H // ‖toCLM T‖ ≤ 1}

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DenseLinearOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Operators from dense additive column data

Bounded additive data on a dense subgroup extends by uniform continuity.
Compatibility with multiplication by `i` makes the extension complex linear.
Only a countable dense subgroup is needed for the later AE construction.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology Pointwise NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace F] in
theorem denseAdditive_uniformContinuous (S : AddSubgroup E)
    (f : S →+ F) (C : ℝ≥0) (hnorm : ∀ x : S, ‖f x‖ ≤ C * ‖x‖) :
    UniformContinuous f :=
  (AddMonoidHomClass.lipschitz_of_bound f C hnorm).uniformContinuous

/-- The additive extension of bounded data from a dense subgroup. -/
def denseAdditiveExtension (S : AddSubgroup E) (hdense : Dense (S : Set E))
    (f : S →+ F) (C : ℝ≥0) (hnorm : ∀ x : S, ‖f x‖ ≤ C * ‖x‖) : E →+ F where
  toFun := (isUniformEmbedding_subtype_val.isUniformInducing.isDenseInducing
    hdense.denseRange_val).extend f
  map_zero' := by
    convert! IsDenseInducing.extend_eq
      (isUniformEmbedding_subtype_val.isUniformInducing.isDenseInducing hdense.denseRange_val)
      (denseAdditive_uniformContinuous S f C hnorm).continuous (0 : S) using 1
    all_goals try with_reducible_and_instances rfl
    exact f.map_zero.symm
  map_add' := by
    have hc := (uniformContinuous_uniformly_extend
      isUniformEmbedding_subtype_val.isUniformInducing hdense.denseRange_val
      (denseAdditive_uniformContinuous S f C hnorm)).continuous
    refine fun x y => hdense.denseRange_val.induction_on₂ ?_ (fun a b => ?_) x y
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · rw [← AddSubgroup.coe_add]
      simp only [IsDenseInducing.extend_eq _
        (denseAdditive_uniformContinuous S f C hnorm).continuous, map_add]

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
theorem denseAdditiveExtension_continuous (S : AddSubgroup E)
    (hdense : Dense (S : Set E)) (f : S →+ F) (C : ℝ≥0)
    (hnorm : ∀ x : S, ‖f x‖ ≤ C * ‖x‖) :
    Continuous (denseAdditiveExtension S hdense f C hnorm) :=
  (uniformContinuous_uniformly_extend
    isUniformEmbedding_subtype_val.isUniformInducing hdense.denseRange_val
    (denseAdditive_uniformContinuous S f C hnorm)).continuous

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
@[simp] theorem denseAdditiveExtension_apply (S : AddSubgroup E)
    (hdense : Dense (S : Set E)) (f : S →+ F) (C : ℝ≥0)
    (hnorm : ∀ x : S, ‖f x‖ ≤ C * ‖x‖) (x : S) :
    denseAdditiveExtension S hdense f C hnorm x = f x :=
  IsDenseInducing.extend_eq
    (isUniformEmbedding_subtype_val.isUniformInducing.isDenseInducing hdense.denseRange_val)
    (denseAdditive_uniformContinuous S f C hnorm).continuous x

omit [CompleteSpace F] in
/-- A continuous additive map that commutes with `i` is complex linear. -/
def continuousAdditiveToComplexLinear (f : E →+ F) (hf : Continuous f)
    (hI : ∀ x, f (Complex.I • x) = Complex.I • f x) : E →L[ℂ] F where
  toFun := f
  map_add' := f.map_add
  map_smul' z x := by
    change f (z • x) = z • f x
    have hr (r : ℝ) (y : E) : f ((r : ℂ) • y) = (r : ℂ) • f y := by
      calc
        f ((r : ℂ) • y) = f (r • y) :=
          congrArg f (RCLike.real_smul_eq_coe_smul (K := ℂ) r y).symm
        _ = r • f y := map_real_smul f hf r y
        _ = (r : ℂ) • f y := RCLike.real_smul_eq_coe_smul (K := ℂ) r (f y)
    rw [← Complex.re_add_im z]
    simp only [add_smul, map_add, mul_smul, hr, hI]
  cont := hf

/-- The bounded dense-subgroup data gives an operator of the same norm bound. -/
theorem exists_operator_of_dense_additive
    (S : AddSubgroup E) (hdense : Dense (S : Set E))
    (hIS : ∀ x ∈ S, Complex.I • x ∈ S) (f : S →+ F) (C : ℝ≥0)
    (hnorm : ∀ x : S, ‖f x‖ ≤ C * ‖x‖)
    (hI : ∀ x : S, f ⟨Complex.I • x.val, hIS x.val x.property⟩ = Complex.I • f x) :
    ∃ T : E →L[ℂ] F, ‖T‖ ≤ C ∧ ∀ x : S, T x = f x := by
  let g := denseAdditiveExtension S hdense f C hnorm
  have hg : Continuous g := denseAdditiveExtension_continuous S hdense f C hnorm
  have hext : ∀ x : S, g x = f x := denseAdditiveExtension_apply S hdense f C hnorm
  have hgI : ∀ x, g (Complex.I • x) = Complex.I • g x := by
    intro x
    refine hdense.denseRange_val.induction_on
      (p := fun y => g (Complex.I • y) = Complex.I • g y) x
      (isClosed_eq (hg.comp (continuous_const.smul continuous_id))
        (continuous_const.smul hg)) ?_
    intro y
    calc
      g (Complex.I • (y : E)) = f ⟨Complex.I • y.val, hIS y.val y.property⟩ :=
        hext ⟨Complex.I • y.val, hIS y.val y.property⟩
      _ = Complex.I • f y := hI y
      _ = Complex.I • g (y : E) := congrArg (Complex.I • ·) (hext y).symm
  let T := continuousAdditiveToComplexLinear g hg hgI
  refine ⟨T, ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg ?_, hext⟩
  intro x
  refine hdense.denseRange_val.induction_on
    (p := fun y => ‖T y‖ ≤ C * ‖y‖) x
    (isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro y
  change ‖g (y : E)‖ ≤ C * ‖(y : E)‖
  rw [hext y]
  exact hnorm y

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_AEColumnOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering fiber operators from almost-everywhere column data

The common conull set is obtained from countably many additive and
`i`-linearity identities. The extension has the original norm bound;
each fixed column agrees almost everywhere with the original data.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, NormedSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

theorem ae_exists_operator_of_countable_additive
    (S : AddSubgroup E) [Countable S] (hdense : Dense (S : Set E))
    (hIS : ∀ x ∈ S, Complex.I • x ∈ S) (C : ℝ≥0)
    (f : ∀ _x : S, ∀ a, K a)
    (hzero : ∀ᵐ a ∂μ, f 0 a = 0)
    (hadd : ∀ x y : S, ∀ᵐ a ∂μ, f (x + y) a = f x a + f y a)
    (hI : ∀ x : S, ∀ᵐ a ∂μ,
      f ⟨Complex.I • x.val, hIS x.val x.property⟩ a = Complex.I • f x a)
    (hnorm : ∀ x : S, ∀ᵐ a ∂μ, ‖f x a‖ ≤ C * ‖x‖) :
    ∀ᵐ a ∂μ, ∃ T : E →L[ℂ] K a, ‖T‖ ≤ C ∧ ∀ x : S, T x = f x a := by
  have ha : ∀ᵐ a ∂μ, ∀ x y : S, f (x + y) a = f x a + f y a :=
    eventually_countable_forall.mpr fun x => eventually_countable_forall.mpr (hadd x)
  have hi : ∀ᵐ a ∂μ, ∀ x : S,
      f ⟨Complex.I • x.val, hIS x.val x.property⟩ a = Complex.I • f x a :=
    eventually_countable_forall.mpr hI
  have hn : ∀ᵐ a ∂μ, ∀ x : S, ‖f x a‖ ≤ C * ‖x‖ :=
    eventually_countable_forall.mpr hnorm
  filter_upwards [hzero, ha, hi, hn] with a hz ha hi hn
  let g : S →+ K a := { toFun := fun x => f x a, map_zero' := hz, map_add' := ha }
  exact exists_operator_of_dense_additive S hdense hIS g C hn hi

omit [∀ a, CompleteSpace (K a)] in
theorem ae_columnOperator_agrees_at
    (S : AddSubgroup E) (hdense : Dense (S : Set E)) (C : ℝ≥0)
    (f : ∀ _x : E, ∀ a, K a)
    (hsub : ∀ x y : E, ∀ᵐ a ∂μ, f (x - y) a = f x a - f y a)
    (hnorm : ∀ x : E, ∀ᵐ a ∂μ, ‖f x a‖ ≤ C * ‖x‖) (x : E) :
    ∀ᵐ a ∂μ, ∀ T : E →L[ℂ] K a, ‖T‖ ≤ C →
      (∀ y : S, T y = f y a) → T x = f x a := by
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense x)
  have hs : ∀ᵐ a ∂μ, ∀ n : ℕ, f (x - y n) a = f x a - f (y n) a :=
    eventually_countable_forall.mpr (fun n => hsub x (y n))
  have hn : ∀ᵐ a ∂μ, ∀ n : ℕ, ‖f (x - y n) a‖ ≤ C * ‖x - y n‖ :=
    eventually_countable_forall.mpr (fun n => hnorm (x - y n))
  filter_upwards [hs, hn] with a hs hn
  intro T hT hext
  have hbound (n : ℕ) : ‖T x - f x a‖ ≤ C * ‖x - y n‖ + C * ‖x - y n‖ := by
    calc
      _ ≤ ‖T x - T (y n)‖ + ‖T (y n) - f x a‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C * ‖x - y n‖ + C * ‖x - y n‖ := add_le_add
        (by
          rw [← map_sub]
          exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _)))
        (by
          rw [hext ⟨y n, hy n⟩, norm_sub_rev, ← hs n]
          exact hn n)
  have hzero : Tendsto (fun n => ‖x - y n‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub hlim).norm
  have hC := hzero.const_mul (C : ℝ)
  have hle : ‖T x - f x a‖ ≤ 0 := by
    simpa only [mul_zero, zero_add] using ge_of_tendsto' (hC.add hC) hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DecomposableColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The columns of an operator commuting with localization are pointwise
bounded by its operator norm. No essential-norm formula is assumed. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped ENNReal Topology

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem indicatorConstL2_norm_sq (s : Set Ω) (hs : MeasurableSet s) (x : H) :
    ‖indicatorConstLp 2 hs (measure_ne_top μ s) x‖ ^ 2 = ‖x‖ ^ 2 * μ.real s := by
  rw [l2_norm_sq_eq_integral]
  have heq : (fun a => ‖indicatorConstLp 2 hs (measure_ne_top μ s) x a‖ ^ 2) =ᵐ[μ]
      s.indicator (fun _ => ‖x‖ ^ 2) := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs)
      (hμs := measure_ne_top μ s) (c := x)] with a ha
    rw [ha]
    by_cases h : a ∈ s <;> simp [h]
  rw [integral_congr_ae heq, integral_indicator hs]
  simp [measureReal_def, mul_comm]

omit [CompleteSpace H] in
/-- Commutation with localization bounds each constant-vector column almost
 everywhere. The null set is allowed to depend on the chosen vector. -/
theorem decomposable_column_ae_bound
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hlocal : ∀ (s : Set Ω) (hs : MeasurableSet s) (x : H),
      T (indicatorConstLp 2 hs (measure_ne_top μ s) x) =ᵐ[μ]
        s.indicator (T (Lp.const 2 μ x)))
    (x : H) :
    ∀ᵐ a ∂μ, ‖T (Lp.const 2 μ x) a‖ ≤ ‖T‖ * ‖x‖ := by
  apply ae_norm_le_of_localized_square_bound μ (T (Lp.const 2 μ x)) (C := ‖T‖ * ‖x‖)
    (mul_nonneg (norm_nonneg T) (norm_nonneg x))
  intro s hs
  let f := indicatorConstLp 2 hs (measure_ne_top μ s) x
  refine ⟨T f, hlocal s hs x, ?_⟩
  calc
    ‖T f‖ ^ 2 ≤ (‖T‖ * ‖f‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (T.le_opNorm f)
    _ = (‖T‖ * ‖x‖) ^ 2 * μ.real s := by
      rw [mul_pow, indicatorConstL2_norm_sq]
      ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_L2Localization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal indicator projections on the actual L² space and the pointwise
column bound for every operator in their commutant. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped ENNReal Topology

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (s : Set Ω) (hs : MeasurableSet s)

def l2Localize (f : Lp H 2 μ) : Lp H 2 μ :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator f)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem l2Localize_ae (f : Lp H 2 μ) :
    l2Localize μ s hs f =ᵐ[μ] s.indicator f := MemLp.coeFn_toLp _

def l2LocalizationLinear : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ where
  toFun := l2Localize μ s hs
  map_add' f g := by
    apply Lp.ext
    filter_upwards [l2Localize_ae μ s hs (f + g), l2Localize_ae μ s hs f,
      l2Localize_ae μ s hs g, Lp.coeFn_add f g,
      Lp.coeFn_add (l2Localize μ s hs f) (l2Localize μ s hs g)] with a hfg hf hg hadd hout
    rw [hfg, hout]
    simp only [Pi.add_apply]
    rw [hf, hg]
    by_cases h : a ∈ s
    · simp only [Set.indicator_of_mem h]
      exact hadd
    · simp [h]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [l2Localize_ae μ s hs (c • f), l2Localize_ae μ s hs f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (l2Localize μ s hs f)] with a hcf hf hsmul hout
    change l2Localize μ s hs (c • f) a = (c • l2Localize μ s hs f) a
    rw [hcf, hout]
    simp only [Pi.smul_apply]
    rw [hf]
    by_cases h : a ∈ s <;> simp [h, hsmul]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem norm_l2Localize_le (f : Lp H 2 μ) : ‖l2Localize μ s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [l2Localize_ae μ s hs f] with a ha
  rw [ha]
  by_cases h : a ∈ s <;> simp [h]

def l2Localization : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  (l2LocalizationLinear μ s hs).mkContinuous 1 (fun f => by
    change ‖l2Localize μ s hs f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_l2Localize_le μ s hs f)

omit [CompleteSpace H] in
theorem l2Localization_ae (f : Lp H 2 μ) :
    l2Localization μ s hs f =ᵐ[μ] s.indicator f := l2Localize_ae μ s hs f

variable [IsFiniteMeasure μ]

omit [CompleteSpace H] in
theorem l2Localization_const (x : H) :
    l2Localization μ s hs (Lp.const 2 μ x) = indicatorConstLp 2 hs (measure_ne_top μ s) x := by
  apply Lp.ext
  filter_upwards [l2Localization_ae μ s hs (Lp.const 2 μ x), Lp.coeFn_const 2 μ x,
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := x)]
    with a hloc hc hi
  rw [hloc, hi]
  by_cases h : a ∈ s
  · simp only [Set.indicator_of_mem h]
    exact hc
  · simp [h]

omit [CompleteSpace H] in
/-- A genuine diagonal-commuting operator has pointwise bounded columns. -/
theorem diagonal_commutant_column_bound
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T)
    (x : H) : ∀ᵐ a ∂μ, ‖T (Lp.const 2 μ x) a‖ ≤ ‖T‖ * ‖x‖ := by
  apply decomposable_column_ae_bound μ T ?_ x
  intro r hr y
  have h := congrArg (fun S : Lp H 2 μ →L[ℂ] Lp H 2 μ => S (Lp.const 2 μ y)) (hT r hr)
  change T (l2Localization μ r hr (Lp.const 2 μ y)) =
    l2Localization μ r hr (T (Lp.const 2 μ y)) at h
  rw [l2Localization_const] at h
  rw [h]
  exact l2Localization_ae μ r hr (T (Lp.const 2 μ y))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFieldAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebraic laws for fields of diagonal-commuting operators

The fields are constructed from the actual operators. Their algebraic laws
hold almost everywhere, by the pointwise action on all L² vectors and a
countable dense family of constant columns.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

omit [IsFiniteMeasure μ] [CompleteSpace H] in
/-- Countably many dense test vectors suffice for equality of operator
fields almost everywhere. -/
theorem ae_operator_eq_of_forall_vectors
    (R S : Ω → H →L[ℂ] H)
    (h : ∀ x : H, ∀ᵐ a ∂μ, R a x = S a x) : ∀ᵐ a ∂μ, R a = S a := by
  have hall : ∀ᵐ a ∂μ, ∀ n : ℕ,
      R a (TopologicalSpace.denseSeq H n) = S a (TopologicalSpace.denseSeq H n) :=
    eventually_countable_forall.mpr fun n => h (TopologicalSpace.denseSeq H n)
  filter_upwards [hall] with a ha
  apply DFunLike.coe_injective
  exact (TopologicalSpace.denseRange_denseSeq H).equalizer
    (R a).continuous (S a).continuous (funext ha)

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The all-vector action supplies the constant-column formula. -/
theorem pointwise_action_column
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a)) (x : H) :
    ∀ᵐ a ∂μ, T (Lp.const 2 μ x) a = R a x := by
  filter_upwards [hR (Lp.const 2 μ x), Lp.coeFn_const 2 μ x] with a ha hc
  simpa only [hc, Function.const_apply] using ha

omit [CompleteSpace H] in
/-- Composition uses the all-L² action on the inner operator's column. -/
theorem pointwise_field_mul
    (T S : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R Q U : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hQ : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, S f a = Q a (f a))
    (hU : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (T * S) f a = U a (f a)) :
    ∀ᵐ a ∂μ, U a = R a * Q a := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [hR (S (Lp.const 2 μ x)), pointwise_action_column μ S Q hQ x,
    pointwise_action_column μ (T * S) U hU x] with a hr hq hu
  simpa only [mul_apply_eq_comp, hr, hq] using hu.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_DiagonalMatrixNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix norms of the reconstructed diagonal representations

Finite L² sums are identified isometrically with tuple-valued L². The
actual matrix action is pointwise under this identification, so its norm is
exactly the essential supremum of the fiber matrix norms.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A genuine pointwise operator automatically commutes with all measurable
localizations. -/
theorem pointwise_action_commutes_localization
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (s : Set Ω) (hs : MeasurableSet s) :
    T * l2Localization μ s hs = l2Localization μ s hs * T := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hR (l2Localization μ s hs f), hR f,
    l2Localization_ae μ s hs f, l2Localization_ae μ s hs (T f)] with a hl ht hf hout
  change T (l2Localization μ s hs f) a = l2Localization μ s hs (T f) a
  rw [hl, hout, hf]
  by_cases ha : a ∈ s
  · simpa only [Set.indicator_of_mem ha] using ht.symm
  · simp only [Set.indicator_of_notMem ha, map_zero]

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] in
/-- The field in any actual all-L² action has precisely the original
operator's scalar norm bounds. -/
theorem pointwise_field_norm_iff
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (C : ℝ) (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ᵐ a ∂μ, ‖R a‖ ≤ C := by
  constructor
  · intro hTC
    have htest (x : H) : ∀ᵐ a ∂μ, ‖R a x‖ ≤ C * ‖x‖ := by
      have hb := diagonal_commutant_column_bound μ T
        (pointwise_action_commutes_localization μ T R hR) x
      filter_upwards [hb, pointwise_action_column μ T R hR x] with a ha he
      rw [he] at ha
      exact ha.trans (mul_le_mul_of_nonneg_right hTC (norm_nonneg x))
    have hall : ∀ᵐ a ∂μ, ∀ n : ℕ,
        ‖R a (TopologicalSpace.denseSeq H n)‖ ≤ C * ‖TopologicalSpace.denseSeq H n‖ :=
      eventually_countable_forall.mpr fun n => htest (TopologicalSpace.denseSeq H n)
    filter_upwards [hall] with a ha
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro x
    exact (TopologicalSpace.denseRange_denseSeq H).induction_on x
      (isClosed_le (by fun_prop) (by fun_prop)) ha
  · intro hb
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro f
    have hglobal : ∀ᵐ a ∂μ, ‖T f a‖ ≤ C * ‖f a‖ := by
      filter_upwards [hR f, hb] with a ha hn
      rw [ha]
      exact ((R a).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    calc
      ‖T f‖ ≤ ‖(C : ℂ) • f‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [hglobal, Lp.coeFn_smul (C : ℂ) f] with a ha he
        rw [he, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
        exact ha
      _ = C * ‖f‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProperlyInfiniteEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The properly infinite commutator estimate. Internal orthogonal isometries
supply the row, and Dickson supplies its actual commutator error bounds. -/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A von Neumann algebra is closed in the operator norm. -/
instance vonNeumannAlgebra_isClosed (P : VonNeumannAlgebra H) :
    IsClosed (P : Set (H →L[ℂ] H)) := by
  change IsClosed P.carrier
  rw [← P.centralizer_centralizer']
  exact Set.isClosed_centralizer _

instance vonNeumannAlgebra_smulMemClass :
    SMulMemClass (VonNeumannAlgebra H) ℂ (H →L[ℂ] H) where
  smul_mem {s} c {_x} hx := s.toStarSubalgebra.smul_mem hx c

def vonNeumannRepresentation (P : VonNeumannAlgebra H) : P →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  P.toStarSubalgebra.subtype

/-- Existence of finite families of orthogonal isometries. For a properly
infinite algebra this is supplied by its projection classification. -/
def HasInternalIsometryRows (P : VonNeumannAlgebra H) : Prop :=
  ∀ n : ℕ, ∃ v : Fin n → P, ∀ i j, star (v i) * v j = if i = j then 1 else 0

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_DicksonRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivation of the norm-two row estimate from the exact little
Grothendieck specialization in Haagerup (1983), Theorem 3.2, as quoted in
Dickson (2014), Lemmas 2.8–2.9, equations (18)–(22). -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Subnormalized states also cover the zero algebra. Only their values on
positive squares and their mass bound are used in the application. -/
def LittleGrothendieckInput (A H : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Prop :=
  ∀ T : A →L[ℂ] H, ∃ f g : A →ₚ[ℂ] ℂ,
    (f 1).re ≤ 1 ∧ (g 1).re ≤ 1 ∧
    ∀ a, ‖T a‖ ^ 2 ≤ ‖T‖ ^ 2 * ((f (star a * a)).re + (g (a * star a)).re)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralCornerWords
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The algebraic even-word step in the dihedral corner argument.
Corner letters absorb the reflection on the right, leaving an explicitly
alternating centered word in the original free factors. -/

noncomputable section
namespace KadisonSimilarity
namespace DihedralCornerWords

variable {R : Type*}

/-- The alternating word containing `n` copies of the pair `d,s`. -/
def pairLetters (d s : R) : ℕ → List R
  | 0 => []
  | n + 1 => d :: s :: pairLetters d s n

/-- A positive-power corner block, after absorbing its first reflection. -/
def blockLetters (d s a : R) (l : ℕ) : List R :=
  a :: s :: pairLetters d s (l - 1)

/-- Concatenate the explicitly alternating expansions of all corner blocks. -/
def productLetters (d s : R) (blocks : List (R × ℕ)) : List R :=
  blocks.flatMap fun b => blockLetters d s b.1 b.2

section Products
variable [Monoid R]

@[simp] theorem pairLetters_prod (d s : R) (n : ℕ) :
    (pairLetters d s n).prod = (d * s) ^ n := by
  induction n with
  | zero => simp [pairLetters]
  | succ n ih =>
    simp only [pairLetters, List.prod_cons, ih, pow_succ', mul_assoc]

end Products

end DihedralCornerWords
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialCompression
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense tracial vectors determine the word-level operator compression.
In particular the matrix-entry identity is proved from the trace and the
two-sided expectation identity, rather than supplied as an operator hypothesis. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {R : Type*} [Ring R] [StarRing R]

/-- Star reverses the exponent of a unitary, in the units convention used in
the dihedral word calculation. -/
theorem star_unitary_zpow (w : Rˣ) (hw : star w = w⁻¹) (j : ℤ) :
    star ((↑(w ^ j) : R)) = (↑(w ^ (-j)) : R) := by
  rw [← Units.coe_star, star_zpow, hw, inv_zpow, zpow_neg]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralCornerDensity
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate L²-continuity extends the positive-power corner trace tests.
Only density of their linear span in the centered corner is needed;
no uniform bound on approximants is imposed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DihedralCornerWords

/-- Ordered alternating products, with the first list supplying fixed
left letters and the second list supplying the variable right letters. -/
def alternatingProduct : List P → List P → P
  | a :: as, x :: xs => a * x * alternatingProduct as xs
  | _, _ => 1

@[simp] theorem alternatingProduct_nil (xs : List P) : alternatingProduct [] xs = 1 := rfl
@[simp] theorem alternatingProduct_cons (a x : P) (as xs : List P) :
    alternatingProduct (a :: as) (x :: xs) = a * x * alternatingProduct as xs := rfl

/-- The positive compressed rotation powers spanning the centered dihedral corner. -/
def positiveCornerPowers (p w : P) : Set P :=
  Set.range fun n : {n : ℕ // 0 < n} => p * w ^ n.val * p

end DihedralCornerWords
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralWordAlgebra
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary dihedral word span is a unital star subalgebra. This
reduces its L²-density to density of the algebra generated by the two
symmetries, without assuming a normal-form density statement. -/

noncomputable section
namespace KadisonSimilarity
namespace DihedralWordAlgebra

section Group
variable {G : Type*} [Group G]

/-- Moving a reflection through any integer rotation power. -/
theorem reflection_zpow (d w : G) (hc : d * w = w⁻¹ * d) (l : ℤ) :
    d * w ^ l = w ^ (-l) * d := by
  have h := (show SemiconjBy d w w⁻¹ from hc).zpow_right l
  simpa only [inv_zpow, zpow_neg] using h.eq

/-- The rotation exponent changes sign when its left factor is a reflection. -/
theorem reflection_rotation (d w : G) (hc : d * w = w⁻¹ * d) (l m : ℤ) :
    (w ^ l * d) * w ^ m = w ^ (l - m) * d := by
  rw [mul_assoc, reflection_zpow d w hc, ← mul_assoc, ← zpow_add]
  simp only [sub_eq_add_neg]

/-- The product of two reflection-coset words is a rotation. -/
theorem reflection_reflection (d w : G) (hd : d * d = 1)
    (hc : d * w = w⁻¹ * d) (l m : ℤ) :
    (w ^ l * d) * (w ^ m * d) = w ^ (l - m) := by
  rw [← mul_assoc, reflection_rotation d w hc, mul_assoc, hd, mul_one]

end Group

variable {P : Type*} [CStarAlgebra P]

/-- Rotation words and reflection-coset words, as elements of the algebra. -/
def wordSet (d w : Pˣ) : Set P :=
  Set.range (fun l : ℤ => (↑(w ^ l) : P)) ∪
    Set.range (fun l : ℤ => (↑(w ^ l) : P) * (d : P))

/-- Normal forms are closed under multiplication. -/
theorem wordSet_mul (d w : Pˣ) (hd : d * d = 1) (hc : d * w = w⁻¹ * d)
    {a b : P} (ha : a ∈ wordSet d w) (hb : b ∈ wordSet d w) : a * b ∈ wordSet d w := by
  rcases ha with ⟨l, rfl⟩ | ⟨l, rfl⟩ <;> rcases hb with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    refine ⟨l + m, ?_⟩
    dsimp only
    rw [zpow_add, Units.val_mul]
  · right
    refine ⟨l + m, ?_⟩
    dsimp only
    rw [zpow_add, Units.val_mul, mul_assoc]
  · right
    refine ⟨l - m, ?_⟩
    have h := congrArg (fun g : Pˣ => (g : P)) (reflection_rotation d w hc l m)
    simpa only [Units.val_mul] using h.symm
  · left
    refine ⟨l - m, ?_⟩
    have h := congrArg (fun g : Pˣ => (g : P)) (reflection_reflection d w hd hc l m)
    simpa only [Units.val_mul] using h.symm

/-- Taking adjoints preserves the two normal forms. -/
theorem wordSet_star (d w : Pˣ) (hc : d * w = w⁻¹ * d)
    (hdstar : star d = d) (hwstar : star w = w⁻¹)
    {a : P} (ha : a ∈ wordSet d w) : star a ∈ wordSet d w := by
  rcases ha with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · left
    exact ⟨-l, (star_unitary_zpow w hwstar l).symm⟩
  · right
    refine ⟨l, ?_⟩
    have hdval : star (d : P) = (d : P) := congrArg (fun g : Pˣ => (g : P)) hdstar
    rw [star_mul, hdval, star_unitary_zpow w hwstar]
    have h := congrArg (fun g : Pˣ => (g : P)) (reflection_zpow d w hc (-l))
    simpa only [Units.val_mul, neg_neg] using h.symm

/-- Bilinearity extends multiplication closure to the full linear span. -/
theorem span_mul (d w : Pˣ) (hd : d * d = 1) (hc : d * w = w⁻¹ * d)
    {a b : P} (ha : a ∈ Submodule.span ℂ (wordSet d w))
    (hb : b ∈ Submodule.span ℂ (wordSet d w)) :
    a * b ∈ Submodule.span ℂ (wordSet d w) := by
  let M := Submodule.span ℂ (wordSet d w)
  refine Submodule.span_induction₂ (p := fun a b _ _ => a * b ∈ M) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · intro a b ha hb
    exact Submodule.subset_span (wordSet_mul d w hd hc ha hb)
  · intro b _
    rw [zero_mul]
    exact M.zero_mem
  · intro a _
    rw [mul_zero]
    exact M.zero_mem
  · intro a b c _ _ _ ha hb
    rw [add_mul]
    exact M.add_mem ha hb
  · intro a b c _ _ _ hb hc
    rw [mul_add]
    exact M.add_mem hb hc
  · intro r a b _ _ h
    rw [smul_mul_assoc]
    exact M.smul_mem r h
  · intro r a b _ _ h
    rw [mul_smul_comm]
    exact M.smul_mem r h

/-- Conjugate linearity extends adjoint closure to the word span. -/
theorem span_star (d w : Pˣ) (hc : d * w = w⁻¹ * d)
    (hdstar : star d = d) (hwstar : star w = w⁻¹)
    {a : P} (ha : a ∈ Submodule.span ℂ (wordSet d w)) :
    star a ∈ Submodule.span ℂ (wordSet d w) := by
  let M := Submodule.span ℂ (wordSet d w)
  induction ha using Submodule.span_induction with
  | mem a ha => exact Submodule.subset_span (wordSet_star d w hc hdstar hwstar ha)
  | zero => simpa only [star_zero] using M.zero_mem
  | add a b _ _ ha hb => simpa only [star_add] using M.add_mem ha hb
  | smul r a _ ha => simpa only [star_smul] using M.smul_mem (star r) ha

/-- The span itself is the required unital star subalgebra. -/
def spanStarAlgebra (d w : Pˣ) (hd : d * d = 1) (hc : d * w = w⁻¹ * d)
    (hdstar : star d = d) (hwstar : star w = w⁻¹) : StarSubalgebra ℂ P where
  carrier := Submodule.span ℂ (wordSet d w)
  zero_mem' := Submodule.zero_mem _
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  one_mem' := Submodule.subset_span (Or.inl ⟨0, by simp⟩)
  mul_mem' := span_mul d w hd hc
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Or.inl ⟨0, by simp⟩))
  star_mem' := span_star d w hc hdstar hwstar

@[simp] theorem spanStarAlgebra_toSubmodule (d w : Pˣ) (hd : d * d = 1)
    (hc : d * w = w⁻¹ * d) (hdstar : star d = d) (hwstar : star w = w⁻¹) :
    (spanStarAlgebra d w hd hc hdstar hwstar).toSubalgebra.toSubmodule =
      Submodule.span ℂ (wordSet d w) := rfl

end DihedralWordAlgebra
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointDensity
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Density for unrestricted endpoints and centered tensor letters

The two endpoint variables and the finitely many centered letters have different
ambient Hilbert spaces. Nested dense matrix stages nevertheless give a common
stage, so their continuous coefficient identities extend together.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct
universe u

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The pair of endpoint letters and all centered tail letters. -/
abbrev EndpointLetters (E F : Type u) (k l : ℕ) :=
  (Bool → E) × (Fin k ⊕ Fin l → F)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixUnitCoordinates
attribute [-instance] _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hilbert coordinates from a finite orthogonal family of corner inclusions

The two matrix-unit equations construct the coordinate unitaries used in the
full-column theorem. The action of an arbitrary operator is then its actual
matrix of corner compressions.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMap

variable {F H : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The elementary operator equations supplied by a complete finite system of
matrix-unit columns. -/
structure FiniteOrthogonalColumns (F H : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) where
  inclusion : Fin n → F →L[ℂ] H
  adjoint_comp : ∀ i j, (inclusion i).adjoint.comp (inclusion j) =
    if i = j then ContinuousLinearMap.id ℂ F else 0
  resolution : ∑ i, (inclusion i).comp (inclusion i).adjoint = ContinuousLinearMap.id ℂ H

namespace FiniteOrthogonalColumns

variable {n : ℕ} (U : FiniteOrthogonalColumns F H n)

@[simp] theorem adjoint_inclusion_apply (i j : Fin n) (x : F) :
    (U.inclusion i).adjoint (U.inclusion j x) = if i = j then x else 0 := by
  have h := congrArg (fun T : F →L[ℂ] F => T x) (U.adjoint_comp i j)
  by_cases hij : i = j
  · simpa [hij] using h
  · simpa [hij] using h

end FiniteOrthogonalColumns

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixCornerFrames
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite family of partial isometries with common initial projection
constructs the actual Hilbert coordinate frame of a corner. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- An algebraic partial isometry is unchanged by its initial projection. -/
theorem mul_initial_projection (e v : P) (he : IsStarProjection e) (hv : star v * v = e) :
    v * e = v := by
  apply sub_eq_zero.mp
  apply (CStarRing.star_mul_self_eq_zero_iff (v * e - v)).mp
  calc
    star (v * e - v) * (v * e - v) =
        e * (star v * v) * e - e * (star v * v) - (star v * v) * e + star v * v := by
      rw [star_sub, star_mul, he.isSelfAdjoint.star_eq]
      noncomm_ring
    _ = 0 := by simp only [hv, he.isIdempotentElem.eq]; abel

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialPropagationEndgame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagation on the entire base Hilbert space. Polar decomposition is used
only for the right support of the bounded vector qv; density handles all other
base vectors. The full-column bound is derived from the cited cyclic inputs. -/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The application-specific consequence of support projections and polar
 decomposition (Blackadar, I.5.2.1--3): the right support of qv has trace at most
that of its containing left projection q. -/
def TracialRightSupportInput (τ : P → ℝ) (q : P) (A : StarSubalgebra ℂ P) : Prop :=
  ∀ v : A, ∃ r : P, IsStarProjection r ∧ τ r ≤ τ q ∧ (q * (v : P)) * r = q * (v : P)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialProjectionLifting
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection lifting in a tracial ultrapower, using only the scalar
spectral rounding estimate. The subsequent trace cutoff uses the strict
gap between the desired trace and the coordinate trace bound. -/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- Blackadar, I.6.2.4 and I.9.2.1(iv): bounded Borel functional calculus
with the cutoff at 1/2. The scalar estimate is
`|x - 1_[1/2,∞)(x)| ≤ 2 |x²-x|`. This predicate is used only for the
fixed finite von Neumann algebra, not for arbitrary C-star algebras. -/
def SpectralProjectionRoundingInput : Prop :=
  ∀ a : A, IsSelfAdjoint a → ∃ p : A, IsStarProjection p ∧
    ‖τ.toPreGNS (p - a)‖ ≤ 2 * ‖τ.toPreGNS (a * a - a)‖

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralRoundingDischarge
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-half spectral rounding inequality

The cutoff is the support of the positive part of `2a-1`.  Its polynomial
order inequality implies the required L² inequality for every positive
functional on a concrete von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vonNeumann_closed (P : VonNeumannAlgebra H) :
    IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed P.carrier
  rw [← P.centralizer_centralizer']
  exact Set.isClosed_centralizer _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialInputTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of the discharged tracial inputs

These are coordinate changes through actual star algebra equivalences.
The concrete normal representation is retained as algebraic data; neither
rounding nor existence of a right support is assumed in the concrete model.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

section Equivalence
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Trace preservation is exactly the norm preservation needed for rounding. -/
theorem preGNS_norm_map_eq (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (e : A →⋆ₐ[ℂ] B) (hτ : ∀ a, τB (e a) = τA a) (a : A) :
    ‖τB.toPreGNS (e a)‖ = ‖τA.toPreGNS a‖ := by
  simp only [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [← map_star e, ← map_mul e, hτ]

end Equivalence

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordPrefixRealization
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed alternating prefixes in propagation are isometries on the
appropriate reduced-word subspace. This follows by iterating the two
one-letter Fock creation formulas. Their global operator bounds follow from
the algebraic symmetry and normalized corner-unitary relations. -/

noncomputable section
namespace KadisonSimilarity

section AlgebraBounds

variable {P : Type*} [CStarAlgebra P]

/-- A unitary has norm at most one, including in the zero C-star algebra. -/
theorem norm_unitary_le_one (u : unitary P) : ‖(u : P)‖ ≤ 1 := by
  have h : ‖(u : P)‖ = ‖(1 : P)‖ := by
    simpa only [mul_one] using CStarRing.norm_coe_unitary_mul u (1 : P)
  rw [h]
  exact IsStarProjection.norm_le 1 (.one P)

/-- A selfadjoint involution is contractive without a nontriviality
assumption on its C-star algebra. -/
theorem norm_symmetry_le_one (s : P) (hstar : star s = s) (hsq : s * s = 1) :
    ‖s‖ ≤ 1 :=
  norm_unitary_le_one ⟨s, ⟨by rw [hstar, hsq], by rw [hstar, hsq]⟩⟩

end AlgebraBounds

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_GeneratedCompression
attribute [-instance] _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction to the C-star algebra generated by the two free factors.
The compression model is used on this cyclic generated representation,
and faithfulness transfers its norm estimate to the ambient algebra. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance isClosed_comap_subtype (A S : StarSubalgebra ℂ P) [IsClosed (A : Set P)] :
    IsClosed (A.comap S.subtype : Set S) :=
  (show IsClosed (A : Set P) from inferInstance).preimage continuous_subtype_val

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorIntegral
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak operator integrals built from scalar integrals. In particular this
permits averaging a strongly continuous unitary action without assuming
continuity in the operator norm. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Integrability of the scalar matrix coefficients of an operator field. -/
def WeaklyIntegrable (A : X → H →L[ℂ] H) : Prop :=
  ∀ x y : H, Integrable (fun g => inner ℂ (A g x) y) μ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixTower
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tracial matrix towers from actual embedded matrix algebras

The matrix-stage geometry is constructed from nested trace-preserving matrix
embeddings in a tracial Hilbert representation. Density of centered trace-zero
stages is derived by orthogonal projection from density of the full stages.
-/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- A real orthonormal sequence expressed entirely in the tracial algebra.
Its Hilbert realization is derived below. -/
structure RealTracialSequence (τ : R →ₗ[ℂ] ℂ) where
  vector : ℕ → R
  trace_zero : ∀ n, τ (vector n) = 0
  selfadjoint : ∀ n, star (vector n) = vector n
  inner : ∀ i j, τ (star (vector i) * vector j) = if i = j then 1 else 0

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_CofinalMatrixTowers
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word degrees are fixed before the matrix stage is chosen. Cofinal tails
let each degree start in its own stable range; no single finite stage must
accommodate every number of tensor slots. -/

noncomputable section
namespace KadisonSimilarity

open Filter

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

theorem iUnion_nat_tail {X : Type*} (S : ℕ → Set X) (hS : Monotone S) (b : ℕ) :
    (⋃ s, S (b + s)) = ⋃ s, S s := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_mono' (fun s => ⟨b + s, Set.Subset.refl _⟩)
  · apply Set.iUnion_subset
    intro s
    exact (hS (Nat.le_add_left s b)).trans (Set.subset_iUnion (fun s => S (b + s)) s)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixCovariance
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual matrix-conjugation actions on tracial tensor words

The conjugation action is constructed from the represented unitary and the
tracial conjugation. Its action on completed tensor words is obtained by genuine
tensor-product isometries.
-/

noncomputable section
namespace KadisonSimilarity
open scoped TensorProduct

universe u v
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {R : Type v} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [CompleteSpace E] {α : Type*} [Fintype α] [DecidableEq α]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] R)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a)) (hdense : DenseRange V)

/-- A matrix unitary acts isometrically through the actual left representation. -/
def representedMatrixUnitary (u : Matrix.unitaryGroup α ℂ) : E →ₗᵢ[ℂ] E :=
  (Unitary.linearIsometryEquiv
    ⟨L (ι (u : Matrix α α ℂ)), Unitary.map_mem (L.comp ι) u.property⟩).toLinearIsometry

omit [StarModule ℂ R] in
@[simp] theorem representedMatrixUnitary_apply (u : Matrix.unitaryGroup α ℂ) (x : E) :
    representedMatrixUnitary L ι u x = L (ι (u : Matrix α α ℂ)) x := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalFactorGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tracial generation by two factors implies generation of the concrete
von Neumann range by their norm-closed algebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*}
  [CStarAlgebra P]
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (A D : StarSubalgebra ℂ P)

theorem map_generated_mem {B : Type*} [CStarAlgebra B]
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (M : VonNeumannAlgebra H)
    (θ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b, θ (σ b) ∈ M) (T : H →L[ℂ] H)
    (hT : T ∈ representationVonNeumannAlgebra σ) : θ T ∈ M := by
  rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
  rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
  intro c hc
  apply θ.symm.injective
  simp only [map_mul]
  change θ.symm c * θ.symm (θ T) = θ.symm (θ T) * θ.symm c
  rw [θ.symm_apply_apply]
  apply hT (θ.symm c)
  rintro _ ⟨b, rfl⟩
  apply θ.injective
  simp only [map_mul]
  change θ (σ b) * θ (θ.symm c) = θ (θ.symm c) * θ (σ b)
  rw [θ.apply_symm_apply]
  exact hc (θ (σ b)) (hσ b)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeMatrixExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix-factor automorphism extends to the actual normal tracial
algebra by conjugating its left representation with the free-word unitary. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*}
  [CStarAlgebra P]
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)]
  [IsClosed (D : Set P)]
  {α : Type*}
  [Fintype α]
  [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D)
  (u : Matrix.unitaryGroup α ℂ)

theorem conjugate_eq_of_intertwining (U : H ≃ₗᵢ[ℂ] H)
    (T S : H →L[ℂ] H)
    (h : U.toLinearIsometry.toContinuousLinearMap.comp T =
      S.comp U.toLinearIsometry.toContinuousLinearMap) : U.conjStarAlgEquiv T = S := by
  ext ξ
  have hx := congrArg (fun F : H →L[ℂ] H => F (U.symm ξ)) h
  change U (T (U.symm ξ)) = S (U (U.symm ξ)) at hx
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  simpa only [U.apply_symm_apply] using hx

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_AmplifiedNormalRange
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite diagonal amplification of an actual normal represented algebra
has the expected normal range. -/

noncomputable section
namespace KadisonSimilarity
open scoped CStarAlgebra

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

local instance normalRange_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CentralSymmetrization
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging over finite families of central projections

The finite sign groups and their averages are constructed explicitly. A weak
operator cluster point of the net indexed by finite projection families
commutes with every central projection. The final passage to the whole center
uses only the already stated spectral-step specialization of Blackadar.
-/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMapWOT
open scoped Topology Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The center as a concrete von Neumann algebra. -/
def vonNeumannCenter (P : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := P.toStarSubalgebra ⊓ P.commutant.toStarSubalgebra
  centralizer_centralizer' := by
    have he : (P : Set (H →L[ℂ] H)) ∩ (P.commutant : Set (H →L[ℂ] H)) =
        Set.centralizer ((P : Set (H →L[ℂ] H)) ∪ P.commutant) := by
      rw [Set.centralizer_union]
      rw [← VonNeumannAlgebra.coe_commutant, ← VonNeumannAlgebra.coe_commutant]
      simp only [VonNeumannAlgebra.commutant_commutant, Set.inter_comm]
    change Set.centralizer (Set.centralizer
      ((P : Set (H →L[ℂ] H)) ∩ P.commutant)) =
      ((P : Set (H →L[ℂ] H)) ∩ P.commutant)
    rw [he]
    exact Set.centralizer_centralizer_centralizer
      ((P : Set (H →L[ℂ] H)) ∪ P.commutant)

@[simp] theorem mem_vonNeumannCenter (P : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    a ∈ vonNeumannCenter P ↔ a ∈ P ∧ a ∈ P.commutant := Iff.rfl

/-- The projection index is unrestricted in cardinality. -/
def CentralProjection (P : VonNeumannAlgebra H) :=
  {p : H →L[ℂ] H // p ∈ vonNeumannCenter P ∧ IsStarProjection p}

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConcreteGNSNormality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace realized faithfully in a concrete finite von Neumann algebra
has normal native GNS range. The original trace vector need not be cyclic. -/

noncomputable section
namespace KadisonSimilarity
open scoped CStarAlgebra ComplexOrder

/-- Normality of the native representation of the chosen positive trace. -/
def HasNormalGNS {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) : Prop :=
  τ.gnsStarAlgHom.range = (representationVonNeumannAlgebra τ.gnsStarAlgHom).toStarSubalgebra

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixTraceUniqueness
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The only tracial linear functional on a full finite matrix algebra is
its value at the identity times the normalized matrix trace. -/

noncomputable section
namespace KadisonSimilarity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Matrix units determine a tracial functional, without positivity. -/
theorem matrix_tracial_functional (F : Matrix ι ι ℂ →ₗ[ℂ] ℂ)
    (htr : ∀ a b, F (a * b) = F (b * a)) (a : Matrix ι ι ℂ) :
    F a = (Fintype.card ι : ℂ)⁻¹ * F 1 * Matrix.trace a := by
  classical
  let k : ι := Classical.arbitrary ι
  have hdiag (i : ι) : F (Matrix.single i i 1) = F (Matrix.single k k 1) := by
    simpa only [Matrix.single_mul_single_same, one_mul] using
      htr (Matrix.single i k 1) (Matrix.single k i 1)
  have hoff (i j : ι) (hij : i ≠ j) : F (Matrix.single i j 1) = 0 := by
    have h := htr (Matrix.single i i 1) (Matrix.single i j 1)
    have hz : Matrix.single i j (1 : ℂ) * Matrix.single i i 1 = 0 := by
      apply Matrix.single_mul_single_of_ne
      exact hij.symm
    simpa only [Matrix.single_mul_single_same, hz, one_mul, map_zero] using h
  have hunit : F 1 = (Fintype.card ι : ℂ) * F (Matrix.single k k 1) := by
    rw [← Matrix.sum_single_one, map_sum]
    simp only [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : F (Matrix.single k k 1) = (Fintype.card ι : ℂ)⁻¹ * F 1 := by
    rw [hunit, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have hentry (i j : ι) (z : ℂ) :
      F (Matrix.single i j z) =
        if i = j then z * ((Fintype.card ι : ℂ)⁻¹ * F 1) else 0 := by
    have hs : Matrix.single i j z = z • Matrix.single i j (1 : ℂ) := by
      rw [Matrix.smul_single]
      simp only [smul_eq_mul, mul_one]
    rw [hs, map_smul, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, hdiag, hd]
    · simp only [hij, ite_false, hoff i j hij, mul_zero]
  calc
    F a = ∑ i, ∑ j, F (Matrix.single i j (Matrix.of.symm a i j)) := by
      simpa only [map_sum, Matrix.of_symm_apply] using congrArg F (Matrix.matrix_eq_sum_single a)
    _ = ∑ i, Matrix.of.symm a i i * ((Fintype.card ι : ℂ)⁻¹ * F 1) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [hentry]
      simp
    _ = (Fintype.card ι : ℂ)⁻¹ * F 1 * Matrix.trace a := by
      rw [← Finset.sum_mul]
      change Matrix.trace a * ((Fintype.card ι : ℂ)⁻¹ * F 1) = _
      ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_UnitaryNormalRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual unitary intertwiner transports normality of a represented range. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem normal_range_of_unitary_intertwining
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (U : H ≃ₗᵢ[ℂ] K) (hU : ∀ a, U.conjStarAlgEquiv (σ a) = ρ a)
    (N : VonNeumannAlgebra K) (hρ : ρ.range = N.toStarSubalgebra) :
    σ.range = (representationVonNeumannAlgebra σ).toStarSubalgebra := by
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    exact mem_representationVonNeumannAlgebra σ a
  · intro hT
    let θ := U.conjStarAlgEquiv
    have hTN : θ T ∈ N := by
      change T ∈ representationVonNeumannAlgebra σ at hT
      rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
      rw [← SetLike.mem_coe, ← N.centralizer_centralizer]
      intro c hc
      apply θ.symm.injective
      simp only [map_mul]
      change θ.symm c * θ.symm (θ T) = θ.symm (θ T) * θ.symm c
      rw [θ.symm_apply_apply]
      apply hT (θ.symm c)
      rintro _ ⟨a, rfl⟩
      apply θ.injective
      simp only [map_mul]
      change θ (σ a) * θ (θ.symm c) = θ (θ.symm c) * θ (σ a)
      rw [θ.apply_symm_apply, hU]
      apply hc
      change ρ a ∈ N.toStarSubalgebra
      rw [← hρ]
      exact ⟨a, rfl⟩
    have hTr : θ T ∈ ρ.range := by
      rw [hρ]
      exact hTN
    obtain ⟨a, ha⟩ := hTr
    exact ⟨a, θ.injective ((hU a).trans ha)⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixSubfactorTransfer
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix amplification of an included subfactor acts entrywise.
Commutation with the original subfactor therefore gives commutation with
the full matrix subfactor on the square array of standard copies. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) {n : ℕ}

/-- The entrywise amplification of the actual subfactor embedding. -/
def matrixEntryHom : CStarMatrix (Fin n) (Fin n) A →⋆ₐ[ℂ]
    CStarMatrix (Fin n) (Fin n) B :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (({ φ.toAlgHom.mapMatrix with
      map_star' := fun X => by
        ext i j
        exact map_star φ (X j i) } :
      Matrix (Fin n) (Fin n) A →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) B).comp
      CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)

@[simp] theorem matrixEntryHom_apply (X : CStarMatrix (Fin n) (Fin n) A)
    (i j : Fin n) : matrixEntryHom φ X i j = φ (X i j) := rfl

theorem matrixEntryHom_injective (hφ : Function.Injective φ) :
    Function.Injective (matrixEntryHom (n := n) φ) := by
  intro X Y h
  ext i j
  apply hφ
  exact congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j) h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixDiagonalEmbedding
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed diffuse matrix-generated factor is embedded diagonally in
its finite matrix amplifications. The normalized trace is unchanged. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] (n : ℕ)

/-- The unital diagonal embedding into a finite C-star matrix algebra. -/
def matrixDiagonalHom : A →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    ({ Matrix.scalarAlgHom (Fin n) ℂ with
      map_star' := by
        intro a
        ext i j
        by_cases h : i = j
        · subst j
          simp [Matrix.scalar]
        · simp [Matrix.scalar, h, Ne.symm h] } :
      A →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) A)

@[simp] theorem matrixDiagonalHom_apply (a : A) (i j : Fin n) :
    matrixDiagonalHom n a i j = if i = j then a else 0 := by
  change Matrix.diagonal (fun _ : Fin n => a) i j = _
  simp only [Matrix.diagonal_apply]

@[simp] theorem matrixDiagonalHom_diagonal (a : A) (i : Fin n) :
    matrixDiagonalHom n a i i = a := by simp

variable [NeZero n]

theorem matrixDiagonalHom_injective : Function.Injective (matrixDiagonalHom (A := A) n) := by
  intro a b h
  have := congrArg (fun X : CStarMatrix (Fin n) (Fin n) A => X 0 0) h
  simpa only [matrixDiagonalHom_diagonal] using this

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixRelativeCommutant
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Irreducibility of an entrywise matrix inclusion

The scalar matrix units force any relative commutant element to be a constant
diagonal matrix. Its diagonal entry commutes with the original inclusion,
so scalarity of the original relative commutant proves scalarity after
matrix amplification. No normality or factor classification is used.
-/

noncomputable section
namespace KadisonSimilarity

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B] {n : ℕ}

@[simp] theorem matrixEntryHom_single (ρ : R →⋆ₐ[ℂ] B)
    (i j : Fin n) (a : R) :
    matrixEntryHom ρ (CStarMatrix.ofMatrix (Matrix.single i j a)) =
      CStarMatrix.ofMatrix (Matrix.single i j (ρ a)) := by
  ext k l
  simp only [matrixEntryHom_apply, CStarMatrix.ofMatrix_apply, Matrix.single_apply]
  split_ifs <;> simp only [map_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FactorAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three factor branches

The finite branch records only the fixed trace, matrix presentation, and
local published inputs used in the preceding application. The alternatives
are the structural factor classification; no alternative assumes an
operator estimate. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The structural data of a finite type-I factor in its given representation. -/
structure FiniteMatrixFactorModel (P : VonNeumannAlgebra H) where
  size : ℕ
  size_ne_zero : size ≠ 0
  inclusion : Matrix (Fin size) (Fin size) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)
  mem : ∀ a, inclusion a ∈ P
  surjective : ∀ T : H →L[ℂ] H, T ∈ P → ∃ a, inclusion a = T

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CentralDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Central decomposition and the uniform separable estimate

The direct-integral input records only representatives of decomposable
operators, their almost-everywhere algebra operations, the scalar and matrix
norm formulas, and countably many dense contraction sections. These are the
specializations of Blackadar, III.1.6.1–4 and III.5.1.10–15 used here (with
Kaplansky density, I.9.1.3, for the contraction tests). Representatives need
satisfy algebraic identities only almost everywhere for each fixed pair.

The scalar fiber bounds, their common conull set, the factor estimates, and
the final perturbation estimate are proved below.
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter ContinuousLinearMapWOT
open scoped Topology

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every element of the algebra commutes with its center. -/
theorem le_center_commutant (P : VonNeumannAlgebra H) :
    P.toStarSubalgebra ≤ (vonNeumannCenter P).commutant.toStarSubalgebra := by
  intro x hx
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro z hz
  exact ((VonNeumannAlgebra.mem_commutant_iff.mp hz.2) x hx).symm

/-- The original algebra as a subalgebra of the decomposable operators. -/
def centerCommutantInclusion (P : VonNeumannAlgebra H) :
    P.toStarSubalgebra →⋆ₐ[ℂ] (vonNeumannCenter P).commutant.toStarSubalgebra :=
  StarSubalgebra.inclusion (le_center_commutant P)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_IntertwinerExtension
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension by zero along an isometric Hilbert-space embedding. These
identities transport the central commutant to the common scalar L² model. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

/-- The actual operator equal to `T` on the range of `J` and zero on its
orthogonal complement. -/
def isometricExtension (T : H →L[ℂ] H) : K →L[ℂ] K :=
  (J.toContinuousLinearMap.comp T).comp J.toContinuousLinearMap.adjoint

theorem isometricExtension_on_range (T : H →L[ℂ] H) (x : H) :
    isometricExtension J T (J x) = J (T x) := by
  have h := congrArg (fun S : H →L[ℂ] H => S x) J.adjoint_comp_self
  change J.toContinuousLinearMap.adjoint (J x) = x at h
  change J (T (J.toContinuousLinearMap.adjoint (J x))) = _
  rw [h]

theorem isometricExtension_add (T U : H →L[ℂ] H) :
    isometricExtension J (T + U) = isometricExtension J T + isometricExtension J U := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [isometricExtension, ContinuousLinearMap.comp_apply, add_apply,
    map_add, LinearIsometry.coe_toContinuousLinearMap]

theorem isometricExtension_mul (T U : H →L[ℂ] H) :
    isometricExtension J (T * U) = isometricExtension J T * isometricExtension J U := by
  apply ContinuousLinearMap.ext
  intro x
  change J (T (U (J.toContinuousLinearMap.adjoint x))) =
    isometricExtension J T (J (U (J.toContinuousLinearMap.adjoint x)))
  exact (isometricExtension_on_range J T _).symm

theorem isometricExtension_star (T : H →L[ℂ] H) :
    isometricExtension J (star T) = star (isometricExtension J T) := by
  simp only [isometricExtension, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

theorem isometricExtension_norm (T : H →L[ℂ] H) : ‖isometricExtension J T‖ = ‖T‖ := by
  have hJ : ‖J.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [LinearIsometry.coe_toContinuousLinearMap, J.norm_map, one_mul] using
      (le_rfl : ‖x‖ ≤ ‖x‖)
  have hJa : ‖J.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hJ
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖J (T (J.toContinuousLinearMap.adjoint x))‖ ≤ _
    rw [J.norm_map]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((J.toContinuousLinearMap.adjoint.le_opNorm x).trans
        (by simpa using mul_le_mul_of_nonneg_right hJa (norm_nonneg x))) (norm_nonneg T))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    calc
      ‖T x‖ = ‖isometricExtension J T (J x)‖ := by
        rw [isometricExtension_on_range, J.norm_map]
      _ ≤ ‖isometricExtension J T‖ * ‖J x‖ := (isometricExtension J T).le_opNorm _
      _ = ‖isometricExtension J T‖ * ‖x‖ := by rw [J.norm_map]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CompressedBicommutant
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compressing a represented bicommutant

Commutation of zero extensions of the original commutant suffices to
recover the original von Neumann algebra after compression. The operator
being compressed need not be supported on the range of the isometry.
-/

noncomputable section
namespace KadisonSimilarity

variable {H K A : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [CStarAlgebra A] (J : H →ₗᵢ[ℂ] K)

/-- Applying the isometry's adjoint to a zero extension intertwines the
extended operator with the original one. -/
theorem adjoint_isometricExtension_apply (T : H →L[ℂ] H) (y : K) :
    J.toContinuousLinearMap.adjoint (isometricExtension J T y) =
      T (J.toContinuousLinearMap.adjoint y) := by
  have h (x : H) : J.toContinuousLinearMap.adjoint (J x) = x :=
    congrArg (fun U : H →L[ℂ] H => U x) J.adjoint_comp_self
  change J.toContinuousLinearMap.adjoint
    (J (T (J.toContinuousLinearMap.adjoint y))) = _
  exact h _

/-- A commutation relation with a zero extension compresses without any
range-support assumption on the other operator. -/
theorem compression_commutes_of_isometricExtension_commutes
    (T : H →L[ℂ] H) (Q : K →L[ℂ] K)
    (hcomm : isometricExtension J T * Q = Q * isometricExtension J T) :
    T * (J.toContinuousLinearMap.adjoint.comp (Q.comp J.toContinuousLinearMap)) =
      (J.toContinuousLinearMap.adjoint.comp (Q.comp J.toContinuousLinearMap)) * T := by
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg
    (fun U : K →L[ℂ] K => J.toContinuousLinearMap.adjoint (U (J x))) hcomm
  simpa only [mul_apply_eq_comp, adjoint_isometricExtension_apply,
    isometricExtension_on_range, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap] using h

/-- If the extended original commutant commutes with a represented
algebra, its represented bicommutant compresses into the original algebra. -/
theorem compression_mem_of_extended_commutant
    (P : VonNeumannAlgebra H) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hcomm : ∀ T : H →L[ℂ] H, T ∈ P.commutant →
      ∀ a : A, isometricExtension J T * σ a = σ a * isometricExtension J T)
    (Q : K →L[ℂ] K) (hQ : Q ∈ representationVonNeumannAlgebra σ) :
    J.toContinuousLinearMap.adjoint.comp (Q.comp J.toContinuousLinearMap) ∈ P := by
  rw [← P.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have hET : isometricExtension J T ∈
      (representationVonNeumannAlgebra σ).commutant := by
    apply (mem_representation_commutant_iff σ _).mpr
    rintro _ ⟨a, rfl⟩
    exact (hcomm T hT a).symm
  apply compression_commutes_of_isometricExtension_commutes J T Q
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hET Q hQ).symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConcretePredualRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normality of a trace restricts to a concrete von Neumann subalgebra.
Restriction sends each vector functional to the same vector functional,
and therefore preserves their closed span. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (hNM : N ≤ M)

def concreteInclusionCLM : N.toStarSubalgebra →L[ℂ] M.toStarSubalgebra :=
  { (StarSubalgebra.inclusion hNM).toLinearMap with
    cont := by
      change Continuous (fun a : N.toStarSubalgebra =>
        (⟨(a : H →L[ℂ] H), hNM a.property⟩ : M.toStarSubalgebra))
      exact continuous_subtype_val.subtype_mk _ }

def normalRestriction : StrongDual ℂ M.toStarSubalgebra →L[ℂ]
    StrongDual ℂ N.toStarSubalgebra :=
  (ContinuousLinearMap.compL ℂ N.toStarSubalgebra M.toStarSubalgebra ℂ).flip
    (concreteInclusionCLM hNM)

@[simp] theorem normalRestriction_apply (φ : StrongDual ℂ M.toStarSubalgebra)
    (a : N.toStarSubalgebra) :
    normalRestriction hNM φ a = φ (StarSubalgebra.inclusion hNM a) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableLpSubsequence
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common almost-everywhere subsequence for countably many L² columns.
The fast diagonal choice uses summable errors, so the same sequence works
for every column. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Countably many L² limits have one choice of indices with simultaneous
pointwise convergence almost everywhere. -/
theorem exists_countable_L2_ae_subsequence
    (f : ℕ → ℕ → Lp H 2 μ) (g : ℕ → Lp H 2 μ)
    (hf : ∀ j, Tendsto (fun n => f n j) atTop (𝓝 (g j))) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧
      ∀ᵐ a ∂μ, ∀ j, Tendsto (fun n => f (k n) j a) atTop (𝓝 (g j a)) := by
  have hex (n : ℕ) : ∃ k, n ≤ k ∧
      ∀ j ∈ Finset.range (n + 1), ‖f k j - g j‖ ≤ (1 / 2 : ℝ) ^ n := by
    have hall : ∀ᶠ k in atTop, ∀ j ∈ Finset.range (n + 1),
        ‖f k j - g j‖ < (1 / 2 : ℝ) ^ n := by
      apply (eventually_all_finset (Finset.range (n + 1))).mpr
      intro j _
      exact (tendsto_iff_norm_sub_tendsto_zero.mp (hf j)).eventually
        (gt_mem_nhds (by positivity))
    obtain ⟨k, hkn, hk⟩ := ((eventually_ge_atTop n).and hall).exists
    exact ⟨k, hkn, fun j hj => (hk j hj).le⟩
  choose k hk hfast using hex
  have hnorm (j : ℕ) : Summable (fun n => ‖f (k n) j - g j‖) := by
    apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop j] with n hn
    simpa only [norm_norm] using hfast n j (Finset.mem_range.mpr (by omega))
  have hae (j : ℕ) : ∀ᵐ a ∂μ, Summable (fun n => ‖(f (k n) j - g j) a‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2) (fun n => Lp.aestronglyMeasurable (f (k n) j - g j))
    simpa only [← Lp.enorm_def] using
      (tsum_enorm_ne_top_iff_summable_norm.mpr (hnorm j))
  refine ⟨k, hk, ?_⟩
  have heq : ∀ᵐ a ∂μ, ∀ j n,
      (f (k n) j - g j) a = f (k n) j a - g j a :=
    eventually_countable_forall.mpr fun j => eventually_countable_forall.mpr fun n =>
      Lp.coeFn_sub (f (k n) j) (g j)
  filter_upwards [eventually_countable_forall.mpr hae, heq] with a ha heq
  intro j
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [heq] using (ha j).tendsto_atTop_zero

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FieldWeakClosure
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Von Neumann closure of actual operator fields

A common subsequence on countably many constant L² columns turns strong
operator convergence into pointwise strong convergence almost everywhere.
The uniform norm bound extends convergence from the dense columns to every
fiber vector. Bicommutant closure then proves fiber membership.
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

/-- Uniformly bounded operators converge strongly once they converge on a
fixed countable dense set. -/
theorem strong_tendsto_of_bounded_dense_columns
    (T : ℕ → H →L[ℂ] H) (S : H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ n, ‖T n‖ ≤ C)
    (hcol : ∀ j, Tendsto (fun n => T n (TopologicalSpace.denseSeq H j))
      atTop (𝓝 (S (TopologicalSpace.denseSeq H j)))) :
    ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 (S x)) := by
  have hequi : Equicontinuous (fun n x => T n x) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => C * r)
      (by simpa only [mul_zero] using (continuous_const_mul C).tendsto (0 : ℝ))
    intro x y n
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact ((T n).le_opNorm (x - y)).trans
      (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
  intro x
  exact (TopologicalSpace.denseRange_denseSeq H).induction_on x
    (hequi.isClosed_setOfPred_tendsto S.continuous) hcol

variable [CompleteSpace H]

omit [TopologicalSpace.SeparableSpace H] in
/-- Strong limits preserve von Neumann membership directly by commuting
with every member of the commutant. -/
theorem vonNeumann_mem_of_strong_tendsto
    (P : VonNeumannAlgebra H) (T : ℕ → H →L[ℂ] H) (S : H →L[ℂ] H)
    (hmem : ∀ n, T n ∈ P)
    (hlim : ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 (S x))) : S ∈ P := by
  rw [← P.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro A hA
  apply ContinuousLinearMap.ext
  intro x
  have hleft : Tendsto (fun n => A (T n x)) atTop (𝓝 (A (S x))) :=
    (A.continuous.tendsto (S x)).comp (hlim x)
  have heq : (fun n => A (T n x)) = (fun n => T n (A x)) := by
    funext n
    exact congrArg (fun R : H →L[ℂ] H => R x)
      (VonNeumannAlgebra.mem_commutant_iff.mp hA (T n) (hmem n)).symm
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (hlim (A x))

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Fiber membership is inherited from uniformly bounded strong
approximants on L². The pointwise action hypotheses are per fixed vector,
so no uncountable intersection of conull sets is used. -/
theorem ae_field_mem_of_strong_approximation
    (P : Ω → VonNeumannAlgebra H)
    (T : ℕ → Lp H 2 μ →L[ℂ] Lp H 2 μ) (S : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (R : ℕ → Ω → H →L[ℂ] H) (Q : Ω → H →L[ℂ] H)
    (haction : ∀ n (f : Lp H 2 μ), ∀ᵐ a ∂μ, T n f a = R n a (f a))
    (hS : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, S f a = Q a (f a))
    (hstrong : ∀ f : Lp H 2 μ, Tendsto (fun n => T n f) atTop (𝓝 (S f)))
    (C : ℝ) (hbound : ∀ n, ∀ᵐ a ∂μ, ‖R n a‖ ≤ C)
    (hmem : ∀ n, ∀ᵐ a ∂μ, R n a ∈ P a) :
    ∀ᵐ a ∂μ, Q a ∈ P a := by
  let d := TopologicalSpace.denseSeq H
  obtain ⟨k, _, hlim⟩ := exists_countable_L2_ae_subsequence μ
    (fun n j => T n (Lp.const 2 μ (d j)))
    (fun j => S (Lp.const 2 μ (d j))) (fun j => hstrong _)
  have hsource : ∀ᵐ a ∂μ, ∀ j n,
      T (k n) (Lp.const 2 μ (d j)) a = R (k n) a (d j) :=
    eventually_countable_forall.mpr fun j => eventually_countable_forall.mpr fun n =>
      pointwise_action_column μ (T (k n)) (R (k n)) (haction (k n)) (d j)
  have htarget : ∀ᵐ a ∂μ, ∀ j,
      S (Lp.const 2 μ (d j)) a = Q a (d j) :=
    eventually_countable_forall.mpr fun j => pointwise_action_column μ S Q hS (d j)
  have hb : ∀ᵐ a ∂μ, ∀ n, ‖R n a‖ ≤ C :=
    eventually_countable_forall.mpr hbound
  have hm : ∀ᵐ a ∂μ, ∀ n, R n a ∈ P a :=
    eventually_countable_forall.mpr hmem
  filter_upwards [hlim, hsource, htarget, hb, hm] with a hlim hsource htarget hb hm
  have hcol : ∀ j, Tendsto (fun n => R (k n) a (TopologicalSpace.denseSeq H j))
      atTop (𝓝 (Q a (TopologicalSpace.denseSeq H j))) := by
    intro j
    have heq : (fun n => T (k n) (Lp.const 2 μ (d j)) a) =
        (fun n => R (k n) a (d j)) := funext (hsource j)
    have hj := hlim j
    rw [heq, htarget j] at hj
    exact hj
  exact vonNeumann_mem_of_strong_tendsto (P a) (fun n => R (k n) a) (Q a)
    (fun n => hm (k n))
    (strong_tendsto_of_bounded_dense_columns _ _ C (fun n => hb (k n)) hcol)

/-- In applications the uniform bound is a norm bound on the actual
approximating operators; the pointwise bound is then derived. -/
theorem ae_field_mem_of_norm_bounded_strong_approximation
    (P : Ω → VonNeumannAlgebra H)
    (T : ℕ → Lp H 2 μ →L[ℂ] Lp H 2 μ) (S : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (R : ℕ → Ω → H →L[ℂ] H) (Q : Ω → H →L[ℂ] H)
    (haction : ∀ n (f : Lp H 2 μ), ∀ᵐ a ∂μ, T n f a = R n a (f a))
    (hS : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, S f a = Q a (f a))
    (hstrong : ∀ f : Lp H 2 μ, Tendsto (fun n => T n f) atTop (𝓝 (S f)))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖T n‖ ≤ C)
    (hmem : ∀ n, ∀ᵐ a ∂μ, R n a ∈ P a) :
    ∀ᵐ a ∂μ, Q a ∈ P a :=
  ae_field_mem_of_strong_approximation μ P T S R Q haction hS hstrong C
    (fun n => (pointwise_field_norm_iff μ (T n) (R n) (haction n) C hC).mp (hbound n)) hmem

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConullFieldExtension
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend fields from a conull measurable base by zero while retaining
their actual L² action on the original measure space. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {Ω F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (μ : Measure Ω) (s : Set Ω)

def zeroExtendOperatorField (Q : s → F →L[ℂ] F) (x : Ω) : F →L[ℂ] F := by
  classical
  exact if h : x ∈ s then Q ⟨x, h⟩ else 0

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_KaplanskyStrongSequence
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sequential Kaplansky approximation on a separable Hilbert space

Finite-vector Kaplansky approximation applied to increasing finite sets of
dense vectors gives an actual strongly convergent sequence. Every source
term satisfies the exact norm bound of the target operator.
-/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology CStarAlgebra

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [TopologicalSpace.SeparableSpace H] in
/-- Strong convergence survives extension by zero to the common L² model. -/
theorem isometricExtension_strong_tendsto
    (J : H →ₗᵢ[ℂ] K) (T : ℕ → H →L[ℂ] H) (S : H →L[ℂ] H)
    (hstrong : ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 (S x))) :
    ∀ y : K, Tendsto (fun n => isometricExtension J (T n) y) atTop
      (𝓝 (isometricExtension J S y)) := by
  intro y
  change Tendsto (fun n => J (T n (J.toContinuousLinearMap.adjoint y))) atTop
    (𝓝 (J (S (J.toContinuousLinearMap.adjoint y))))
  exact (J.continuous.tendsto _).comp (hstrong _)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NonseparableReduction
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing separability from the uniform commutator estimate

Each operator-norm test involves finitely many matrix entries and finitely
many vectors. Their common reducing subspace is separable. We restrict the
actual C-star algebra generated by those entries, use the two-vector
Kaplansky specialization to reach its bicommutant, and recover the original
vector test by the isometric inclusion.
-/

noncomputable section
universe u
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The separable version of the actual universal von Neumann estimate. -/
def SeparableUniformCommutatorEstimate (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (P : VonNeumannAlgebra K), CommutatorEstimate P C

/-- Blackadar I.9.1.3 and C-star quotient norm lifting, only on two test
vectors in a separable represented Hilbert space. This is the exact
published closure input used in the reduction below. -/
def SeparableTwoVectorKaplanskyInput : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)),
      TwoVectorKaplanskyInput σ (representationVonNeumannAlgebra σ)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProjectionFieldReduction
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing operator fields to their projection fibers

Each orthogonal projection has an actual closed Hilbert range. Compression
of a supported operator to this range preserves its norm and action. These
constructions are pointwise, so they apply to every fixed operator field;
no simultaneous representation law on an uncountable algebra is required.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual closed range of an orthogonal projection. -/
def projectionFiber (p : H →L[ℂ] H) (hp : IsStarProjection p) : ClosedSubmodule ℂ H :=
  ⟨p.range, ContinuousLinearMap.IsIdempotentElem.isClosed_range hp.isIdempotentElem⟩

variable {A : Type*} [CStarAlgebra A]

section Fields

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] in
/-- An actual left-support identity gives the corresponding field identity
almost everywhere. -/
theorem ae_field_left_support
    (P T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p R : Ω → H →L[ℂ] H)
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hPT : P * T = T) : ∀ᵐ a ∂μ, p a * R a = R a := by
  have h := pointwise_field_mul μ P T p R R hP hR (by simpa only [hPT] using hR)
  exact h.mono fun _ ha => ha.symm

omit [CompleteSpace H] in
/-- Right support is also inherited from the actual L² operator equation. -/
theorem ae_field_right_support
    (P T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p R : Ω → H →L[ℂ] H)
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hTP : T * P = T) : ∀ᵐ a ∂μ, R a * p a = R a := by
  have h := pointwise_field_mul μ T P R p R hR hP (by simpa only [hTP] using hR)
  exact h.mono fun _ ha => ha.symm

end Fields

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NonunitalRangeRepresentation
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonunital representation of a unital C-star algebra becomes unital
on the range of the image of its unit. This also covers the zero fibers
used outside a conull spectral base. -/

noncomputable section
namespace KadisonSimilarity

variable {B K : Type*} [CStarAlgebra B]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def nonunitalUnitProjection (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : K →L[ℂ] K := ρ 1

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_UnitalizedExtension
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension by zero is a nonunital star homomorphism. Its unitization
provides a genuine representation whose distinguished projection recovers
the original Hilbert subspace. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

def isometricExtensionHom : (H →L[ℂ] H) →⋆ₙₐ[ℂ] (K →L[ℂ] K) where
  toFun := isometricExtension J
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    simp [isometricExtension]
  map_add' := isometricExtension_add J
  map_mul' := isometricExtension_mul J
  map_smul' := by
    intro c T
    apply ContinuousLinearMap.ext
    intro x
    simp [isometricExtension]
  map_star' := isometricExtension_star J

variable {B : Type*} [CStarAlgebra B] (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- A unital representation retaining the zero extension of every original
algebra element. The added unit acts on the full ambient Hilbert space. -/
def unitalizedExtension : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K) :=
  Unitization.starLift ((isometricExtensionHom J).comp σ.toNonUnitalStarAlgHom)

@[simp] theorem unitalizedExtension_inr (b : B) :
    unitalizedExtension J σ (Unitization.inr b) = isometricExtension J (σ b) := by
  change algebraMap ℂ (K →L[ℂ] K) 0 + isometricExtension J (σ b) = _
  simp

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_UnitizationProjection
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover a represented unital algebra from its unitization by restricting
to the image of its old unit. -/

noncomputable section
namespace KadisonSimilarity

variable {B K : Type*} [CStarAlgebra B]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem unitization_old_unit_commutes (b : Unitization ℂ B) :
    Commute (Unitization.inr (1 : B)) b := by
  apply Unitization.ext
  · simp
  · simp [add_comm]

def unitizationProjection (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) : K →L[ℂ] K :=
  ρ (Unitization.inr (1 : B))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_VectorL2Representation
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual unital star representation of continuous scalar functions
on the vector-valued L² space. -/

noncomputable section
namespace KadisonSimilarity.VectorL2
open MeasureTheory
open scoped InnerProductSpace

variable {X H : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem continuousL2Mul_star (f : C(X, ℂ)) :
    continuousL2Mul (H := H) μ (star f) = (continuousL2Mul μ f).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousL2Mul_ae μ (star f) ξ, continuousL2Mul_ae μ f η] with x hx hy
  rw [hx, hy]
  simp [inner_smul_left, inner_smul_right]

def continuousRepresentation : C(X, ℂ) →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun := continuousL2Mul μ
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply Lp.ext
    filter_upwards [continuousL2Mul_ae μ 0 ξ, Lp.coeFn_zero H 2 μ] with x hm hz
    change continuousL2Mul μ 0 ξ x = (0 : Lp H 2 μ) x
    rw [hm, hz]
    simp
  map_one' := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply Lp.ext
    filter_upwards [continuousL2Mul_ae μ 1 ξ] with x hm
    rw [hm]
    simp
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro ξ
    change continuousL2Mul μ (f + g) ξ = continuousL2Mul μ f ξ + continuousL2Mul μ g ξ
    apply Lp.ext
    filter_upwards [continuousL2Mul_ae μ (f + g) ξ, continuousL2Mul_ae μ f ξ,
      continuousL2Mul_ae μ g ξ,
      Lp.coeFn_add (continuousL2Mul μ f ξ) (continuousL2Mul μ g ξ)] with x hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply]
    rw [hf, hg, ContinuousMap.add_apply, add_smul]
  map_mul' f g := by
    apply ContinuousLinearMap.ext
    intro ξ
    change continuousL2Mul μ (f * g) ξ = continuousL2Mul μ f (continuousL2Mul μ g ξ)
    apply Lp.ext
    filter_upwards [continuousL2Mul_ae μ (f * g) ξ,
      continuousL2Mul_ae μ f (continuousL2Mul μ g ξ),
      continuousL2Mul_ae μ g ξ] with x hfg hf hg
    rw [hfg, hf, hg, ContinuousMap.mul_apply, mul_smul]
  commutes' z := by
    apply ContinuousLinearMap.ext
    intro ξ
    change continuousL2Mul μ (algebraMap ℂ C(X, ℂ) z) ξ = z • ξ
    apply Lp.ext
    filter_upwards [continuousL2Mul_ae μ (algebraMap ℂ C(X, ℂ) z) ξ,
      Lp.coeFn_smul z ξ] with x hm hz
    rw [hm, hz]
    rfl
  map_star' f := continuousL2Mul_star μ f

end KadisonSimilarity.VectorL2

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ConjugateMomentCriterion
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer mixed moments imply freeness of a conjugated subalgebra. -/

noncomputable section
namespace KadisonSimilarity

variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

def conjugateMomentBlock (F : B → C) (u : unitary C) (p : B × B) : C :=
  F p.1 * (u : C) * F p.2 * star (u : C)

variable (σ : C →ₗ[ℂ] ℂ) (h1 : σ 1 = 1)
  (tr : ∀ a b, σ (a * b) = σ (b * a)) (φ : B →⋆ₐ[ℂ] C) (u : unitary C)

include tr in
lemma trace_conjugation (b : C) :
    σ ((u : C) * b * star (u : C)) = σ b := by
  rw [tr, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_IntegerMomentScaling
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar homogeneity of each finite integer-power mixed word. -/

noncomputable section
namespace KadisonSimilarity

variable {B I : Type*} [CStarAlgebra B]

def wordScalar (c : I → ℂ) : Option I → ℂ
  | none => 1
  | some i => c i

end KadisonSimilarity

end

end OAI
end


