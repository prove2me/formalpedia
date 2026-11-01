-- Prove2me | Definitions.Def_OAIQ075A006
-- name    : OAIQ075A006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T07:56:45.939306+00:00
-- url     : https://prove2.me/theorems/f77cf8a6-731f-41d2-b73c-49439a71956e
-- title:
--   Definitions bundle OAIQ075A006 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 289 declarations of OpenAI's Lean: 127 definitions, 24 instances and 138 theorems. The definitions and types are `OAI.KadisonSimilarity.angularCharacter`, `OAI.KadisonSimilarity.angularIntegral`, `OAI.KadisonSimilarity.angularPowerMoment`, `OAI.KadisonSimilarity.arcCoefficient`, `OAI.KadisonSimilarity.arcHankelMatrix`, `OAI.KadisonSimilarity.arcWidth`, `OAI.KadisonSimilarity.binaryIsometryFamily`, `OAI.KadisonSimilarity.binarySpectralCorrection`, `OAI.KadisonSimilarity.boundedFieldLinear`, `OAI.KadisonSimilarity.boundedFieldOperator`, `OAI.KadisonSimilarity.boundedFieldVector`, `OAI.KadisonSimilarity.boundedHomOrbit`, `OAI.KadisonSimilarity.centeredDihedralArc`, `OAI.KadisonSimilarity.cfcSqrtRemainder`, `OAI.KadisonSimilarity.complementProjection`, `OAI.KadisonSimilarity.continuousOrbitSubmodule`, `OAI.KadisonSimilarity.cstarMatrixPadding`, `OAI.KadisonSimilarity.cyclicColumnRoot`, `OAI.KadisonSimilarity.cyclicPolarColumn`, `OAI.KadisonSimilarity.cyclicShiftVector`, `OAI.KadisonSimilarity.denseSubringRepresentation`, `OAI.KadisonSimilarity.derivationDefect`, `OAI.KadisonSimilarity.derivationDefectSpace`, `OAI.KadisonSimilarity.dihedralArcProjection`, `OAI.KadisonSimilarity.exponentialSimilarityRatAlgebra`, `OAI.KadisonSimilarity.factorizationSpace`, `OAI.KadisonSimilarity.finiteMatrixHaarProbability`, `OAI.KadisonSimilarity.finiteMatrixTestAlgebra`, `OAI.KadisonSimilarity.finiteMatrixUnitaryMeasurableSpace`, `OAI.KadisonSimilarity.finiteMean`, `OAI.KadisonSimilarity.finiteTwirl`, `OAI.KadisonSimilarity.fixedPointComplement`, `OAI.KadisonSimilarity.fixedPointRemainder`, `OAI.KadisonSimilarity.gnsLeftSequence`, `OAI.KadisonSimilarity.grothendieckConstant`, `OAI.KadisonSimilarity.grothendieckRestrict`, `OAI.KadisonSimilarity.grothendieckUnitaryFamily`, `OAI.KadisonSimilarity.halfSpectralProjection`, `OAI.KadisonSimilarity.hilbertSumTransport`, `OAI.KadisonSimilarity.hilbertSumTransportWithComponents` and 87 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_GroupTrace`, `KadisonSimilarity_Derivation_CyclicColumnPolar`, `KadisonSimilarity_Derivation_CyclicColumnTests`, `KadisonSimilarity_Derivation_CyclicSpectralSum`, `KadisonSimilarity_Derivation_DerivationDefectSpace`, `KadisonSimilarity_Derivation_DicksonAdjoint`, `KadisonSimilarity_Derivation_DicksonRow`, `KadisonSimilarity_Derivation_FactorizationSpace`, `KadisonSimilarity_Derivation_GrothendieckUltrapower`, `KadisonSimilarity_Derivation_NormAttainingGrothendieck`, `KadisonSimilarity_Derivation_NormalCyclicGraph`, `KadisonSimilarity_Derivation_QuadraticSandwich`, `KadisonSimilarity_Derivation_RectangularDerivations`, `KadisonSimilarity_FreeProduct_AngularIntegralBounds`, `KadisonSimilarity_FreeProduct_ArcFourier`, `KadisonSimilarity_FreeProduct_CompressionProjectionTransport`, `KadisonSimilarity_FreeProduct_CompressionSetup`, `KadisonSimilarity_FreeProduct_DihedralArcProjection`, `KadisonSimilarity_FreeProduct_DihedralCutMoments`, `KadisonSimilarity_FreeProduct_DihedralFourier`, `KadisonSimilarity_FreeProduct_DihedralPolynomialMoments`, `KadisonSimilarity_FreeProduct_FreeProductMatrixContinuity`, `KadisonSimilarity_FreeProduct_HaarSymmetrization`, `KadisonSimilarity_FreeProduct_HankelBounds`, `KadisonSimilarity_FreeProduct_LeadingWordGeometry`, `KadisonSimilarity_FreeProduct_SpectralArcResolvents`, `KadisonSimilarity_Representation_Amplification`, `KadisonSimilarity_Representation_BoundedMeasurableField`, `KadisonSimilarity_Representation_CentralSymmetrization`, `KadisonSimilarity_Representation_ClosedFamilySpan`, `KadisonSimilarity_Representation_ConcreteIrreducibleSubfactor`, `KadisonSimilarity_Representation_ConullRepresentationExtension`, `KadisonSimilarity_Representation_CountablyGeneratedCStarAlgebra`, `KadisonSimilarity_Representation_DenseLinearOperator`, `KadisonSimilarity_Representation_DenseStarRepresentation`, `KadisonSimilarity_Representation_DiagonalFieldAction`, `KadisonSimilarity_Representation_FiniteSymmetrization`, `KadisonSimilarity_Representation_HilbertSumIsometries`, `KadisonSimilarity_Representation_JointFiberRestriction`, `KadisonSimilarity_Representation_L2ScalarIntertwining`, `KadisonSimilarity_Representation_NonseparableReduction`, `KadisonSimilarity_Representation_NormalSpectralTruncation`, `KadisonSimilarity_Representation_NormalStandardEmbedding`, `KadisonSimilarity_Representation_NormalizedContractions`, `KadisonSimilarity_Representation_OrthogonalColumns`, `KadisonSimilarity_Representation_PolarPartialIsometry`, `KadisonSimilarity_Representation_ProjectionCommutators`, `KadisonSimilarity_Representation_ProperlyInfiniteStructure`, `KadisonSimilarity_Representation_RadonNikodymCoordinates`, `KadisonSimilarity_Representation_ReducingRepresentationTransfer`, `KadisonSimilarity_Representation_RegularizedPolarFactor`, `KadisonSimilarity_Representation_ScalarLocalizationApproximation`, `KadisonSimilarity_Representation_ScalarLocalizationLimit`, `KadisonSimilarity_Representation_SeparableReducingTest`, `KadisonSimilarity_Representation_SeparableRepresentationTests`, `KadisonSimilarity_Representation_SpectralBaseTopology`, `KadisonSimilarity_Representation_SpectralCutBounds`, `KadisonSimilarity_Representation_SpectralDensityIsometry`, `KadisonSimilarity_Representation_SpectralRoundingDischarge`, `KadisonSimilarity_Representation_SpectralStepDischarge`, `KadisonSimilarity_Representation_SpectralSupportLimit`, `KadisonSimilarity_Representation_SquareArrayPadding`, `KadisonSimilarity_Representation_UnitizationFiberClosure`, `KadisonSimilarity_Representation_WeakOperatorIntegral`, `KadisonSimilarity_Similarity_ArvesonCompleteNorm`, `KadisonSimilarity_Similarity_CyclicSimilarity`, `KadisonSimilarity_Similarity_ExponentialSimilarity`, `KadisonSimilarity_Similarity_FiniteCyclicSimilarity`, `KadisonSimilarity_Similarity_KirchbergConjugation`, `KadisonSimilarity_Similarity_KirchbergIntegral`, `KadisonSimilarity_Similarity_SimilarityCompleteBound`, `KadisonSimilarity_Similarity_SimilarityMetric`, `KadisonSimilarity_Similarity_SimilarityUniverseTransfer`, `KadisonSimilarity_Tensor_EndpointPairings`, `KadisonSimilarity_Tensor_InvariantCycles`, `KadisonSimilarity_Tensor_InvariantIntertwiners`, `KadisonSimilarity_Tensor_InvariantTensors`, `KadisonSimilarity_Tensor_TensorClassification`, `KadisonSimilarity_Tensor_TensorCoefficientMatrix`, `KadisonSimilarity_Tensor_TensorCommutantExtension`, `KadisonSimilarity_Tensor_TensorDiagonalWeights`, `KadisonSimilarity_Tensor_TensorMatrixAlgebra`, `KadisonSimilarity_Tensor_TensorStableSpanning`, `KadisonSimilarity_Tracial_CStarMatrixPadding`, `KadisonSimilarity_Tracial_FiniteFactorSymmetrization`, `KadisonSimilarity_Tracial_JointCStarSource`, `KadisonSimilarity_Tracial_MatrixSmallCorner`, `KadisonSimilarity_Tracial_TracialInputTransport`, `KadisonSimilarity_Tracial_TracialMatrixCovariance`, `KadisonSimilarity_Tracial_TracialRightSupportDischarge`, `KadisonSimilarity_Tracial_TracialStageCommutation`, `KadisonSimilarity_Tracial_TracialUltrapowerActions`, `Naimark_Basic`, `Naimark_States`.
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A011` and `OAIQ075A012`; the statement `OAI.KadisonSimilarity.list_equal_square_orbit_comparison`.
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
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_GroupTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual ultraweak topology, generated by absolutely summable vector
functionals. No continuity of a chosen trace is built into this definition. -/
@[instance_reducible] def ultraweakTopology : TopologicalSpace (H →L[ℂ] H) :=
  ⨅ (ξ : ℕ → H) (η : ℕ → H) (_ : Summable (fun n => ‖ξ n‖ * ‖η n‖)),
    TopologicalSpace.induced (fun T : H →L[ℂ] H => ∑' n, inner ℂ (ξ n) (T (η n)))
      inferInstance

variable {H}

@[instance_reducible] def algebraUltraweakTopology (M : VonNeumannAlgebra H) :
    TopologicalSpace M.toStarSubalgebra :=
  TopologicalSpace.induced (fun T : M.toStarSubalgebra => (T : H →L[ℂ] H)) (ultraweakTopology H)

end UltrapowerBridge

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix amplification and the main statements

Matrices act on finite Hilbert sums with their `ℓ²` norm. Consequently the
norm in `CommutatorEstimate` is the concrete operator matrix norm, rather than
the coordinatewise supremum norm of a matrix. No main estimate is assumed here.
-/

noncomputable section

universe u v

namespace KadisonSimilarity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

/-- Orthogonal projections are contractions, including the zero projection. -/
theorem norm_projection_le_one (e : H →L[ℂ] H) (hstar : star e = e)
    (hsq : e * e = e) : ‖e‖ ≤ 1 := by
  have hnorm : ‖e‖ * ‖e‖ = ‖e‖ := by
    rw [← CStarRing.norm_star_mul_self, hstar, hsq]
  nlinarith [norm_nonneg e]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_OrthogonalColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite orthogonal word levels and their full-codomain errors. -/

noncomputable section
namespace KadisonSimilarity

open Finset ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Pythagoras for the finite family of orthogonal output vectors. -/
theorem norm_sum_sq_of_pairwise_orthogonal {N : ℕ} (v : Fin N → K)
    (horth : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i : Fin N, v i‖ ^ 2 = ∑ i : Fin N, ‖v i‖ ^ 2 := by
  have hin (i : Fin N) : ∑ j : Fin N, inner ℂ (v j) (v i) = inner ℂ (v i) (v i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact horth j i hji
    · simp
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner, inner_sum, hin, map_sum]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_RectangularDerivations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangular derivations and the row/column estimate -/

noncomputable section
namespace KadisonSimilarity

variable {A F K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable [CompleteSpace F] [CompleteSpace K]

open scoped CStarAlgebra

/-- A rectangular derivation vanishes at the identity. -/
theorem rectangularDerivation_map_one (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) : δ 1 = 0 := by
  have h := hδ 1 1
  simp only [one_mul, map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_id] at h
  have h' : δ 1 + 0 = δ 1 + δ 1 := by simpa using h
  exact (add_left_cancel h').symm

/-- Rescaling the derivation before forming the triangular representation. -/
def normalizedRectangularDerivation (δ : A →L[ℂ] (K →L[ℂ] F)) :
    A →L[ℂ] (K →L[ℂ] F) := ((‖δ‖⁻¹ : ℝ) : ℂ) • δ

theorem normalizedRectangularDerivation_leibniz (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b)) (a b : A) :
    normalizedRectangularDerivation δ (a * b) =
      (ρ a).comp (normalizedRectangularDerivation δ b) +
        (normalizedRectangularDerivation δ a).comp (σ b) := by
  ext x
  simp [normalizedRectangularDerivation, hδ, smul_add]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_DicksonAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The adjoint homomorphism and the exact row-to-column transfer. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Taking adjoints in both source and target preserves the algebra map. -/
def sharpHom (π : BoundedUnitalHom A H) : BoundedUnitalHom A H :=
  ⟨{
    toFun := fun a => star (π.1 (star a))
    map_one' := by simp
    map_mul' := by intro a b; simp only [star_mul, map_mul]
    map_zero' := by simp
    map_add' := by intro a b; simp only [star_add, map_add]
    commutes' := by
      intro z
      change star (π.1 (star (algebraMap ℂ A z))) = algebraMap ℂ (H →L[ℂ] H) z
      simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one, map_smul, map_one,
        star_star] },
    continuous_star.comp (π.2.comp continuous_star)⟩

@[simp] theorem sharpHom_apply (π : BoundedUnitalHom A H) (a : A) :
    (sharpHom π).1 a = star (π.1 (star a)) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProjectionCommutators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal block estimate used before the spectral step approximation. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open ContinuousLinearMap

/-- Complement of a commutant projection, as a commutant projection. -/
def complementProjection {M : VonNeumannAlgebra H} (e : CommutantProjection M) :
    CommutantProjection M :=
  ⟨1 - e.val, M.commutant.sub_mem M.commutant.one_mem e.property.1,
    by simp [e.property.2.1], by
      calc
        (1 - e.val) * (1 - e.val) = 1 - e.val - e.val + e.val * e.val := by noncomm_ring
        _ = 1 - e.val := by rw [e.property.2.2]; abel⟩

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

/-- Closed range used to construct the support projection of an operator. -/
def operatorRangeClosure (B : H →L[ℂ] H) : Submodule ℂ H :=
  B.range.topologicalClosure

instance operatorRangeClosure_complete (B : H →L[ℂ] H) :
    CompleteSpace (operatorRangeClosure B) :=
  inferInstanceAs (CompleteSpace B.range.topologicalClosure)

/-- The orthogonal projection onto the closed operator range. -/
def rangeSupport (B : H →L[ℂ] H) : H →L[ℂ] H :=
  (operatorRangeClosure B).starProjection

omit [CompleteSpace H] in
theorem operatorRangeClosure_invariant (B T : H →L[ℂ] H) (h : Commute B T)
    {x : H} (hx : x ∈ operatorRangeClosure B) : T x ∈ operatorRangeClosure B := by
  have hh : B.range.topologicalClosure ≤
      (operatorRangeClosure B).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨y, rfl⟩
      apply Submodule.le_topologicalClosure
      refine ⟨T y, ?_⟩
      exact congrArg (fun S : H →L[ℂ] H => S y) h.eq
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact hh hx

/-- The open upper spectral cut `(t,∞)` of a selfadjoint operator. -/
def upperSpectralCut (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  rangeSupport ((A - t • 1)⁺)

/-- One binary spectral correction. -/
def binarySpectralCorrection (B : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  r • rangeSupport B⁺ - (r / 2) • 1

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RegularizedPolarFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contractive approximate polar factors inside the original C-star algebra.
These avoid any bidual extension in the row-bound argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveShiftReciprocal (h : A) (ε : ℝ) : A :=
  cfc (fun t : ℝ => (t + ε)⁻¹) h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicColumnPolar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contractive regularized polar columns inside the source algebra. These
columns will supply dense cyclic vector tests with a varying unit vector. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder WithCStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The positive square root of a finite column square. -/
def cyclicColumnRoot {n : ℕ} (a : Fin n → A) : A :=
  CFC.sqrt (∑ i, star (a i) * a i)

/-- The regularized polar column stays in the original algebra. -/
def cyclicPolarColumn {n : ℕ} (a : Fin n → A) (ε : ℝ) : Matrix (Fin n) (Fin 1) A :=
  fun i _ => a i * positiveShiftReciprocal (cyclicColumnRoot a) ε

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

def sharpVectorMap (π : BoundedUnitalHom A H) (ξ : H) : A →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H ξ).comp
    ⟨(sharpHom π).1.toLinearMap, (sharpHom π).2⟩

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem sharpVectorMap_apply (π : BoundedUnitalHom A H) (ξ : H) (a : A) :
    sharpVectorMap π ξ a = (π.1 (star a)).adjoint ξ := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_NormAttainingGrothendieck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm-attaining case of the little Grothendieck inequality.
The unitary paths and their quadratic estimates are constructed explicitly. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The fourth-order remainder for the unitary path, still expressed in
one continuous functional calculus. -/
def cfcSqrtRemainder (a : A) (t : ℝ) : A :=
  cfc (fun x : ℝ => 1 - Real.sqrt (1 - (t * x) ^ 2) - (t * x) ^ 2 / 2) a

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_GrothendieckUltrapower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded families turn approximate unitary norm attainment into exact
attainment. The source is the ordinary bounded product C-star algebra; only
the Hilbert target needs an ultraproduct. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped ENNReal Topology ComplexOrder

variable {B H : Type*} [CStarAlgebra B] [Nontrivial B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Constants in the bounded product algebra. -/
def grothendieckConstant : B →⋆ₐ[ℂ] lp (fun _ : ℕ => B) ∞ where
  toFun b := ⟨fun _ => b, memℓp_infty ⟨‖b‖, by rintro _ ⟨i, rfl⟩; exact le_rfl⟩⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  commutes' _ := rfl

@[simp] theorem grothendieckConstant_apply (b : B) (i : ℕ) :
    grothendieckConstant b i = b := rfl

/-- A bounded family of unitaries is unitary in the bounded product. -/
def grothendieckUnitaryFamily (u : ℕ → unitary B) : unitary (lp (fun _ : ℕ => B) ∞) :=
  ⟨⟨fun i => u i, memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    exact (CStarRing.norm_coe_unitary (u i)).le⟩⟩, by
      constructor <;> apply Subtype.ext <;> funext i
      · exact Unitary.star_mul_self_of_mem (u i).prop
      · exact Unitary.mul_star_self_of_mem (u i).prop⟩

local instance instCStarAlgebraSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions : CStarAlgebra (lp (fun _ : ℕ => B) ∞) where

section Positive
variable [PartialOrder B] [StarOrderedRing B]

local instance instPartialOrderSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions : PartialOrder (lp (fun _ : ℕ => B) ∞) := CStarAlgebra.spectralOrder _
local instance instNontrivialSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions_rffde6c_1 : Nontrivial (lp (fun _ : ℕ => B) ∞) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have he := congrArg (fun X : lp (fun _ : ℕ => B) ∞ => X 0) h
  exact zero_ne_one he
local instance instStarOrderedRingSubtypePreLpNatMemAddSubgroupLpTopENNReal_solutions : StarOrderedRing (lp (fun _ : ℕ => B) ∞) := CStarAlgebra.spectralOrderedRing _

/-- Restrict a positive functional on bounded families to the constants. -/
def grothendieckRestrict (f : lp (fun _ : ℕ => B) ∞ →ₚ[ℂ] ℂ) : B →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (f.toLinearMap.comp grothendieckConstant.toLinearMap) (fun b hb => by
    obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
    change 0 ≤ f (grothendieckConstant (star c * c))
    rw [map_mul, map_star]
    exact f.map_nonneg (star_mul_self_nonneg _))

end Positive

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicColumnTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense cyclic orbits give the bounded column tests needed for the
matrix derivation estimate. The unit vector may vary with the test. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped ComplexOrder Topology

variable {A K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The shifted square root is the single input vector for the regularized column. -/
def cyclicShiftVector (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) (ε : ℝ) : K :=
  σ (cyclicColumnRoot a + ε • (1 : A)) Ω

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralBaseTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectrum of a norm-separable commutative C-star algebra is a
compact metrizable base for its vector spectral measures. -/

noncomputable section
namespace KadisonSimilarity

variable (A : Type*) [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]

theorem characterSpace_metrizable :
    TopologicalSpace.MetrizableSpace (WeakDual.characterSpace ℂ A) := by
  apply WeakDual.metrizable_of_isCompact ℂ A
  exact isCompact_iff_compactSpace.mpr inferInstance

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SquareArrayPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Zero padding of Hilbert arrays

The coordinate inclusion along an arbitrary finite injection is isometric.
Extension of an operator by zero consequently preserves scalar commutator
norms and the norms of their matrix amplifications. No dimension factor occurs.
-/

noncomputable section
namespace KadisonSimilarity

section ContractiveRetraction

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Extension by zero along an isometric, contractively split inclusion has
exactly the original operator norm. -/
theorem norm_split_extension (J : E →L[ℂ] F) (R : F →L[ℂ] E)
    (hJ : ‖J‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hRJ : R.comp J = ContinuousLinearMap.id ℂ E) (T : E →L[ℂ] E) :
    ‖J.comp (T.comp R)‖ = ‖T‖ := by
  have hbound (S : E →L[ℂ] E) : ‖J.comp (S.comp R)‖ ≤ ‖S‖ := by
    calc
      _ ≤ ‖J‖ * (‖S‖ * ‖R‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _))
      _ ≤ 1 * (‖S‖ * 1) := by gcongr
      _ = ‖S‖ := by ring
  apply le_antisymm (hbound T)
  have hrecover : R.comp ((J.comp (T.comp R)).comp J) = T := by
    simp only [← ContinuousLinearMap.comp_assoc, hRJ, ContinuousLinearMap.id_comp]
    simp only [ContinuousLinearMap.comp_assoc, hRJ, ContinuousLinearMap.comp_id]
  calc
    ‖T‖ = ‖R.comp ((J.comp (T.comp R)).comp J)‖ := congrArg norm hrecover.symm
    _ ≤ ‖R‖ * (‖J.comp (T.comp R)‖ * ‖J‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (‖J.comp (T.comp R)‖ * 1) := by gcongr
    _ = ‖J.comp (T.comp R)‖ := by ring

end ContractiveRetraction

section MatrixIndices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {r m : ℕ}

/-- Entrywise zero extension of a square operator matrix. -/
def padOperatorMatrix (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) :
    Matrix (Fin m) (Fin m) (H →L[ℂ] H) :=
  fun i j => ∑ p : Fin r, ∑ q : Fin r,
    if i = e p ∧ j = e q then X p q else 0

end MatrixIndices

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_CStarMatrixPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isometric zero padding of C-star matrices

Padding along an injection is a nonunital star algebra monomorphism. Its
isometry follows from the C-star norm theorem, and its represented action is
the concrete zero extension on finite Hilbert sums.
-/

noncomputable section
namespace KadisonSimilarity

section AlgebraicPadding

variable {A : Type*} [CStarAlgebra A] {r m : ℕ}

/-- A square matrix with zero entries outside the embedded index set. -/
def matrixZeroPadding (e : Fin r ↪ Fin m) (X : Matrix (Fin r) (Fin r) A) :
    Matrix (Fin m) (Fin m) A :=
  fun i j => ∑ p : Fin r, ∑ q : Fin r,
    if i = e p ∧ j = e q then X p q else 0

@[simp] theorem matrixZeroPadding_apply_image (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) A) (i j : Fin r) :
    matrixZeroPadding e X (e i) (e j) = X i j := by
  simp [matrixZeroPadding, e.injective.eq_iff, ite_and]

theorem matrixZeroPadding_not_mem_left (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) A) (i j : Fin m) (hi : i ∉ Set.range e) :
    matrixZeroPadding e X i j = 0 := by
  have h (p : Fin r) : i ≠ e p := fun hp => hi ⟨p, hp.symm⟩
  simp [matrixZeroPadding, h]

theorem matrixZeroPadding_not_mem_right (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) A) (i j : Fin m) (hj : j ∉ Set.range e) :
    matrixZeroPadding e X i j = 0 := by
  have h (q : Fin r) : j ≠ e q := fun hq => hj ⟨q, hq.symm⟩
  simp [matrixZeroPadding, h]

theorem matrixPadding_sum {M : Type*} [AddCommMonoid M]
    (e : Fin r ↪ Fin m) (f : Fin m → M)
    (hf : ∀ j, j ∉ Set.range e → f j = 0) :
    ∑ j : Fin m, f j = ∑ i : Fin r, f (e i) := by
  calc
    _ = ∑ j ∈ Finset.univ.map e, f j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      apply hf
      rintro ⟨i, rfl⟩
      exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    _ = _ := by rw [Finset.sum_map]

theorem matrixZeroPadding_mul (e : Fin r ↪ Fin m)
    (X Y : Matrix (Fin r) (Fin r) A) :
    matrixZeroPadding e (X * Y) = matrixZeroPadding e X * matrixZeroPadding e Y := by
  ext i j
  by_cases hi : i ∈ Set.range e
  · obtain ⟨p, rfl⟩ := hi
    by_cases hj : j ∈ Set.range e
    · obtain ⟨q, rfl⟩ := hj
      rw [matrixZeroPadding_apply_image, Matrix.mul_apply, Matrix.mul_apply]
      rw [matrixPadding_sum e _ (by
        intro k hk
        rw [matrixZeroPadding_not_mem_right e X (e p) k hk, zero_mul])]
      simp only [matrixZeroPadding_apply_image]
    · rw [matrixZeroPadding_not_mem_right e (X * Y) (e p) j hj, Matrix.mul_apply]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [matrixZeroPadding_not_mem_right e Y k j hj, mul_zero]
  · rw [matrixZeroPadding_not_mem_left e (X * Y) i j hi, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [matrixZeroPadding_not_mem_left e X i k hi, zero_mul]

theorem matrixZeroPadding_star (e : Fin r ↪ Fin m)
    (X : Matrix (Fin r) (Fin r) A) :
    matrixZeroPadding e (star X) = star (matrixZeroPadding e X) := by
  ext i j
  change matrixZeroPadding e (star X) i j = star (matrixZeroPadding e X j i)
  by_cases hi : i ∈ Set.range e
  · obtain ⟨p, rfl⟩ := hi
    by_cases hj : j ∈ Set.range e
    · obtain ⟨q, rfl⟩ := hj
      simp only [matrixZeroPadding_apply_image, Matrix.star_apply]
    · rw [matrixZeroPadding_not_mem_right e (star X) (e p) j hj,
        matrixZeroPadding_not_mem_left e X j (e p) hj, star_zero]
  · rw [matrixZeroPadding_not_mem_left e (star X) i j hi,
      matrixZeroPadding_not_mem_right e X j i hi, star_zero]

/-- The algebraic zero-padding map, before assigning the C-star matrix norm. -/
def matrixZeroPaddingHom (e : Fin r ↪ Fin m) :
    Matrix (Fin r) (Fin r) A →⋆ₙₐ[ℂ] Matrix (Fin m) (Fin m) A where
  toFun := matrixZeroPadding e
  map_zero' := by ext i j; simp [matrixZeroPadding]
  map_add' X Y := by
    ext i j
    simp only [matrixZeroPadding, Matrix.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  map_smul' c X := by
    ext i j
    simp only [matrixZeroPadding, Matrix.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  map_mul' := matrixZeroPadding_mul e
  map_star' := matrixZeroPadding_star e

end AlgebraicPadding

section CStarPadding

variable {A : Type*} [CStarAlgebra A] {r m : ℕ}

/-- Zero padding with the actual C-star matrix norms. -/
def cstarMatrixPadding (e : Fin r ↪ Fin m) :
    CStarMatrix (Fin r) (Fin r) A →⋆ₙₐ[ℂ] CStarMatrix (Fin m) (Fin m) A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toNonUnitalStarAlgHom.comp
    ((matrixZeroPaddingHom e).comp
      CStarMatrix.ofMatrixStarAlgEquiv.symm.toNonUnitalStarAlgHom)

@[simp] theorem cstarMatrixPadding_apply (e : Fin r ↪ Fin m)
    (X : CStarMatrix (Fin r) (Fin r) A) (i j : Fin m) :
    cstarMatrixPadding e X i j = matrixZeroPadding e (CStarMatrix.ofMatrix.symm X) i j := rfl

@[simp] theorem cstarMatrixPadding_apply_image (e : Fin r ↪ Fin m)
    (X : CStarMatrix (Fin r) (Fin r) A) (i j : Fin r) :
    cstarMatrixPadding e X (e i) (e j) = X i j := by
  simp only [cstarMatrixPadding_apply, matrixZeroPadding_apply_image,
    CStarMatrix.ofMatrix_symm_apply]

theorem cstarMatrixPadding_injective (e : Fin r ↪ Fin m) :
    Function.Injective (cstarMatrixPadding (A := A) e) := by
  intro X Y h
  ext i j
  have he := congrArg (fun Z : CStarMatrix (Fin m) (Fin m) A => Z (e i) (e j)) h
  simpa only [cstarMatrixPadding_apply_image] using he

variable [PartialOrder A] [StarOrderedRing A]

/-- No norm or dimension factor is lost by matrix zero padding. -/
@[simp] theorem norm_cstarMatrixPadding (e : Fin r ↪ Fin m)
    (X : CStarMatrix (Fin r) (Fin r) A) : ‖cstarMatrixPadding e X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (cstarMatrixPadding e) (cstarMatrixPadding_injective e) X

end CStarPadding

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

/-- A matrix unit with row `a` and column `b`. -/
def tensorMatrixUnit (a b : α) : Matrix α α ℂ :=
  fun r c => if r = a ∧ c = b then 1 else 0

omit [Fintype α] in
@[simp] theorem tensorMatrixUnit_apply (a b r c : α) :
    tensorMatrixUnit a b r c = if r = a ∧ c = b then 1 else 0 := rfl

/-- Distinct labels assigned to the vertices of a permutation give its test
tuple of matrix units. -/
def permutationTest (j : ι → α) (π : Equiv.Perm ι) : ι → Matrix α α ℂ :=
  fun i => tensorMatrixUnit (j i) (j (π i))

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

/-- A permutation fixing `i` preserves the complement of `i`. -/
def fixedPointComplement (π : Equiv.Perm ι) (i : ι) (hi : π i = i)
    (j : {j : ι // j ≠ i}) : {j : ι // j ≠ i} :=
  ⟨π j, fun h => j.2 (π.injective (h.trans hi.symm))⟩

/-- The contraction over all slots except a distinguished fixed point. -/
def fixedPointRemainder (π : Equiv.Perm ι) (i : ι) (hi : π i = i)
    (v : ι → Matrix α α ℂ) : ℂ :=
  ∑ g : {j : ι // j ≠ i} → α,
    ∏ j : {j : ι // j ≠ i}, v j (g j) (g (fixedPointComplement π i hi j))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From finite-stage pairings to permutation operators

The operator classification follows from the finite-stage coefficient
identity, using density, same-side-pair elimination, and completed tensor
permutations. The finite-stage identity remains a separately stated prerequisite.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Source letters precede all test letters in the orientation of a pair. -/
def sourceFirstRank {k l : ℕ} : Fin k ⊕ Fin l → ℕ :=
  Sum.elim Fin.val (fun j => k + j.val)

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

omit [Fintype ι] [DecidableEq ι] in
theorem optionPerm_some (π : Equiv.Perm (Option ι)) (hnone : π none = none)
    (i : ι) : ∃ j, π (some i) = some j := by
  cases h : π (some i) with
  | none => exact False.elim (Option.some_ne_none i (π.injective (h.trans hnone.symm)))
  | some j => exact ⟨j, rfl⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantIntertwiners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix realization of the invariant-intertwiner argument

Finite coefficient forms are constructed from explicit Hilbert-space matrix
realizations. Normalized Hilbert--Schmidt inner products supply the matrix-unit
norms, while left matrix actions supply endpoint transfer. The sole invariant
theory input remains finite-dimensional Schur--Weyl spanning.
-/

noncomputable section
namespace KadisonSimilarity

variable {E F α : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [Fintype α] [DecidableEq α]

omit [Fintype α] in
@[simp] theorem tensorMatrixUnit_eq_single (a b : α) :
    tensorMatrixUnit a b = Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [tensorMatrixUnit, Matrix.single_apply]
  simp only [eq_comm]

omit [Fintype α] in
@[simp] theorem star_tensorMatrixUnit (a b : α) :
    star (tensorMatrixUnit a b) = tensorMatrixUnit b a := by
  ext i j
  change star (tensorMatrixUnit a b j i) = tensorMatrixUnit b a i j
  simp only [tensorMatrixUnit, and_comm]
  split_ifs <;> simp

@[simp] theorem tensorMatrixUnit_mul (a b c : α) :
    tensorMatrixUnit a b * tensorMatrixUnit b c = tensorMatrixUnit a c := by
  simp only [tensorMatrixUnit_eq_single, Matrix.single_mul_single_same, one_mul]

@[simp] theorem trace_tensorMatrixUnit (a : α) :
    Matrix.trace (tensorMatrixUnit a a) = 1 := by
  rw [tensorMatrixUnit_eq_single, Matrix.trace_single_eq_same]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicSpectralSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal cyclic decomposition of a commutative representation,
expressed as an actual Hilbert sum of scalar spectral L² spaces. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : Type*} [CommCStarAlgebra A]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))

local instance spectralSumMeasurable : MeasurableSpace (WeakDual.characterSpace ℂ A) :=
  borel (WeakDual.characterSpace ℂ A)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_DerivationDefectSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reducing defect space of a factorized derivation. It will provide
the sharp implementing operator in the commutant-distance formula. -/

noncomputable section
namespace KadisonSimilarity
open scoped Topology

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def derivationDefect (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (a : A) : H →L[ℂ] K :=
  (π a).comp W - W.comp (σ a)

def derivationDefectSpace (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) : ClosedSubmodule ℂ K :=
  (Submodule.span ℂ (Set.range fun p : A × H => derivationDefect σ π W p.1 p.2)).closure

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_SimilarityMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative positive metric from an invertible star intertwiner

This is the final geometric step of Paulsen's theorem. The intertwiner may
map to a different Hilbert space. Its positive metric on the original space
and its positive square root yield the actual similarity unit, with exactly
the product of the forward and inverse operator norms.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap
open scoped ComplexOrder

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The metric of a bounded linear isomorphism has an explicit inverse. -/
def intertwinerMetricUnit (W : H →L[ℂ] K) (L : K →L[ℂ] H)
    (hLW : L.comp W = 1) (hWL : W.comp L = 1) : (H →L[ℂ] H)ˣ where
  val := W.adjoint.comp W
  inv := L.comp L.adjoint
  val_inv := by
    change W.adjoint.comp (W.comp (L.comp L.adjoint)) = 1
    rw [← comp_assoc W L, hWL, one_def, id_comp]
    rw [← adjoint_comp, hLW, adjoint_one]
  inv_val := by
    change L.comp (L.adjoint.comp (W.adjoint.comp W)) = 1
    rw [← comp_assoc L.adjoint W.adjoint, ← adjoint_comp, hWL, adjoint_one,
      one_def, id_comp, hLW]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_FactorizationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reducing space generated by a homomorphism factorization

Only the vectors generated by the right factor are needed. Multiplicativity
makes the left factor an intertwiner on this closed span. Its kernel is then
a reducing subspace, which is the geometric input to invertible similarity.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The closed cyclic span of the range of the right factor. -/
def factorizationSpace (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) :
    ClosedSubmodule ℂ K :=
  (Submodule.span ℂ (Set.range fun p : A × H => σ p.1 (W p.2))).closure

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ReducingRepresentationTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transfer from a reducing representation to a larger one. Extension
by zero preserves scalar and matrix commutator norms, so a standard-form
embedding costs no constant in the finite-factor estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
  (I : H →ₗᵢ[ℂ] K)
  (hI : ∀ a, I.toContinuousLinearMap.comp (σ a) =
    (ρ a).comp I.toContinuousLinearMap)

/-- Extension by zero of the operator under study. -/
def reducingExtension (Y : H →L[ℂ] H) : K →L[ℂ] K :=
  I.toContinuousLinearMap.comp (Y.comp I.toContinuousLinearMap.adjoint)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralCutBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative high spectral cuts. The discarded part has small operator
norm, and positivity bounds the trace of the retained projection. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Trace
open Filter
open scoped Topology

local instance spectralCut_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

end Trace
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HankelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite Hankel test in the similarity manuscript

The coefficients here are the actual Fourier coefficients of the narrow-arc
function in Section `hankel`: `sin (l θ) / (π l)`, with `θ = 1/(2N)`.
The lower bound uses the constant vector in the first `N` coordinates.
No assertion about the free-product construction is assumed here.
-/

noncomputable section

namespace KadisonSimilarity

open Finset

/-- The angular half-width used in the manuscript. -/
def arcWidth (N : ℕ) : ℝ := 1 / (2 * N)

/-- A positive Fourier coefficient of the centered narrow-arc indicator. -/
def arcCoefficient (N l : ℕ) : ℝ :=
  Real.sin (l * arcWidth N) / (Real.pi * l)

/-- The actual `N × N` Hankel block tested in the manuscript. -/
def arcHankelMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun j k => arcCoefficient N (j.val + k.val + 1)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ArcFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered arc, its exact second moment, and its nonzero Fourier
coefficients, computed using normalized angular Lebesgue integration. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Set

/-- The real Fourier coefficient, including the centered zero frequency. -/
def realArcFourierCoefficient (θ : ℝ) (l : ℤ) : ℝ :=
  if l = 0 then 0 else Real.sin (l * θ) / (Real.pi * l)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralPolynomialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Haar and reflection-coset moments determine all polynomial moments
of the real part of a dihedral rotation. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

/-- Angular characters with the sign convention of `arcFourierIntegral`. -/
def angularCharacter (l : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (((l : ℝ) * x : ℝ) * Complex.I)

/-- Normalized angular moments of powers of the real coordinate. -/
def angularPowerMoment (n : ℕ) (l : ℤ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ x in -Real.pi..Real.pi,
    (Real.cos x : ℂ) ^ n * angularCharacter l x

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_AngularIntegralBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Norm control for the normalized angular Fourier integrals used in
the spectral-arc construction. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

def angularIntegral (f : ℝ → ℂ) (l : ℤ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ x in -Real.pi..Real.pi, f x * angularCharacter l x

@[simp] theorem norm_angularCharacter (l : ℤ) (x : ℝ) :
    ‖angularCharacter l x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralSupportLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive resolvent approximations to the concrete range-support
projection. This gives the strong limit needed for the dihedral arc's
spectral moments, with operator norm bounded by one throughout. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def supportResolvent (B : H →L[ℂ] H) (ε : ℝ) : H →L[ℂ] H :=
  B * positiveShiftReciprocal B ε

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SpectralArcResolvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous functions approximating the open arc spectral projection. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology
open Filter

/-- The positive resolvent approximation to the open cut `(c,∞)`. -/
def spectralCutFunction (c ε t : ℝ) : ℝ := (t - c)⁺ / ((t - c)⁺ + ε)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact dihedral word identity and the finite Fourier matrix entries. -/

noncomputable section
namespace KadisonSimilarity

section Algebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The trace-orthogonal projection onto the span of a centered symmetry. -/
def symmetryExpectation (τ : R →ₗ[ℂ] ℂ) (s : R) : R →ₗ[ℂ] R where
  toFun x := τ x • 1 + τ (s * x) • s
  map_add' x y := by simp only [mul_add, map_add, add_smul]; abel
  map_smul' c x := by
    simp only [mul_smul_comm, map_smul, smul_add, smul_smul, RingHom.id_apply,
      smul_eq_mul]

@[simp] theorem symmetryExpectation_apply (τ : R →ₗ[ℂ] ℂ) (s x : R) :
    symmetryExpectation τ s x = τ x • 1 + τ (s * x) • s := rfl

end Algebra
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralArcProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete projection underlying the centered dihedral arc.  Its
Fourier moments are separate from the operator construction: the projection
is the open spectral cut of the real part of the rotation at `cos θ`.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The open centered angular arc, expressed as a spectral cut of the real part. -/
def dihedralArcProjection (w : H →L[ℂ] H) (θ : ℝ) : H →L[ℂ] H :=
  upperSpectralCut (realPart w) (Real.cos θ)

/-- The actual centered operator used for the Haar arc. -/
def centeredDihedralArc (w : H →L[ℂ] H) (θ : ℝ) : H →L[ℂ] H :=
  dihedralArcProjection w θ - (θ / Real.pi) • 1

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralCutMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from the continuous Haar functional calculus to the actual
open spectral projection, using its bounded strong resolvent limit. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def regularizer (n : ℕ) : ℝ := (1 / 2) ^ n

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


def IsState {A : Type u} [CStarAlgebra A] (f : A →L[ℂ] ℂ) : Prop :=
  ‖f‖ = 1 ∧ ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re

section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] theorem gns_apply_coe (f : A →ₚ[ℂ] ℂ) (a b : A) :
    f.gnsStarAlgHom a (f.toPreGNS b : f.GNS) = (f.toPreGNS (a * b) : f.GNS) := by
  simp [PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.gnsNonUnitalStarAlgHom,
    ContinuousLinearMap.completion_apply_coe, PositiveLinearMap.leftMulMapPreGNS]

def Peaks (p : ℕ → A) (f : A →L[ℂ] ℂ) : Prop :=
  (∀ n, IsStarProjection (p n)) ∧ Antitone p ∧ IsState f ∧
    (∀ n, f (p n) = 1) ∧
    ∀ g : A →L[ℂ] ℂ, IsState g → (∀ n, g (p n) = 1) → g = f

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def starAlgHomCLM (φ : A →⋆ₐ[ℂ] B) : A →L[ℂ] B :=
  φ.toAlgHom.toLinearMap.mkContinuous 1 (fun a => by
    change ‖φ a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ a)

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def dominatedPreGNS (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) :
    f.PreGNS →L[ℂ] g.PreGNS :=
  (g.toPreGNS.toLinearMap.comp f.ofPreGNS.toLinearMap).mkContinuous (Real.sqrt C) fun x => by
    change √(g (star (f.ofPreGNS x) * f.ofPreGNS x)).re ≤
      √C * √(f (star (f.ofPreGNS x) * f.ofPreGNS x)).re
    rw [← Real.sqrt_mul hC]
    exact Real.sqrt_le_sqrt (hdom _)

end GNS

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_States
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

def cornerSubalgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | e * a = a ∧ a * e = a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    simp [mul_add, add_mul, ha, hb, ha', hb']
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    exact ⟨by rw [← mul_assoc, ha], by rw [mul_assoc, hb']⟩
  smul_mem' := by
    rintro z a ⟨ha,ha'⟩
    exact ⟨by rw [mul_smul_comm, ha], by rw [smul_mul_assoc, ha']⟩
  star_mem' := by
    rintro a ⟨ha,ha'⟩
    constructor
    · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star ha'
    · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star ha

instance cornerClosed : IsClosed (cornerSubalgebra e he : Set A) := by
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

abbrev CStarCorner := cornerSubalgebra e he

instance cornerOne : One (CStarCorner e he) :=
  ⟨⟨e, he.isIdempotentElem.eq, he.isIdempotentElem.eq⟩⟩

@[simp] theorem corner_coe_one : ((1 : CStarCorner e he) : A) = e := rfl

instance cornerRing : Ring (CStarCorner e he) := {
  (inferInstance : NonUnitalRing (CStarCorner e he)) with
  one := 1
  one_mul a := Subtype.ext a.2.1
  mul_one a := Subtype.ext a.2.2
  natCast n := n • (1 : CStarCorner e he)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast z := z • (1 : CStarCorner e he)
  intCast_ofNat n := ofNat_zsmul _ _
  intCast_negSucc n := by
    change (Int.negSucc n) • (1 : CStarCorner e he) = -((n+1) • (1 : CStarCorner e he))
    rw [Int.negSucc_eq, neg_zsmul]
    congr 1
    exact ofNat_zsmul (1 : CStarCorner e he) (n+1) }

instance cornerNormedRing : NormedRing (CStarCorner e he) := {
  (inferInstance : NonUnitalNormedRing (CStarCorner e he)), cornerRing e he with }

instance cornerAlgebra : Algebra ℂ (CStarCorner e he) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance cornerCStarAlgebra : CStarAlgebra (CStarCorner e he) := {
  (inferInstance : NonUnitalCStarAlgebra (CStarCorner e he)),
  cornerNormedRing e he, cornerAlgebra e he with }

instance cornerPartialOrder : PartialOrder (CStarCorner e he) :=
  CStarAlgebra.spectralOrder _

instance cornerStarOrderedRing : StarOrderedRing (CStarCorner e he) :=
  CStarAlgebra.spectralOrderedRing _

def cornerCompression : A →L[ℂ] CStarCorner e he where
  toFun a := ⟨e*a*e, by
    constructor
    · rw [← mul_assoc, ← mul_assoc, he.isIdempotentElem.eq]
    · rw [mul_assoc (e*a), he.isIdempotentElem.eq]⟩
  map_add' a b := Subtype.ext (by
    change e*(a+b)*e = e*a*e+e*b*e
    simp only [mul_add, add_mul])
  map_smul' z a := Subtype.ext (by
    change e*(z • a)*e = z • (e*a*e)
    simp only [mul_smul_comm, smul_mul_assoc])
  cont := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_id).mul continuous_const

@[simp] theorem cornerCompression_coe (a : A) :
    (cornerCompression e he a : A) = e*a*e := rfl

@[simp] theorem cornerCompression_corner (a : CStarCorner e he) :
    cornerCompression e he (a : A) = a := by
  apply Subtype.ext
  exact (congrArg (· * e) a.2.1).trans a.2.2

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def weakStates (A : Type*) [CStarAlgebra A] : Set (WeakDual ℂ A) :=
  {f | IsState f.toStrongDual}

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def cornerFunctional (f : A →L[ℂ] ℂ) (p : A) : A →L[ℂ] ℂ :=
  f.comp (ContinuousLinearMap.mulLeftRight ℂ A p p)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cornerFunctional_apply (f : A →L[ℂ] ℂ) (p a : A) :
    cornerFunctional f p a = f (p * a * p) := rfl

def cornerState (f : A →L[ℂ] ℂ) (p : A) : A →L[ℂ] ℂ :=
  (f p).re⁻¹ • cornerFunctional f p

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cornerState_apply (f : A →L[ℂ] ℂ) (p a : A) :
    cornerState f p a = (f p).re⁻¹ • f (p * a * p) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem state_projection_real (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p : A) (hp : IsStarProjection p) : f p = ((f p).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, Complex.ofReal_im]
      using (hf.2 p).1

theorem cornerState_eq_one (f : A →L[ℂ] ℂ) (hf : IsState f)
    (q p : A) (hq : IsStarProjection q) (hp : IsStarProjection p) (hqp : q ≤ p)
    (hpos : 0 < (f q).re) : cornerState f q p = 1 := by
  rw [cornerState_apply, (hq.le_iff_mul_eq_left hp).mp hqp, hq.isIdempotentElem.eq,
    state_projection_real f hf q hq]
  simp only [Complex.ofReal_re]
  rw [Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hpos), Complex.ofReal_one]

def peakAtom (p : ℕ → A) (n : ℕ) : A := p n - p (n + 1)

theorem Peaks.peakAtom_projection {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (n : ℕ) :
    IsStarProjection (peakAtom p n) :=
  ((hp.1 (n+1)).le_iff_sub (hp.1 n)).mp (hp.2.1 (Nat.le_succ n))

theorem Peaks.peakAtom_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (n : ℕ) :
    peakAtom p n ≤ p n := by
  exact sub_le_self _ (hp.1 (n+1)).nonneg

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem selfAdjoint_nonneg_of_norm_one (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ g a := by
  have hau : (a : A) ≤ ‖a‖ • (1 : A) := by
    change (a : A) ≤ ‖(a : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap (a : A) (norm_nonneg _) ha).mp le_rfl
  have hpos : 0 ≤ ‖a‖ • (1 : A) - (a : A) := sub_nonneg.mpr hau
  have hnorm : ‖‖a‖ • (1 : selfAdjoint A) - a‖ ≤ ‖a‖ := by
    change ‖‖a‖ • (1 : A) - (a : A)‖ ≤ ‖a‖
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hpos).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_le_self (‖a‖ • (1 : A)) ha
  have hb := g.le_opNorm (‖a‖ • (1 : selfAdjoint A) - a)
  have hc : ‖g (‖a‖ • (1 : selfAdjoint A) - a)‖ ≤ ‖a‖ :=
    hb.trans ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans (by simpa using hnorm))
  rw [map_sub, map_smul, h1, smul_eq_mul, mul_one, Real.norm_eq_abs] at hc
  have h := (le_abs_self _).trans hc
  linarith

def selfAdjointComplexify (g : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (g (realPart a) : ℂ) + Complex.I * (g (imaginaryPart a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add, mul_add]; ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem selfAdjointComplexify_coe (g : selfAdjoint A →ₗ[ℝ] ℝ) (a : selfAdjoint A) :
    selfAdjointComplexify g (a : A) = (g a : ℂ) := by
  simp [selfAdjointComplexify]

def selfAdjointPositive (g : selfAdjoint A →L[ℝ] ℝ) (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) :
    A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (selfAdjointComplexify g.toLinearMap) fun a ha => by
    let x : selfAdjoint A := ⟨a, ha.isSelfAdjoint⟩
    change 0 ≤ selfAdjointComplexify g.toLinearMap (x : A)
    rw [selfAdjointComplexify_coe]
    exact ⟨selfAdjoint_nonneg_of_norm_one g hg h1 x ha, by simp⟩

@[simp] theorem selfAdjointPositive_coe (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) (a : selfAdjoint A) :
    selfAdjointPositive g hg h1 (a : A) = (g a : ℂ) :=
  selfAdjointComplexify_coe _ _

@[simp] theorem selfAdjointPositive_one (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) : selfAdjointPositive g hg h1 1 = 1 := by
  simpa only [selfAdjoint.val_one, h1, Complex.ofReal_one] using selfAdjointPositive_coe g hg h1 1

def selfAdjointSubspace (S : StarSubalgebra ℂ A) : Submodule ℝ A :=
  (S.toSubalgebra.toSubmodule.restrictScalars ℝ) ⊓ selfAdjoint.submodule ℝ A

def selfAdjointSubspaceInclusion (S : StarSubalgebra ℂ A) :
    selfAdjointSubspace S →L[ℝ] S :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨a.val, a.property.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun a => by simp [one_mul])

open scoped ComplexOrder InnerProductSpace ComplexStarModule
open UniformSpace

open scoped Topology
open Filter

variable {A : Type*} [CStarAlgebra A] {ι : Type*}

theorem orthogonalProjection_commute (p : ι → A)
    (horth : Pairwise (fun i j => p i * p j = 0)) (i j : ι) : Commute (p i) (p j) := by
  by_cases h : i = j
  · subst j; exact Commute.refl _
  · exact (horth h).trans (horth (Ne.symm h)).symm

theorem normal_orthogonalProjection_sum (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ι → ℂ) (s : Finset ι) :
    IsStarNormal (∑ i ∈ s, c i • p i) := by
  constructor
  rw [star_sum]
  apply Commute.sum_left
  intro i hi
  apply Commute.sum_right
  intro j hj
  rw [star_smul, (hp i).isSelfAdjoint.star_eq]
  exact (orthogonalProjection_commute p horth i j).smul_left (star (c i)) |>.smul_right (c j)

theorem norm_orthogonalProjection_sum_le (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ι → ℂ) (s : Finset ι)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i ∈ s, ‖c i‖ ≤ C) : ‖∑ i ∈ s, c i • p i‖ ≤ C := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hC
  | @insert i s his ih =>
    rw [Finset.sum_insert his]
    have hn : IsStarNormal (c i • p i) := by
      let : IsStarNormal (p i) := (hp i).isSelfAdjoint.isStarNormal
      infer_instance
    have hs := normal_orthogonalProjection_sum p hp horth c s
    have hab : (c i • p i) * (∑ j ∈ s, c j • p j) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [smul_mul_assoc, mul_smul_comm, horth (ne_of_mem_of_not_mem hj his).symm,
        smul_zero]
    have hcomm : Commute (c i • p i) (∑ j ∈ s, c j • p j) := by
      apply Commute.sum_right
      intro j hj
      exact (orthogonalProjection_commute p horth i j).smul_left _ |>.smul_right _
    rw [hn.norm_add_eq_max hs hcomm hab]
    apply max_le
    · calc
        ‖c i • p i‖ = ‖c i‖ * ‖p i‖ := norm_smul _ _
        _ ≤ ‖c i‖ * 1 := mul_le_mul_of_nonneg_left ((hp i).norm_le _) (norm_nonneg _)
        _ ≤ C := by simpa using hc i (Finset.mem_insert_self _ _)
    · exact ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))

theorem summable_orthogonalProjection (p : ℕ → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ℕ → ℂ)
    (hc : Tendsto c atTop (𝓝 0)) : Summable (fun i => c i • p i) := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  have hsmall := (tendsto_zero_iff_norm_tendsto_zero.mp hc).eventually
    (Iio_mem_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨Finset.range N, fun s hs => ?_⟩
  apply lt_of_le_of_lt (norm_orthogonalProjection_sum_le p hp horth c s (ε/2)
    (le_of_lt (half_pos hε)) ?_) (half_lt_self hε)
  intro i hi
  apply le_of_lt (hN i _)
  by_contra h
  have hin : i ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge h)
  exact Finset.disjoint_left.mp hs hi hin

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.peakAtom_mul_peak {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    {i n : ℕ} (hin : i < n) : peakAtom p i * p n = 0 := by
  have h₁ := ((hp.1 n).le_iff_mul_eq_right (hp.1 i)).mp (hp.2.1 (Nat.le_of_lt hin))
  have h₂ := ((hp.1 n).le_iff_mul_eq_right (hp.1 (i+1))).mp (hp.2.1 hin)
  simp only [peakAtom, sub_mul, h₁, h₂, sub_self]

theorem Peaks.peak_mul_peakAtom {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    {i n : ℕ} (hin : i < n) : p n * peakAtom p i = 0 := by
  simpa only [star_mul, (hp.1 n).isSelfAdjoint.star_eq,
    (hp.peakAtom_projection i).isSelfAdjoint.star_eq, star_zero]
    using congrArg star (hp.peakAtom_mul_peak hin)

theorem Peaks.peakAtom_orthogonal {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) :
    Pairwise (fun i j => peakAtom p i * peakAtom p j = 0) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · change peakAtom p i * (p j - p (j+1)) = 0
    rw [mul_sub, hp.peakAtom_mul_peak h, hp.peakAtom_mul_peak (h.trans_le (Nat.le_succ j)),
      sub_self]
  · change (p i - p (i+1)) * peakAtom p j = 0
    rw [sub_mul, hp.peak_mul_peakAtom h, hp.peak_mul_peakAtom (h.trans_le (Nat.le_succ i)),
      sub_self]

omit [PartialOrder A] [StarOrderedRing A] in

theorem peakAtom_sum (p : ℕ → A) (n : ℕ) :
    ∑ i ∈ Finset.range n, peakAtom p i = p 0 - p n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, peakAtom]; abel

def peakDiagonal (p : ℕ → A) (c : ℂ) (b : ℕ → ℂ) : A :=
  c • (1 : A) + ∑' i, (b i - c) • peakAtom p i

omit [PartialOrder A] [StarOrderedRing A] in

theorem peakDiagonal_partial {p : ℕ → A} (hp0 : p 0 = 1)
    (c : ℂ) (b : ℕ → ℂ) (n : ℕ) :
    c • (1 : A) + ∑ i ∈ Finset.range n, (b i - c) • peakAtom p i =
      (∑ i ∈ Finset.range n, b i • peakAtom p i) + c • p n := by
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, peakAtom_sum, hp0, smul_sub]
  abel

theorem Peaks.norm_peakDiagonal_partial_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (c : ℂ) (b : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ‖c‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ C) (n : ℕ) :
    ‖c • (1 : A) + ∑ i ∈ Finset.range n, (b i - c) • peakAtom p i‖ ≤ C := by
  rw [peakDiagonal_partial hp0]
  have hs := normal_orthogonalProjection_sum _ hp.peakAtom_projection hp.peakAtom_orthogonal
    b (Finset.range n)
  have hn : IsStarNormal (c • p n) := by
    let : IsStarNormal (p n) := (hp.1 n).isSelfAdjoint.isStarNormal
    infer_instance
  have hzero : (∑ i ∈ Finset.range n, b i • peakAtom p i) * (c • p n) = 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [smul_mul_assoc, mul_smul_comm, hp.peakAtom_mul_peak (Finset.mem_range.mp hi),
      smul_zero]
  have hzero' : (c • p n) * (∑ i ∈ Finset.range n, b i • peakAtom p i) = 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [smul_mul_assoc, mul_smul_comm, hp.peak_mul_peakAtom (Finset.mem_range.mp hi),
      smul_zero]
  rw [hs.norm_add_eq_max hn (hzero.trans hzero'.symm) hzero]
  apply max_le
  · exact norm_orthogonalProjection_sum_le _ hp.peakAtom_projection hp.peakAtom_orthogonal
      b _ C hC (fun i _ => hb i)
  · calc
      ‖c • p n‖ = ‖c‖ * ‖p n‖ := norm_smul _ _
      _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left ((hp.1 n).norm_le _) (norm_nonneg _)
      _ ≤ C := by simpa using hc

theorem Peaks.tendsto_peakDiagonal {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (c : ℂ) (b : ℕ → ℂ) (hb : Tendsto b atTop (𝓝 c)) :
    Tendsto (fun n => c • (1 : A) + ∑ i ∈ Finset.range n, (b i - c) • peakAtom p i)
      atTop (𝓝 (peakDiagonal p c b)) := by
  apply tendsto_const_nhds.add
  exact (summable_orthogonalProjection _ hp.peakAtom_projection hp.peakAtom_orthogonal
    (fun i => b i - c) (by simpa using hb.sub_const c)).hasSum.tendsto_sum_nat

theorem Peaks.norm_peakDiagonal_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (c : ℂ) (b : ℕ → ℂ) (hb : Tendsto b atTop (𝓝 c))
    (C : ℝ) (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hbc : ∀ i, ‖b i‖ ≤ C) :
    ‖peakDiagonal p c b‖ ≤ C := by
  apply le_of_tendsto (hp.tendsto_peakDiagonal c b hb).norm
  exact Filter.Eventually.of_forall (hp.norm_peakDiagonal_partial_le hp0 c b C hC hc hbc)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def peakingExpectationFun (p : ℕ → A) (f τ : A →L[ℂ] ℂ) (a : A) : A :=
  peakDiagonal p (f a) (fun n => cornerState τ (peakAtom p n) a)

omit [PartialOrder A] [StarOrderedRing A] in

theorem peakingExpectationFun_smul (p : ℕ → A) (f τ : A →L[ℂ] ℂ) (c : ℂ) (a : A) :
    peakingExpectationFun p f τ (c • a) = c • peakingExpectationFun p f τ a := by
  simp only [peakingExpectationFun, peakDiagonal, map_smul, ← smul_sub]
  simp_rw [smul_assoc]
  rw [tsum_const_smul'', smul_add]

open scoped ComplexOrder MatrixOrder CStarAlgebra
open Matrix

open scoped CStarAlgebra

open Filter Topology
open scoped ComplexOrder ComplexStarModule

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_PolarPartialIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete right supports in a finite tracial von Neumann algebra

The partial isometry is constructed by extending the isometry
`sqrt(x* x) ξ ↦ x ξ` from its dense range and setting it to zero on the
orthogonal complement. Bicommutant closure keeps that operator in the algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The range map, with its codomain restricted to the closed range. -/
def rangeIntoClosure (B : H →L[ℂ] H) : H →ₗ[ℂ] operatorRangeClosure B :=
  B.toLinearMap.codRestrict _ (fun x =>
    Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

omit [CompleteSpace H] in
theorem rangeIntoClosure_dense (B : H →L[ℂ] H) : DenseRange (rangeIntoClosure B) := by
  change Dense (Set.range (rangeIntoClosure B))
  rw [Subtype.dense_iff, ← Set.range_comp]
  exact Set.Subset.rfl

/-- Positive square root used only for this polar factor. -/
def polarModulus (x : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (star x * x)

theorem polarModulus_selfAdjoint (x : H →L[ℂ] H) : IsSelfAdjoint (polarModulus x) :=
  (CFC.sqrt_nonneg _).isSelfAdjoint

theorem polarModulus_square (x : H →L[ℂ] H) : polarModulus x * polarModulus x = star x * x :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg x)

theorem polarModulus_norm_apply (x : H →L[ℂ] H) (ξ : H) :
    ‖polarModulus x ξ‖ = ‖x ξ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  have he : (polarModulus x).adjoint.comp (polarModulus x) = x.adjoint.comp x := by
    change star (polarModulus x) * polarModulus x = star x * x
    rw [(polarModulus_selfAdjoint x).star_eq, polarModulus_square]
  rw [he]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialUltrapowerActions
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded left-multiplier sequences reduce the tracial GNS subspace of
the Hilbert ultrapower. The compressed operator therefore inherits every
eventual coordinate commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

open scoped ENNReal Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- The actual uniformly bounded family of left multipliers. -/
def gnsLeftSequence (x : ℕ →ᵇ A) : lp (fun _ : ℕ => τ.GNS →L[ℂ] τ.GNS) ∞ :=
  ⟨fun i => τ.gnsStarAlgHom (x i), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨i, rfl⟩
    exact (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (x i)).trans
      (x.norm_coe_le_norm i)⟩⟩

@[simp] theorem gnsLeftSequence_apply (x : ℕ →ᵇ A) (i : ℕ) :
    gnsLeftSequence τ x i = τ.gnsStarAlgHom (x i) := rfl

@[simp] theorem gnsLeftSequence_star (x : ℕ →ᵇ A) :
    gnsLeftSequence τ (star x) = star (gnsLeftSequence τ x) := by
  apply Subtype.ext
  funext i
  exact map_star τ.gnsStarAlgHom (x i)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralRoundingDischarge
attribute [-instance] _root_.OAI.NaimarkZFC.cornerPartialOrder
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

/-- The actual half-threshold spectral projection. -/
def halfSpectralProjection (a : H →L[ℂ] H) : H →L[ℂ] H :=
  rangeSupport (2 * a - 1)⁺

section VonNeumann
variable (P : VonNeumannAlgebra H)

local instance roundingOrder : PartialOrder P.toStarSubalgebra := inferInstance

end VonNeumann

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialRightSupportDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right support trace bounds from the constructed polar partial isometry -/
noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Tracial
variable (P : VonNeumannAlgebra H)
local instance supportClosed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed P.carrier
  rw [← P.centralizer_centralizer']
  exact Set.isClosed_centralizer _
local instance supportCStar : CStarAlgebra P.toStarSubalgebra := inferInstance
local instance supportOrder : PartialOrder P.toStarSubalgebra := inferInstance

end Tracial

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

/-- A star homomorphism of C-star algebras preserves positivity. -/
theorem starAlgHom_preserves_nonneg (f : A →⋆ₐ[ℂ] B) {a : A} (ha : 0 ≤ a) : 0 ≤ f a := by
  obtain ⟨b, hb⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := a)).mp ha
  rw [hb, map_mul, map_star]
  exact star_mul_self_nonneg _

/-- Positive functional in the coordinates of the target algebra. -/
def transportedPositiveTrace (τ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] B) : B →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (τ.toLinearMap.comp e.symm.toStarAlgHom.toLinearMap)
    (fun _ hb => τ.map_nonneg (starAlgHom_preserves_nonneg e.symm.toStarAlgHom hb))

@[simp] theorem transportedPositiveTrace_apply (τ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] B) (b : B) :
    transportedPositiveTrace τ e b = τ (e.symm b) := rfl

@[simp] theorem transportedPositiveTrace_map (τ : A →ₚ[ℂ] ℂ) (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    transportedPositiveTrace τ e (e a) = τ a := by simp

end Equivalence

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductMatrixContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong continuity of the constructed finite matrix action follows from
ordinary factor-algebra density and the isometry bound; it is not an extra
free-product or Haar-averaging hypothesis. -/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology CStarAlgebra

section ContinuousOrbits
variable {Γ H : Type*} [TopologicalSpace Γ]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (U : Γ → H →L[ℂ] H)

/-- Vectors with continuous orbit form a linear subspace. -/
def continuousOrbitSubmodule : Submodule ℂ H where
  carrier := {x | Continuous (fun g => U g x)}
  zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using (continuous_const : Continuous (fun _ : Γ => (0 : H)))
  add_mem' hx hy := by simpa only [Set.mem_ofPred_eq, map_add] using hx.fun_add hy
  smul_mem' c _ hx := by simpa only [Set.mem_ofPred_eq, map_smul] using
    (continuous_const : Continuous (fun _ : Γ => c)).fun_smul hx

end ContinuousOrbits

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteSymmetrization
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite unitary averaging and weak-operator cluster points. These are the
analytic and algebraic symmetrization steps, before identifying the matrix
unitaries of the free-product model. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open Filter ContinuousLinearMapWOT

variable {Γ V H : Type*} [Fintype Γ] [Nonempty Γ]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Uniform average over a nonempty finite set. -/
def finiteMean (f : Γ → V) : V := (Fintype.card Γ : ℂ)⁻¹ • ∑ g, f g

@[simp] theorem finiteMean_const (v : V) : finiteMean (fun _ : Γ => v) = v := by
  simp only [finiteMean, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [Group Γ]

/-- The twirl associated to a finite unitary representation. Its inverse is
written using the group, so no adjoint identities are hidden in this definition. -/
def finiteTwirl (U : Γ →* (H →L[ℂ] H)) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  finiteMean (fun g => U g * T * U g⁻¹)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorIntegral
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

def integralOperatorForm (A : X → H →L[ℂ] H) : H → H → ℂ :=
  fun x y => ∫ g, inner ℂ (A g x) y ∂μ

omit [CompleteSpace H] in
theorem norm_integralOperatorForm_le (A : X → H →L[ℂ] H) {R : ℝ}
    (hA : ∀ g, ‖A g‖ ≤ R) (x y : H) :
    ‖integralOperatorForm μ A x y‖ ≤ R * ‖x‖ * ‖y‖ := by
  have hb : ∀ᵐ g ∂μ, ‖inner ℂ (A g x) y‖ ≤ R * ‖x‖ * ‖y‖ :=
    Filter.Eventually.of_forall fun g => calc
      _ ≤ ‖A g x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ (‖A g‖ * ‖x‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right ((A g).le_opNorm x) (norm_nonneg y)
      _ ≤ R * ‖x‖ * ‖y‖ := by gcongr; exact hA g
  simpa only [integralOperatorForm, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HaarSymmetrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar symmetrization, defined through weak scalar integrals. This applies
to the compact matrix-unitary actions used in the free-product argument. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {Γ H K : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (μ : Measure Γ) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

/-- The orbit of a bounded operator under a representation. -/
def unitaryConjugate (U : Γ →* (H →L[ℂ] H)) (T : H →L[ℂ] H) (g : Γ) :
    H →L[ℂ] H := U g * T * U g⁻¹

omit [MeasurableSpace Γ] [MeasurableMul Γ] [CompleteSpace H] in
theorem norm_unitaryConjugate_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H) (g : Γ) :
    ‖unitaryConjugate U T g‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖U g‖ * ‖T‖ * ‖U g⁻¹‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖T‖ * 1 := by gcongr; exact hU _; exact hU _
    _ = ‖T‖ := by ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalizedContractions
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Naturality of normalized permutation contractions under trace-preserving
matrix algebra maps, proved by deleting one permutation vertex at a time. -/

noncomputable section
namespace KadisonSimilarity

open Finset

universe u
variable {ι : Type u} {α β : Type*} [Fintype ι] [decι : DecidableEq ι]

/-- Insert one new vertex after `b` in its permutation cycle. -/
def insertPermutationVertex (p : Equiv.Perm ι) (b : ι) : Equiv.Perm (Option ι) :=
  Equiv.swap none (some (p b)) * p.optionCongr

omit [Fintype ι] in
@[simp] theorem insertPermutationVertex_none (p : Equiv.Perm ι) (b : ι) :
    insertPermutationVertex p b none = some (p b) := by
  simp [insertPermutationVertex, Equiv.Perm.mul_apply]

omit [Fintype ι] in
@[simp] theorem insertPermutationVertex_self (p : Equiv.Perm ι) (b : ι) :
    insertPermutationVertex p b (some b) = none := by
  simp [insertPermutationVertex, Equiv.Perm.mul_apply]

omit [Fintype ι] in
theorem insertPermutationVertex_other (p : Equiv.Perm ι) (b i : ι) (hi : i ≠ b) :
    insertPermutationVertex p b (some i) = some (p i) := by
  simp [insertPermutationVertex, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    p.injective.ne hi]

variable [Fintype α] [DecidableEq α]

/-- Splicing two adjacent slots multiplies their matrix arguments in cycle order. -/
def splicePermutationWord (v : Option ι → Matrix α α ℂ) (b : ι) : ι → Matrix α α ℂ :=
  Function.update (fun i => v (some i)) b (v (some b) * v none)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorMatrixAlgebra
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite tensor matrices and the invariance of permutation contractions.
These coordinate calculations supply the spanning generators for the local
Schur--Weyl argument. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The matrix of a tensor product of finitely many matrix operators. -/
def tupleTensorMatrix (v : ι → Matrix α α ℂ) : Matrix (ι → α) (ι → α) ℂ :=
  Matrix.of fun f g => ∏ i, v i (f i) (g i)

omit [DecidableEq ι] [Fintype α] [DecidableEq α] in
@[simp] theorem tupleTensorMatrix_apply (v : ι → Matrix α α ℂ) (f g : ι → α) :
    tupleTensorMatrix v f g = ∏ i, v i (f i) (g i) := rfl

omit [DecidableEq ι] [Fintype α] in
@[simp] theorem tupleTensorMatrix_one :
    tupleTensorMatrix (fun _ : ι => (1 : Matrix α α ℂ)) = 1 := by
  ext f g
  simp only [tupleTensorMatrix_apply, Matrix.one_apply, Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

omit [DecidableEq ι] [Fintype α] [DecidableEq α] in
@[simp] theorem tupleTensorMatrix_star (v : ι → Matrix α α ℂ) :
    tupleTensorMatrix (fun i => star (v i)) = star (tupleTensorMatrix v) := by
  ext f g
  simp [tupleTensorMatrix, Matrix.star_apply]

/-- Reordering the tensor coordinates. -/
def tensorCoordinatePermutation (π : Equiv.Perm ι) : Equiv.Perm (ι → α) where
  toFun f := fun i => f (π i)
  invFun f := fun i => f (π.symm i)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

/-- Its matrix uses the same successor convention as `permutationContraction`. -/
def tensorPermutationMatrix (π : Equiv.Perm ι) : Matrix (ι → α) (ι → α) ℂ :=
  Matrix.of fun f g => if f = tensorCoordinatePermutation π g then 1 else 0

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorCoefficientMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The trace-pairing bridge from invariant multilinear forms to the
commutant of finite tensor powers. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The transposed matrix-unit coefficients give the trace-dual matrix. -/
def tensorCoefficientMatrix
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ) :
    Matrix (ι → α) (ι → α) ℂ :=
  Matrix.of fun f g => F (fun i => tensorMatrixUnit (g i) (f i))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorDiagonalWeights
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal unitary phases separate the multiplicity weights of a finite
tensor power. This is the weight calculation in the Schur--Weyl argument. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The multiplicity of a label in an elementary tensor. -/
def tensorLabelCount (f : ι → α) (a : α) : ℕ := Fintype.card {i // f i = a}

/-- A scalar diagonal whose entries lie on the unit circle. -/
def tensorDiagonalUnitary (d : α → unitary ℂ) : Matrix.unitaryGroup α ℂ :=
  ⟨Matrix.diagonal (fun a => (d a : ℂ)), by
    constructor <;> ext i j <;> by_cases hij : i = j
    · subst j
      simpa only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul, Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.one_apply_eq,
        Complex.star_def] using (d i).property.1
    · simp [Matrix.star_eq_conjTranspose, hij]
    · subst j
      simpa only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.mul_diagonal, Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.one_apply_eq,
        Complex.star_def] using (d i).property.2
    · simp [Matrix.star_eq_conjTranspose, hij]⟩

def tensorRoot (n : ℕ) : unitary ℂ :=
  let z := Complex.exp (2 * Real.pi * Complex.I / n)
  have hn : ‖z‖ = 1 := by
    dsimp [z]
    have he : (2 * (Real.pi : ℂ) * Complex.I / n) =
        ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he]
    exact Complex.norm_exp_ofReal_mul_I _
  have hz : star z * z = 1 := by
    change starRingEnd ℂ z * z = 1
    rw [Complex.conj_mul', hn]
    norm_num
  ⟨z, hz, by rw [mul_comm]; exact hz⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorCommutantExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending a tensor commutation identity from unitary matrices to all
matrices. Diagonal weights, Hermitian diagonalization and a polynomial
identity suffice; no decomposition of a general matrix is assumed. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

def tensorCommutatorPolynomial (C : Matrix (ι → α) (ι → α) ℂ)
    (a b : Matrix α α ℂ) (f g : ι → α) : Polynomial ℂ :=
  (∑ h : ι → α, Polynomial.C (C f h) *
    ∏ i, (Polynomial.C (a (h i) (g i)) + Polynomial.X * Polynomial.C (b (h i) (g i)))) -
  ∑ h : ι → α, (∏ i, (Polynomial.C (a (f i) (h i)) +
    Polynomial.X * Polynomial.C (b (f i) (h i)))) * Polynomial.C (C h g)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorStableSpanning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Schur--Weyl spanning in the stable range needed after taking a cofinal
tail of the matrix tower. The proof uses a single column with distinct labels. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

def tensorColumnTransfer (j f : ι → α) : Matrix α α ℂ :=
  ∑ i, Matrix.single (f i) (j i) 1

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixCovariance
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

include htrace in
omit [StarModule ℂ R] in
theorem trace_matrix_conjugation (u : Matrix.unitaryGroup α ℂ) (a : R) :
    τ (ι (u : Matrix α α ℂ) * a * star (ι (u : Matrix α α ℂ))) = τ a := by
  rw [htrace, ← mul_assoc, ← map_star ι, ← map_mul ι,
    Unitary.coe_star_mul_self, map_one, one_mul]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalSpectralTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing normal trace norm forces any convergent fixed-vector orbit
to have zero limit, by cutting off its high left spectrum. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance normalTruncation_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_NormalCyclicGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A faithful normal finite trace makes the cyclic orbit map closable.
The proof removes a high spectral projection of vanishing trace, leaving
an arbitrarily small operator applied to the fixed cyclic vector. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H K E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance normalCyclic_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_QuadraticSandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The separation step in Haagerup's cyclic-similarity argument. Equal
finite square sums with comparable orbit norms give a positive functional
between the corresponding quadratic forms. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def listSquareSum (L : List A) : selfAdjoint A :=
  (L.map fun a => (⟨star a * a, (star_mul_self_nonneg a).isSelfAdjoint⟩ : selfAdjoint A)).sum

def listOrbitSum (π : BoundedUnitalHom A H) (ξ : H) (L : List A) : ℝ :=
  (L.map fun a => ‖π.1 a ξ‖ ^ 2).sum

@[simp] theorem listSquareSum_nil : listSquareSum ([] : List A) = 0 := rfl
@[simp] theorem listSquareSum_singleton_coe (a : A) :
    (listSquareSum [a] : A) = star a * a := by simp [listSquareSum]
omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
@[simp] theorem listOrbitSum_nil (π : BoundedUnitalHom A H) (ξ : H) :
    listOrbitSum π ξ [] = 0 := rfl

@[simp] theorem listSquareSum_append (L K : List A) :
    listSquareSum (L ++ K) = listSquareSum L + listSquareSum K := by
  simp [listSquareSum]

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
@[simp] theorem listOrbitSum_append (π : BoundedUnitalHom A H) (ξ : H) (L K : List A) :
    listOrbitSum π ξ (L ++ K) = listOrbitSum π ξ L + listOrbitSum π ξ K := by
  simp [listOrbitSum]

theorem listSquareSum_scale (r : ℝ) (hr : 0 ≤ r) (L : List A) :
    listSquareSum (L.map fun a => Real.sqrt r • a) = r • listSquareSum L := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, listSquareSum, List.sum_cons] at ih ⊢
    rw [ih, smul_add]
    congr 1
    apply Subtype.ext
    change star (Real.sqrt r • a) * (Real.sqrt r • a) = r • (star a * a)
    rw [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, Real.mul_self_sqrt hr]

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
theorem listOrbitSum_scale (π : BoundedUnitalHom A H) (ξ : H)
    (r : ℝ) (hr : 0 ≤ r) (L : List A) :
    listOrbitSum π ξ (L.map fun a => Real.sqrt r • a) = r * listOrbitSum π ξ L := by
  have he (a : A) : ‖π.1 (Real.sqrt r • a) ξ‖ ^ 2 = r * ‖π.1 a ξ‖ ^ 2 := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, smul_apply,
      norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg r), mul_pow,
      Real.sq_sqrt hr]
  simp only [listOrbitSum, List.map_map, Function.comp_def, he]
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

def orbitSandwichCone (π : BoundedUnitalHom A H) (ξ : H) (K : ℝ) :
    PointedCone ℝ (selfAdjoint A × ℝ) where
  carrier := {z | ∃ a b : List A,
    z.1 = listSquareSum a - listSquareSum b ∧
      z.2 ≤ listOrbitSum π ξ a - K * listOrbitSum π ξ b}
  zero_mem' := ⟨[], [], by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hx, hr⟩ ⟨c, d, hy, hs⟩
    refine ⟨a ++ c, b ++ d, ?_, ?_⟩
    · simp only [Prod.fst_add, listSquareSum_append, hx, hy]; abel
    · simp only [Prod.snd_add, listOrbitSum_append]
      linarith
  smul_mem' := by
    rintro ⟨r, hr⟩ x ⟨a, b, hx, hs⟩
    refine ⟨a.map (fun c => Real.sqrt r • c), b.map (fun c => Real.sqrt r • c), ?_, ?_⟩
    · simp only [Prod.smul_fst, Nonneg.mk_smul, listSquareSum_scale r hr, hx, smul_sub]
    · simp only [Prod.smul_snd, Nonneg.mk_smul, smul_eq_mul, listOrbitSum_scale π ξ r hr]
      nlinarith [mul_le_mul_of_nonneg_left hs hr]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ClosedFamilySpan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual closed spans and elementary tensors of total families. -/

noncomputable section
namespace KadisonSimilarity

variable {I J E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem map_mem_of_total (v : I → E)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (f : E →L[ℂ] F) (S : ClosedSubmodule ℂ F) (h : ∀ i, f (v i) ∈ S) (x : E) :
    f x ∈ S := by
  have hs : Submodule.span ℂ (Set.range v) ≤ S.toSubmodule.comap f.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  have hc := (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal hs
    (S.isClosed.preimage f.continuous)
  rw [hv] at hc
  exact hc (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ E))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_LeadingWordGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complement of the words starting in one factor consists exactly of
the nonempty words starting in the other factor. -/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem orthogonal_eq_of_dense_sup (S T : ClosedSubmodule ℂ E)
    (ho : ∀ (x : S) (y : T), inner ℂ (x : E) (y : E) = 0)
    (hd : (S.toSubmodule ⊔ T.toSubmodule).topologicalClosure = ⊤) :
    S.toSubmoduleᗮ = T.toSubmodule := by
  apply le_antisymm
  · intro x hx
    let r := x - T.toSubmodule.starProjection x
    have hT : r ∈ T.toSubmoduleᗮ := T.toSubmodule.sub_starProjection_mem_orthogonal x
    have hp : T.toSubmodule.starProjection x ∈ S.toSubmoduleᗮ := by
      intro y hy
      exact ho ⟨y, hy⟩ ⟨_, T.toSubmodule.starProjection_apply_mem x⟩
    have hS : r ∈ S.toSubmoduleᗮ := S.toSubmoduleᗮ.sub_mem hx hp
    have hker : S.toSubmodule ⊔ T.toSubmodule ≤ (innerSL ℂ r).ker := by
      apply sup_le
      · intro y hy
        exact Submodule.inner_left_of_mem_orthogonal hy hS
      · intro y hy
        exact Submodule.inner_left_of_mem_orthogonal hy hT
    have hc := (S.toSubmodule ⊔ T.toSubmodule).topologicalClosure_minimal hker
      (innerSL ℂ r).isClosed_ker
    rw [hd] at hc
    have hz : r = 0 := inner_self_eq_zero.mp (hc (Submodule.mem_top : r ∈ (⊤ : Submodule ℂ E)))
    have he : x = T.toSubmodule.starProjection x := sub_eq_zero.mp hz
    rw [he]
    exact T.toSubmodule.starProjection_apply_mem x
  · intro y hy x hx
    exact ho ⟨x, hx⟩ ⟨y, hy⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CompressionSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite head coordinates and the tail projection for compression. -/

noncomputable section
namespace KadisonSimilarity

section Projections
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def isometryRangeProjection (j : E →ₗᵢ[ℂ] F) : F →L[ℂ] F :=
  j.toContinuousLinearMap.comp j.toContinuousLinearMap.adjoint

theorem isometryRangeProjection_adjoint (j : E →ₗᵢ[ℂ] F) :
    (isometryRangeProjection j).adjoint = isometryRangeProjection j := by
  simp only [isometryRangeProjection, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem isometryRangeProjection_sq (j : E →ₗᵢ[ℂ] F) :
    isometryRangeProjection j * isometryRangeProjection j = isometryRangeProjection j := by
  let J := j.toContinuousLinearMap
  have hj : J.adjoint.comp J = 1 := j.adjoint_comp_self
  change (J.comp J.adjoint).comp (J.comp J.adjoint) = J.comp J.adjoint
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc J.adjoint J,
    hj, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

theorem isometryRangeProjection_norm (j : E →ₗᵢ[ℂ] F) :
    ‖isometryRangeProjection j‖ ≤ 1 := by
  have hj : ‖j.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [LinearIsometry.coe_toContinuousLinearMap, j.norm_map, one_mul, le_refl]
  calc
    _ ≤ ‖j.toContinuousLinearMap‖ * ‖j.toContinuousLinearMap.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖j.toContinuousLinearMap‖ * ‖j.toContinuousLinearMap‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * 1 := mul_le_mul hj hj (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem isometryRangeProjection_apply (j : E →ₗᵢ[ℂ] F) (x : E) :
    isometryRangeProjection j (j x) = j x := by
  change j (j.toContinuousLinearMap.adjoint (j x)) = j x
  have h := congrArg (fun f : E →L[ℂ] E => f x) j.adjoint_comp_self
  exact congrArg j h

theorem subtypeRangeProjection (S : ClosedSubmodule ℂ E) [CompleteSpace S.toSubmodule] :
    isometryRangeProjection S.toSubmodule.subtypeₗᵢ = S.toSubmodule.starProjection := by
  change S.toSubmodule.subtypeL.comp S.toSubmodule.subtypeL.adjoint = _
  rw [S.toSubmodule.adjoint_subtypeL]
  rfl

end Projections

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CompressionProjectionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal inclusion projections in the head tensor coordinates. -/

noncomputable section
namespace KadisonSimilarity

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isometryRangeProjection_comp (j : E →ₗᵢ[ℂ] F) (u : F →ₗᵢ[ℂ] K) :
    isometryRangeProjection (u.comp j) = u.toContinuousLinearMap.comp
      ((isometryRangeProjection j).comp u.toContinuousLinearMap.adjoint) := by
  change (u.toContinuousLinearMap.comp j.toContinuousLinearMap).comp
    (u.toContinuousLinearMap.comp j.toContinuousLinearMap).adjoint = _
  simp only [ContinuousLinearMap.adjoint_comp, isometryRangeProjection,
    ContinuousLinearMap.comp_assoc]

theorem isometryRangeProjection_complement (u : E ≃ₗᵢ[ℂ] F)
    (S T : ClosedSubmodule ℂ E) [CompleteSpace S.toSubmodule] [CompleteSpace T.toSubmodule]
    (hST : S.toSubmoduleᗮ = T.toSubmodule) :
    isometryRangeProjection (u.toLinearIsometry.comp S.toSubmodule.subtypeₗᵢ) =
      1 - isometryRangeProjection (u.toLinearIsometry.comp T.toSubmodule.subtypeₗᵢ) := by
  have hp : S.toSubmodule.starProjection = 1 - T.toSubmodule.starProjection := by
    have ht : T.toSubmodule.starProjection = 1 - S.toSubmodule.starProjection := by
      simpa only [hST] using (Submodule.starProjection_orthogonal' S.toSubmodule)
    rw [ht]
    abel
  rw [isometryRangeProjection_comp, isometryRangeProjection_comp,
    subtypeRangeProjection, subtypeRangeProjection, hp]
  have huadj : u.toLinearIsometry.toContinuousLinearMap.adjoint =
      u.symm.toLinearIsometry.toContinuousLinearMap := u.adjoint_eq_symm
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, huadj]
  have hu : u.toLinearIsometry.toContinuousLinearMap.comp
      u.symm.toLinearIsometry.toContinuousLinearMap = 1 := by
    ext x
    exact u.apply_symm_apply x
  rw [hu, ContinuousLinearMap.one_def]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SeparableRepresentationTests
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common contraction tests for representations

A norm-dense sequence in the unit ball of a separable C-star algebra works in
every representation. The proved finite-vector Kaplansky theorem extends its
weak-operator closure to the unit ball of the represented bicommutant. This
does not require normality of a representation or of a pointwise fiber map.
-/

noncomputable section

namespace KadisonSimilarity

open ContinuousLinearMapWOT Filter
open scoped Topology CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite-vector strong approximation implies membership in the weak
operator closure. -/
theorem mem_weak_closure_of_finite_strong_approximation
    (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (happrox : ∀ (s : Finset H) (ε : ℝ), 0 < ε →
      ∃ R ∈ S, ∀ x ∈ s, ‖R x - T x‖ < ε) :
    ofCLM T ∈ closure (ofCLM '' S) := by
  classical
  have hex (j : Finset H × ℕ) :
      ∃ R ∈ S, ∀ x ∈ j.1, ‖R x - T x‖ < 1 / (j.2 + 1 : ℝ) :=
    happrox j.1 _ (by positivity)
  choose R hR hclose using hex
  have hstrong (x : H) : Tendsto (fun j => R j x) atTop (𝓝 (T x)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨({x}, N), ?_⟩
    intro j hj
    have hx : x ∈ j.1 := hj.1 (by simp)
    rw [dist_eq_norm]
    apply (hclose j x hx).trans_le
    exact (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hj.2 1)).trans hN.le
  have hweak : Tendsto (fun j => ofCLM (R j)) atTop (𝓝 (ofCLM T)) := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro x y
    exact tendsto_const_nhds.inner (hstrong x)
  exact mem_closure_of_tendsto hweak (Eventually.of_forall fun j => ⟨R j, hR j, rfl⟩)

variable {A : Type*} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]

/-- Choose one sequence in the source unit ball, dense for its norm topology. -/
theorem exists_norm_dense_contraction_tests :
    ∃ test : ℕ → A, (∀ n, ‖test n‖ ≤ 1) ∧
      ∀ a : A, ‖a‖ ≤ 1 → a ∈ closure (Set.range test) := by
  let B := {a : A // ‖a‖ ≤ 1}
  let : Nonempty B := ⟨⟨0, by simp⟩⟩
  let : SecondCountableTopology B :=
    (show Topology.IsEmbedding (Subtype.val : B → A) from
      Topology.IsEmbedding.subtypeVal).secondCountableTopology
  let : TopologicalSpace.SeparableSpace B := inferInstance
  let d : ℕ → B := TopologicalSpace.denseSeq B
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq B
  refine ⟨fun n => (d n).val, fun n => (d n).property, ?_⟩
  intro a ha
  exact map_mem_closure (f := (Subtype.val : B → A)) continuous_subtype_val
    (hd ⟨a, ha⟩) (by rintro _ ⟨n, rfl⟩; exact ⟨n, rfl⟩)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DenseStarRepresentation
attribute [-instance] _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending the pointwise algebra in a fiber

This is the norm-continuity step in Blackadar, III.5.1.11. A contractive
unital ring representation on a dense subring extends to the C-star algebra.
Preservation of star and of `i · 1` makes that extension a complex star
representation. Countability is needed only to gather almost-everywhere
relations on a common conull set, not for the extension itself.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology CStarAlgebra

variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem denseSubring_uniformContinuous
    (S : Subring A) (f : S →+* (H →L[ℂ] H))
    (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖) : UniformContinuous f := by
  apply (AddMonoidHomClass.lipschitz_of_bound f 1 ?_).uniformContinuous
  intro a
  simpa only [one_mul] using hnorm a

/-- The uniform extension, retaining its ring structure. -/
def denseSubringRepresentation (S : Subring A) (hdense : Dense (S : Set A))
    (f : S →+* (H →L[ℂ] H)) (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖) :
    A →+* (H →L[ℂ] H) :=
  IsDenseInducing.extendRingHom (i := S.subtype)
    isUniformEmbedding_subtype_val.isUniformInducing hdense.denseRange_val
    (denseSubring_uniformContinuous S f hnorm)

@[simp] theorem denseSubringRepresentation_apply
    (S : Subring A) (hdense : Dense (S : Set A))
    (f : S →+* (H →L[ℂ] H)) (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖) (a : S) :
    denseSubringRepresentation S hdense f hnorm a = f a :=
  IsDenseInducing.extend_eq
    (isUniformEmbedding_subtype_val.isUniformInducing.isDenseInducing hdense.denseRange_val)
    (denseSubring_uniformContinuous S f hnorm).continuous a

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

theorem countable_addSubgroupClosure {G : Type*} [AddCommGroup G] {s : Set G}
    (hs : s.Countable) : (AddSubgroup.closure s : Set G).Countable := by
  let : Countable s := hs.to_subtype
  let f : FreeAbelianGroup s →+ G := FreeAbelianGroup.lift (fun x : s => (x : G))
  have hle : AddSubgroup.closure s ≤ f.range := (AddSubgroup.closure_le f.range).2 fun x hx => by
    exact ⟨FreeAbelianGroup.of ⟨x, hx⟩, FreeAbelianGroup.lift_apply_of _ _⟩
  exact (Set.countable_range f).mono hle

/-- A separable complex normed space has a countable dense additive subgroup
that is stable under multiplication by `i`. -/
theorem exists_countable_dense_complex_addSubgroup
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ S : AddSubgroup E, (S : Set E).Countable ∧ Dense (S : Set E) ∧
      ∀ x ∈ S, Complex.I • x ∈ S := by
  let s := Set.range (TopologicalSpace.denseSeq E)
  let t := s ∪ (fun x : E => Complex.I • x) '' s
  let S := AddSubgroup.closure t
  have hs : s.Countable := Set.countable_range _
  refine ⟨S, countable_addSubgroupClosure (hs.union (hs.image _)), ?_, ?_⟩
  · exact (TopologicalSpace.denseRange_denseSeq E).mono fun x hx =>
      AddSubgroup.subset_closure (Or.inl hx)
  · intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
        rcases hx with hx | ⟨y, hy, rfl⟩
        · exact AddSubgroup.subset_closure (Or.inr ⟨x, hx, rfl⟩)
        · simpa only [smul_smul, Complex.I_mul_I, neg_one_smul] using
            (AddSubgroup.closure t).neg_mem (AddSubgroup.subset_closure (Or.inl hy))
    | zero => simpa only [smul_zero] using S.zero_mem
    | add x y _ _ hx hy => simpa only [smul_add] using S.add_mem hx hy
    | neg x _ hx => simpa only [smul_neg] using S.neg_mem hx

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFieldAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise action on all L² vectors

The field reconstructed from constant columns acts pointwise on arbitrary
L² vectors. Indicator constants give a dense class; two successive AE
subsequences prove that the pointwise-action identity is norm closed.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [IsFiniteMeasure μ] [CompleteSpace H] in
/-- Pointwise action by any family of continuous operators is a closed
condition on L² vectors for a fixed bounded operator. -/
theorem isClosed_pointwise_operator_action
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (field : Ω → H →L[ℂ] H) :
    IsClosed {f : Lp H 2 μ | ∀ᵐ a ∂μ, T f a = field a (f a)} := by
  apply IsSeqClosed.isClosed
  intro f g hf hlim
  obtain ⟨s, hs, hsae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have ht : Tendsto (fun n => T (f (s n))) atTop (𝓝 (T g)) :=
    (T.continuous.tendsto g).comp (hlim.comp hs.tendsto_atTop)
  obtain ⟨t, htmono, htae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have heq : ∀ᵐ a ∂μ, ∀ n : ℕ,
      T (f (s (t n))) a = field a (f (s (t n)) a) :=
    eventually_countable_forall.mpr (fun n => hf (s (t n)))
  filter_upwards [hsae, htae, heq] with a ha hta he
  have hr := ((field a).continuous.tendsto (g a)).comp (ha.comp htmono.tendsto_atTop)
  have hefun : (fun n => T (f (s (t n))) a) =
      (fun n => field a (f (s (t n)) a)) := funext he
  rw [hefun] at hta
  exact tendsto_nhds_unique hta hr

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_BoundedMeasurableField
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded measurable operator fields on L²

Strong measurability of each constant column suffices to apply a field to
an arbitrary L² vector. An almost-everywhere uniform bound then constructs
the actual bounded L² operator, with its pointwise action and localization
commutation proved directly. No norm measurability of the operator field
is required.
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Measurability of constant columns extends to simple-vector sections. -/
theorem aestronglyMeasurable_field_simple
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (f : SimpleFunc Ω H) : AEStronglyMeasurable (fun a => R a (f a)) μ := by
  classical
  induction f using SimpleFunc.induction' with
  | const x => simpa only [SimpleFunc.const_apply] using hR x
  | @pcw f g s hs hf hg =>
    have heq : (fun a => R a (f.piecewise s hs g a)) =
        s.piecewise (fun a => R a (f a)) (fun a => R a (g a)) := by
      funext a
      by_cases ha : a ∈ s <;> simp [SimpleFunc.piecewise_apply, ha]
    rw [heq]
    exact hf.restrict.piecewise hs hg.restrict

/-- Only the strong operator measurability of the field is needed for
applying it to a measurable vector section. -/
theorem aestronglyMeasurable_field_apply
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    {f : Ω → H} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun a => R a (f a)) μ := by
  let g := hf.mk f
  have hg : StronglyMeasurable g := hf.stronglyMeasurable_mk
  have hlim : AEStronglyMeasurable (fun a => R a (g a)) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => aestronglyMeasurable_field_simple μ R hR (hg.approx n))
    exact Eventually.of_forall fun a =>
      ((R a).continuous.tendsto (g a)).comp (hg.tendsto_approx a)
  apply hlim.congr
  filter_upwards [hf.ae_eq_mk] with a ha
  exact congrArg (R a) ha.symm

/-- An essentially bounded field sends L² sections to L² sections. -/
theorem boundedField_memLp
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) :
    MemLp (fun a => R a (f a)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := C)
    (aestronglyMeasurable_field_apply μ R hR (Lp.aestronglyMeasurable f))
  filter_upwards [hbound] with a ha
  exact ((R a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))

/-- The L² section obtained by applying an essentially bounded field. -/
def boundedFieldVector
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) : Lp H 2 μ :=
  (boundedField_memLp μ R hR C hbound f).toLp (fun a => R a (f a))

theorem boundedFieldVector_ae
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) :
    boundedFieldVector μ R hR C hbound f =ᵐ[μ] fun a => R a (f a) :=
  MemLp.coeFn_toLp _

def boundedFieldLinear
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ where
  toFun := boundedFieldVector μ R hR C hbound
  map_add' f g := by
    apply Lp.ext
    filter_upwards [boundedFieldVector_ae μ R hR C hbound (f + g),
      boundedFieldVector_ae μ R hR C hbound f, boundedFieldVector_ae μ R hR C hbound g,
      Lp.coeFn_add f g, Lp.coeFn_add (boundedFieldVector μ R hR C hbound f)
        (boundedFieldVector μ R hR C hbound g)] with a hfg hf hg hin hout
    rw [hfg, hout, hin]
    simp only [Pi.add_apply, map_add, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [boundedFieldVector_ae μ R hR C hbound (c • f),
      boundedFieldVector_ae μ R hR C hbound f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (boundedFieldVector μ R hR C hbound f)] with a hcf hf hin hout
    change boundedFieldVector μ R hR C hbound (c • f) a =
      (c • boundedFieldVector μ R hR C hbound f) a
    rw [hcf, hout, hin]
    simp only [Pi.smul_apply, map_smul, hf]

theorem boundedFieldVector_norm_le
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) :
    ‖boundedFieldVector μ R hR C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedFieldVector_ae μ R hR C hbound f, hbound] with a ha hb
  rw [ha]
  exact ((R a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- The bounded L² operator associated to an essentially bounded strongly
operator measurable field. -/
def boundedFieldOperator
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  (boundedFieldLinear μ R hR C hbound).mkContinuous C
    (boundedFieldVector_norm_le μ R hR C hbound)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CentralSymmetrization
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

theorem intUnit_eq_one_or_neg_one (g : ℤˣ) : g = 1 ∨ g = -1 := by
  exact Int.units_eq_one_or g

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConcreteIrreducibleSubfactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Irreducible increasing matrix subfactors in the normal tracial GNS
representation. The matrix refinement theorem is applied after deriving
separability of that representation from the given predual. -/

noncomputable section
namespace KadisonSimilarity

open UltrapowerBridge
open scoped ComplexOrder

theorem scalar_center_of_starEquiv {A B : Type*}
    [Ring A] [StarRing A] [Algebra ℂ A] [Ring B] [StarRing B] [Algebra ℂ B]
    (e : A ≃⋆ₐ[ℂ] B)
    (h : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • (1 : A)) :
    ∀ c : B, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • (1 : B) := by
  intro c hc
  obtain ⟨b, rfl⟩ := e.surjective c
  change ∀ a : B, a * e b = e b * a at hc
  have hb (a : A) : a * b = b * a := by
    apply e.injective
    change e (a * b) = e (b * a)
    rw [map_mul e a b, map_mul e b a]
    exact hc (e a)
  obtain ⟨z, hz⟩ := h b hb
  refine ⟨z, ?_⟩
  change e b = z • (1 : B)
  rw [hz, map_smul, map_one]

theorem diffuse_projections_of_starEquiv {A B : Type*}
    [Ring A] [StarRing A] [Algebra ℂ A] [Ring B] [StarRing B] [Algebra ℂ B]
    (e : A ≃⋆ₐ[ℂ] B)
    (h : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    ∀ p : B, IsStarProjection p → p ≠ 0 →
      ∃ q : B, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  intro p hp hp0
  obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := h (e.symm p) (hp.map e.symm)
    (fun hz => hp0 (by simpa only [map_zero, e.apply_symm_apply] using congrArg e hz))
  refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply hq0
    apply e.injective
    change e q = e 0
    simpa only [map_zero] using hz
  · exact fun hz => hqp (by simpa only [e.symm_apply_apply] using congrArg e.symm hz)
  · simpa only [map_mul, e.apply_symm_apply] using congrArg e hpq
  · simpa only [map_mul, e.apply_symm_apply] using congrArg e hqp'

universe u

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConullRepresentationExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the original algebra's conull fiber representations by zero.
The maps remain nonunital star homomorphisms at every base point, so their
unit projections give genuine representations on every projection fiber. -/

noncomputable section
namespace KadisonSimilarity

variable {Ω B F : Type*} [CStarAlgebra B]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (s : Set Ω)

def zeroExtendNonunitalRepresentation
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (x : Ω) : B →⋆ₙₐ[ℂ] (F →L[ℂ] F) := by
  classical
  exact if h : x ∈ s then
    (ρ ⟨x, h⟩).toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ B)
  else 0

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountablyGeneratedCStarAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A separable C-star algebra generating a separably represented algebra

The complex linear span of the words in a countable family and its adjoints
is separable. Its norm closure is therefore a separable C-star algebra.
Applying this to the countable weakly dense contraction tests gives an
actual norm-separable C-star subalgebra whose bicommutant is the original
von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMapWOT
open scoped Topology Pointwise

variable {A : Type*} [CStarAlgebra A]

/-- The concrete norm-closed C-star algebra generated by a sequence. -/
abbrev sequenceGeneratedCStarAlgebra (g : ℕ → A) : StarSubalgebra ℂ A :=
  (StarAlgebra.adjoin ℂ (Set.range g)).topologicalClosure

instance sequenceGeneratedCStarAlgebra_isClosed (g : ℕ → A) :
    IsClosed (sequenceGeneratedCStarAlgebra g : Set A) :=
  StarSubalgebra.isClosed_topologicalClosure _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_HilbertSumIsometries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate isometries preserve orthogonality when composing a Hilbert sum. -/

noncomputable section
namespace KadisonSimilarity

variable {ι : Type*} {E F : ι → Type*} {H : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem orthogonalFamily_comp_isometries (V : ∀ i, F i →ₗᵢ[ℂ] H)
    (hV : OrthogonalFamily ℂ F V) (J : ∀ i, E i →ₗᵢ[ℂ] F i) :
    OrthogonalFamily ℂ E (fun i => (V i).comp (J i)) := by
  intro i j hij x y
  exact hV hij (J i x) (J j y)

def hilbertSumTransport [∀ i, CompleteSpace (E i)] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : ∀ i, E i →ₗᵢ[ℂ] H) (hV : IsHilbertSum ℂ E V)
    (W : ∀ i, E i →ₗᵢ[ℂ] K) (hW : OrthogonalFamily ℂ E W) : H →ₗᵢ[ℂ] K :=
  hW.linearIsometry.comp hV.linearIsometryEquiv.toLinearIsometry

theorem hilbertSum_transport_component [∀ i, CompleteSpace (E i)] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : ∀ i, E i →ₗᵢ[ℂ] H) (hV : IsHilbertSum ℂ E V)
    (W : ∀ i, E i →ₗᵢ[ℂ] K) (hW : OrthogonalFamily ℂ E W)
    (i : ι) (x : E i) :
    hilbertSumTransport V hV W hW (V i x) = W i x := by
  classical
  rw [← hV.linearIsometryEquiv_symm_apply_single x]
  change hW.linearIsometry
    (hV.linearIsometryEquiv (hV.linearIsometryEquiv.symm
      (lp.single (E := E) 2 i x))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, hW.linearIsometry_apply_single]

def hilbertSumTransportWithComponents [∀ i, CompleteSpace (E i)] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : ∀ i, E i →ₗᵢ[ℂ] H) (hV : IsHilbertSum ℂ E V)
    (W : ∀ i, E i →ₗᵢ[ℂ] K) (hW : OrthogonalFamily ℂ E W) :
    {J : H →ₗᵢ[ℂ] K // ∀ i x, J (V i x) = W i x} :=
  ⟨hilbertSumTransport V hV W hW, hilbertSum_transport_component V hV W hW⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_FiniteFactorSymmetrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-factor averaging stage uses actual normalized Haar measures
on the finite matrix-unitary groups. Their continuity and weak integrability
are proved here; the resulting operator is within the original scalar
commutator bound and has scalar commutator bound at most three times it. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory TopologicalSpace
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

section SingleStage

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Restriction of a matrix representation to its unitary group. -/
def matrixUnitaryAction (R : Matrix α α ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    Matrix.unitaryGroup α ℂ →* (H →L[ℂ] H) :=
  R.toMonoidHom.comp (unitary (Matrix α α ℂ)).subtype

end SingleStage

local instance finiteMatrixUnitaryCompactSpace (n : ℕ) :
    CompactSpace (Matrix.unitaryGroup (I n) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi Set.univ fun _ : I n =>
      Set.pi Set.univ fun _ : I n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  apply hK.of_isClosed_subset (isClosed_unitary (R := Matrix (I n) (I n) ℂ))
  intro x hx i _ j _
  change dist (x i j) 0 ≤ 1
  rw [dist_zero_right]
  exact entry_norm_bound_of_unitary hx i j

local instance finiteMatrixUnitaryMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (I n) ℂ) := borel _
local instance finiteMatrixUnitaryBorelSpace (n : ℕ) :
    BorelSpace (Matrix.unitaryGroup (I n) ℂ) := ⟨rfl⟩

/-- Normalized Haar measure on each actual finite matrix-unitary group. -/
def finiteMatrixHaarProbability (n : ℕ) : Measure (Matrix.unitaryGroup (I n) ℂ) :=
  Measure.haarMeasure ⊤

instance finiteMatrixHaarProbability_probability (n : ℕ) :
    IsProbabilityMeasure (finiteMatrixHaarProbability (I := I) n) := by
  apply IsProbabilityMeasure.mk
  exact Measure.haarMeasure_self
    (K₀ := (⊤ : PositiveCompacts (Matrix.unitaryGroup (I n) ℂ)))

instance finiteMatrixHaarProbability_leftInvariant (n : ℕ) :
    (finiteMatrixHaarProbability (I := I) n).IsMulLeftInvariant :=
  inferInstanceAs (Measure.haarMeasure
    (⊤ : PositiveCompacts (Matrix.unitaryGroup (I n) ℂ))).IsMulLeftInvariant

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalStandardEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The standard embedding of a separable concrete finite algebra is
constructed from its faithful normal GNS trace. No vector-realization or
standard-embedding result is an additional hypothesis. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

local instance normalEmbedding_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixSmallCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished scalar matrix corner has the original algebra's
commutator estimate on a finite standard multiplicity. The proof uses
actual coordinate insertion/projection and then transports the estimate
to the normalized matrix GNS space. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

/-- A diagonal scalar matrix unit in the actual C-star matrix algebra. -/
def matrixCornerProjection (i : Fin n) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.single i i 1)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialStageCommutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Commutation with all matrix stages extends to the represented source
by density of trace vectors in the actual normal ambient algebra. -/

noncomputable section
namespace KadisonSimilarity
open UltrapowerBridge
open scoped CStarAlgebra ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def relativeOperatorCommutant (N : VonNeumannAlgebra H) (Z : H →L[ℂ] H) :
    VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ ((N.commutant : Set (H →L[ℂ] H)) ∪ {Z})
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (Set.centralizer
      (((N.commutant : Set (H →L[ℂ] H)) ∪ {Z}) ∪
        star ((N.commutant : Set (H →L[ℂ] H)) ∪ {Z})))) = _
    exact Set.centralizer_centralizer_centralizer _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_JointCStarSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common separable source for an algebra and its commutant

Taking the norm closure of the joint star algebra preserves norm separability.
When the two sources generate `P` and `P'`, the common source generates the
commutant of the center. This puts both sources in one fiber representation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology

variable {A : Type*} [CStarAlgebra A]

/-- The norm-closed star algebra containing the two given sources. -/
abbrev jointCStarSource (B C : StarSubalgebra ℂ A) : StarSubalgebra ℂ A :=
  (B ⊔ C).topologicalClosure

instance jointCStarSource_isClosed (B C : StarSubalgebra ℂ A) :
    IsClosed (jointCStarSource B C : Set A) :=
  StarSubalgebra.isClosed_topologicalClosure _

theorem le_jointCStarSource_left (B C : StarSubalgebra ℂ A) :
    B ≤ jointCStarSource B C :=
  le_sup_left.trans (StarSubalgebra.le_topologicalClosure _)

theorem le_jointCStarSource_right (B C : StarSubalgebra ℂ A) :
    C ≤ jointCStarSource B C :=
  le_sup_right.trans (StarSubalgebra.le_topologicalClosure _)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_JointFiberRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting a joint unitized representation

A unital inclusion preserves the old-unit projection. Thus restricting
a joint unitized representation to one source preserves its actual Hilbert
range, and the range representations agree after the canonical identity
isometry between the two equal projection ranges.
-/

noncomputable section
namespace KadisonSimilarity

variable {B S F : Type*} [CStarAlgebra B] [CStarAlgebra S]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Restrict through the functorial map between the two unitizations. -/
def unitizationRestrict (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) :
    Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F) :=
  ρ.comp (Unitization.starMap φ.toNonUnitalStarAlgHom)

@[simp] theorem unitizationRestrict_inr (φ : B →⋆ₐ[ℂ] S)
    (ρ : Unitization ℂ S →⋆ₐ[ℂ] (F →L[ℂ] F)) (b : B) :
    unitizationRestrict φ ρ (Unitization.inr b) = ρ (Unitization.inr (φ b)) := by
  change ρ (Unitization.starMap φ.toNonUnitalStarAlgHom (Unitization.inr b)) = _
  rw [Unitization.starMap_inr]
  rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralDensityIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication by a square-root density identifies the scalar L²
coordinates of a spectral measure with a subspace over a common base measure. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal ENNReal Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  (u : X → ℝ≥0) (hu : Measurable u)
  (hL2 : MemLp (fun x => (u x : ℂ)) 2 μ)

def squaredDensityMeasure : Measure X := μ.withDensity (fun x => ((u x) ^ 2 : ℝ≥0))

omit [T2Space X] in
include hu hL2 in
theorem weightedContinuous_memLp (f : C(X, ℂ)) :
    MemLp (fun x => (u x : ℂ) * f x) 2 μ := by
  apply hL2.of_le_mul (c := ‖f‖)
  · exact (hu.coe_nnreal_real.complex_ofReal.mul f.continuous.measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _)

def weightedContinuousVector (f : C(X, ℂ)) : Lp ℂ 2 μ :=
  (weightedContinuous_memLp μ u hu hL2 f).toLp (fun x => (u x : ℂ) * f x)

omit [T2Space X] in
theorem weightedContinuousVector_ae (f : C(X, ℂ)) :
    weightedContinuousVector μ u hu hL2 f =ᵐ[μ] (fun x => (u x : ℂ) * f x) :=
  MemLp.coeFn_toLp _

def weightedContinuousLinear : C(X, ℂ) →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := weightedContinuousVector μ u hu hL2
  map_add' f g := by
    apply Lp.ext
    filter_upwards [weightedContinuousVector_ae μ u hu hL2 (f + g),
      weightedContinuousVector_ae μ u hu hL2 f, weightedContinuousVector_ae μ u hu hL2 g,
      Lp.coeFn_add (weightedContinuousVector μ u hu hL2 f)
        (weightedContinuousVector μ u hu hL2 g)] with x hfg hf hg hs
    rw [hfg, hs]
    change _ = weightedContinuousVector μ u hu hL2 f x + weightedContinuousVector μ u hu hL2 g x
    rw [hf, hg, ContinuousMap.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [weightedContinuousVector_ae μ u hu hL2 (c • f),
      weightedContinuousVector_ae μ u hu hL2 f,
      Lp.coeFn_smul c (weightedContinuousVector μ u hu hL2 f)] with x hcf hf hs
    change weightedContinuousVector μ u hu hL2 (c • f) x =
      (c • weightedContinuousVector μ u hu hL2 f) x
    rw [hcf, hs]
    change _ = c * weightedContinuousVector μ u hu hL2 f x
    rw [hf, ContinuousMap.smul_apply]
    simp only [smul_eq_mul]
    ring

variable [IsFiniteMeasure (squaredDensityMeasure μ u)]

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [BorelSpace X] in
include hu in
theorem weight_memLp_of_finite_squareDensity :
    MemLp (fun x => (u x : ℂ)) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  have h1 : Integrable (fun _ : X => (1 : ℝ)) (squaredDensityMeasure μ u) := integrable_const 1
  have hw := (integrable_withDensity_iff_integrable_smul (hu.pow_const 2)).mp h1
  simpa only [NNReal.smul_def, smul_eq_mul, mul_one, NNReal.coe_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using hw

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_L2ScalarIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar multiplication is preserved by coordinate inclusions and the
cyclic spectral maps. These are the intertwining identities for the common
central Hilbert model. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Cyclic
variable [T2Space X] [CompleteSpace H]
  {A : Type*} [CommCStarAlgebra A]

local instance scalarIntertwiningMeasurable : MeasurableSpace (WeakDual.characterSpace ℂ A) :=
  borel (WeakDual.characterSpace ℂ A)
local instance scalarIntertwiningBorel : BorelSpace (WeakDual.characterSpace ℂ A) := ⟨rfl⟩

end Cyclic
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SeparableReducingTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separable reducing subspaces for finitely many tests

Take the closed complex span of the orbit of finitely many vectors under
words in finitely many operators and their adjoints. The orbit is countable,
so the resulting Hilbert subspace is separable. No representation estimate
or separability assumption on the ambient space is used.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {m r : ℕ}

def testLetter (T : Fin m → H →L[ℂ] H) (a : Fin m × Bool) : H →L[ℂ] H :=
  if a.2 then (T a.1).adjoint else T a.1

def testWord (T : Fin m → H →L[ℂ] H) : List (Fin m × Bool) → H →L[ℂ] H
  | [] => 1
  | a :: w => testLetter T a * testWord T w

def testOrbit (T : Fin m → H →L[ℂ] H) (ξ : Fin r → H) : Set H :=
  Set.range (fun p : List (Fin m × Bool) × Fin r => testWord T p.1 (ξ p.2))

/-- The canonical separable reducing space of a finite test family. -/
def separableReducingTestSpace (T : Fin m → H →L[ℂ] H) (ξ : Fin r → H) :
    ClosedSubmodule ℂ H :=
  (Submodule.span ℂ (testOrbit T ξ)).closure

instance separableReducingTestSpace_separable
    (T : Fin m → H →L[ℂ] H) (ξ : Fin r → H) :
    TopologicalSpace.SeparableSpace (separableReducingTestSpace T ξ) := by
  have hcount : (testOrbit T ξ).Countable := Set.countable_range _
  apply TopologicalSpace.IsSeparable.separableSpace
  change TopologicalSpace.IsSeparable
    (closure (Submodule.span ℂ (testOrbit T ξ) : Set H))
  exact (hcount.isSeparable.span (R := ℂ)).closure

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NonseparableReduction
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

/-- The norm-closed C-star algebra generated by the entries of one test. -/
def finiteMatrixTestAlgebra {n : ℕ} (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ (Set.range (fun ij : Fin n × Fin n => X ij.1 ij.2))).topologicalClosure

instance finiteMatrixTestAlgebra_closed {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    IsClosed (finiteMatrixTestAlgebra X : Set (H →L[ℂ] H)) :=
  StarSubalgebra.isClosed_topologicalClosure _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ProperlyInfiniteStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two orthogonal isometries yield every finite internal isometry row.
The concrete Banach predual supplies the structural existence theorem. -/

noncomputable section
namespace KadisonSimilarity

def binaryIsometryFamily {A : Type*} [Monoid A] (v w : A) : ℕ → A
  | 0 => w
  | n + 1 => v * binaryIsometryFamily v w n

theorem binaryIsometryFamily_orthogonal {A : Type*} [Ring A] [StarRing A]
    (v w : A) (hv : star v * v = 1) (hw : star w * w = 1)
    (hvw : star v * w = 0) :
    ∀ i j, star (binaryIsometryFamily v w i) * binaryIsometryFamily v w j =
      if i = j then 1 else 0 := by
  have hwv : star w * v = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hvw
  intro i
  induction i with
  | zero =>
      intro j
      cases j with
      | zero => simpa only [binaryIsometryFamily, ite_true] using hw
      | succ j =>
          simp only [binaryIsometryFamily, Nat.zero_ne_add_one, ite_false,
            ← mul_assoc, hwv, zero_mul]
  | succ i ih =>
      intro j
      cases j with
      | zero =>
          simp only [binaryIsometryFamily, Nat.add_one_ne_zero, ite_false,
            star_mul, mul_assoc, hvw, mul_zero]
      | succ j =>
          rw [show binaryIsometryFamily v w (i + 1) = v * binaryIsometryFamily v w i
            from rfl, show binaryIsometryFamily v w (j + 1) =
              v * binaryIsometryFamily v w j from rfl, star_mul]
          calc
            (star (binaryIsometryFamily v w i) * star v) *
                (v * binaryIsometryFamily v w j) =
              star (binaryIsometryFamily v w i) *
                ((star v * v) * binaryIsometryFamily v w j) := by noncomm_ring
            _ = if i + 1 = j + 1 then 1 else 0 := by
              rw [hv, one_mul, ih]
              simp only [Nat.add_right_cancel_iff]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : VonNeumannAlgebra H)

open scoped ComplexOrder

theorem central_projection_zero_or_one {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (hfactor : ∀ a : A, (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ A c)
    (p : A) (hp : IsStarProjection p) (hc : ∀ a, p * a = a * p) : p = 0 ∨ p = 1 := by
  obtain ⟨c, hpc⟩ := hfactor p hc
  have hcc : c * c = c := by
    apply FaithfulSMul.algebraMap_injective ℂ A
    rw [map_mul]
    simpa only [hpc] using hp.isIdempotentElem.eq
  have hz : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hcc, sub_self]
  rcases mul_eq_zero.mp hz with hc0 | hc1
  · left
    rw [hpc, hc0, map_zero]
  · right
    rw [hpc, sub_eq_zero.mp hc1, map_one]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RadonNikodymCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-root Radon–Nikodym coordinates put each finite scalar spectral
measure over a common finite base. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] (μ ν : Measure X)

def squareRootDensity (x : X) : ℝ≥0 := NNReal.sqrt ((ν.rnDeriv μ x).toNNReal)

theorem squareRootDensity_measurable : Measurable (squareRootDensity μ ν) :=
  NNReal.continuous_sqrt.measurable.comp (Measure.measurable_rnDeriv ν μ).ennreal_toNNReal

theorem squareRootDensity_sq_ae [SigmaFinite μ] [SigmaFinite ν] :
    (fun x => ((squareRootDensity μ ν x) ^ 2 : ℝ≥0∞)) =ᵐ[μ] ν.rnDeriv μ := by
  filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
  simp only [squareRootDensity, ← ENNReal.coe_pow, NNReal.sq_sqrt, ENNReal.coe_toNNReal hx.ne]

theorem squaredDensityMeasure_eq [SigmaFinite μ] [SigmaFinite ν] (hν : ν ≪ μ) :
    squaredDensityMeasure μ (squareRootDensity μ ν) = ν := by
  calc
    _ = μ.withDensity (ν.rnDeriv μ) :=
      withDensity_congr_ae (squareRootDensity_sq_ae μ ν)
    _ = ν := Measure.withDensity_rnDeriv_eq _ _ hν

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem squareRootDensity_memLp (hν : ν ≪ μ) :
    MemLp (fun x => (squareRootDensity μ ν x : ℂ)) 2 μ := by
  have he := squaredDensityMeasure_eq μ ν hν
  have hνfin : IsFiniteMeasure ν := inferInstance
  let : IsFiniteMeasure (squaredDensityMeasure μ (squareRootDensity μ ν)) := he.symm ▸ hνfin
  exact weight_memLp_of_finite_squareDensity μ (squareRootDensity μ ν)
    (squareRootDensity_measurable μ ν)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ScalarLocalizationApproximation
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly bounded continuous functions approximate the measurable
scalar localizations needed in the central spectral model. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  [IsFiniteMeasure μ] [μ.Regular]

theorem exists_continuous_indicator_eLpNorm_approx (s : Set X) (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : C(X, ℂ), (∀ x, ‖f x‖ ≤ 1) ∧
      eLpNorm (fun x => f x - s.indicator (fun _ => (1 : ℂ)) x) 2 μ ≤ ε := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_Lp_half ℂ μ 2 hε
  obtain ⟨η, hηpos, hη⟩ := exists_eLpNorm_indicator_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (1 : ℂ) hδpos.ne'
  have hηpos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.mpr hηpos
  obtain ⟨F, hFs, _, hFc, hμF⟩ :=
    hs.exists_isCompact_isClosed_sdiff_lt (measure_ne_top μ s) hηpos'.ne'
  have hI : eLpNorm ((F.indicator fun _ => (1 : ℂ)) -
      s.indicator (fun _ => (1 : ℂ))) 2 μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hFs]
    exact hη _ hμF.le
  obtain ⟨g, hgc, hgd, hgb, _, _⟩ := exists_continuous_eLpNorm_sub_le_of_closed
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hFc isOpen_univ (subset_univ F)
    (measure_ne_top μ F) (1 : ℂ) hδpos.ne'
  refine ⟨⟨g, hgc⟩, ?_, ?_⟩
  · intro x
    change ‖g x‖ ≤ 1
    simpa only [norm_one] using hgb x
  · convert! (hδ _ _ (hgc.aestronglyMeasurable.sub (aestronglyMeasurable_const.indicator hFc.measurableSet)) ((aestronglyMeasurable_const.indicator hFc.measurableSet).sub (aestronglyMeasurable_const.indicator hs)) hgd hI).le using 2
    all_goals try with_reducible_and_instances rfl
    ext x
    simp

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ScalarLocalizationLimit
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable localizations are strong limits of uniformly bounded continuous
scalar multipliers. Consequently their commutant is already determined by the
continuous scalar multipliers. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  [IsFiniteMeasure μ] [μ.Regular]

/-- One bounded sequence works almost everywhere for a fixed measurable set. -/
theorem exists_continuous_indicator_ae_sequence (s : Set X) (hs : MeasurableSet s) :
    ∃ f : ℕ → C(X, ℂ), (∀ n x, ‖f n x‖ ≤ 1) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop
        (𝓝 (s.indicator (fun _ => (1 : ℂ)) x)) := by
  have hex (n : ℕ) := exists_continuous_indicator_eLpNorm_approx μ s hs
    (ε := (2 : ℝ≥0∞)⁻¹ ^ n) (pow_ne_zero n (ENNReal.inv_ne_zero.mpr (by norm_num)))
  choose f hf he using hex
  have ht : Tendsto
      (fun n => eLpNorm (fun x => f n x - s.indicator (fun _ => (1 : ℂ)) x) 2 μ)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1))
      (fun _ => bot_le) he
  obtain ⟨u, _, hu⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (fun n => (f n).continuous.aestronglyMeasurable) (aestronglyMeasurable_const.indicator hs) ht).exists_seq_tendsto_ae
  exact ⟨fun n => f (u n), fun n => hf (u n), hu⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_UnitizationFiberClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bicommutant closure on the old-unit fibers

Restriction to the range of the old unit sends the represented unitization
bicommutant into the bicommutant of the genuine original-algebra
representation. This uses commutants and actual compression, including when
the range is the zero Hilbert space.
-/

noncomputable section
namespace KadisonSimilarity

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {B : Type*} [CStarAlgebra B]

/-- Every unitization element is its scalar part plus its inr part. -/
theorem unitization_representation_decomposition
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : Unitization ℂ B) :
    ρ a = a.fst • (1 : K →L[ℂ] K) + ρ (Unitization.inr a.snd) := by
  calc
    ρ a = ρ (Unitization.inl a.fst + Unitization.inr a.snd) :=
      congrArg ρ (Unitization.inl_fst_add_inr_snd_eq a).symm
    _ = _ := by
      rw [map_add, ← Unitization.algebraMap_eq_inl]
      exact congrArg (fun T : K →L[ℂ] K => T + ρ (Unitization.inr a.snd))
        ((ρ.commutes a.fst).trans (Algebra.algebraMap_eq_smul_one a.fst))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_ArvesonCompleteNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete completely bounded commutator norm controls the actual
entrywise C-star matrix amplifications needed for factorization. -/

noncomputable section
namespace KadisonSimilarity
open scoped ENNReal ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance arvesonComplete_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_CyclicSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive functional comparable to a cyclic orbit gives an actual
invertible intertwiner with its GNS representation. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def boundedHomOrbit (π : BoundedUnitalHom A H) (ξ : H) : A →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H ξ).comp ⟨π.1.toLinearMap, π.2⟩

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
@[simp] theorem boundedHomOrbit_apply (π : BoundedUnitalHom A H) (ξ : H) (a : A) :
    boundedHomOrbit π ξ a = π.1 a ξ := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_SimilarityCompleteBound
attribute [-simp] _root_.OAI.KadisonSimilarity.boundedHomOrbit_apply _root_.OAI.KadisonSimilarity.listOrbitSum_append _root_.OAI.KadisonSimilarity.listOrbitSum_nil _root_.OAI.KadisonSimilarity.sharpHom_apply _root_.OAI.KadisonSimilarity.sharpVectorMap_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual matrix bounds for a similarity, used to identify the minimum
condition number with the complete norm. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def similarityRepresentation (π : BoundedUnitalHom A H) (S : (H →L[ℂ] H)ˣ) :
    BoundedUnitalHom A H := by
  refine ⟨{
    toFun := fun a => (S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)
    map_one' := by simp
    map_mul' := by intro a b; simp [mul_assoc]
    map_zero' := by simp
    map_add' := by intro a b; simp [mul_add, add_mul]
    commutes' := ?_ }, ?_⟩
  · intro c
    simp [Algebra.algebraMap_eq_smul_one]
  · exact (continuous_const.mul π.2).mul continuous_const

@[simp] theorem similarityRepresentation_apply
    (π : BoundedUnitalHom A H) (S : (H →L[ℂ] H)ˣ) (a : A) :
    (similarityRepresentation π S).1 a =
      (S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H) := rfl

def similarityStarRepresentation (π : BoundedUnitalHom A H) (S : (H →L[ℂ] H)ˣ)
    (hS : ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))) :
    A →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  { (similarityRepresentation π S).1 with map_star' := hS }

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_ExponentialSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The optimal positive similarity, written in the exponential form used
in Kirchberg, J. Operator Theory 36 (1996), Proposition 1. -/

noncomputable section
namespace KadisonSimilarity
open NormedSpace
open scoped CStarAlgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance exponentialSimilarityRatAlgebra : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_FiniteCyclicSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finitely cyclic representations reduce to the cyclic case by finite
matrix amplification and the first-coordinate corner. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def scalarCStarMatrixHom (n : ℕ) : A →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp {
    toAlgHom := Matrix.scalarAlgHom (Fin n) ℂ
    map_star' := by
      intro a
      ext i j
      by_cases h : i = j <;> simp [Matrix.scalar, Matrix.star_apply, h, eq_comm] }

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_KirchbergConjugation
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entire conjugation path used in Kirchberg's Proposition 1,
J. Operator Theory 36 (1996), pp. 60--61. -/

noncomputable section
namespace KadisonSimilarity

open NormedSpace Complex Set

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]
  [CStarRing B] [CompleteSpace B] [StarModule ℂ B]

local instance kirchbergConjugationRatAlgebra : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℂ B

/-- The imaginary direction of this path is unitary conjugation. -/
def kirchbergPath (t a : B) (z : ℂ) : B :=
  exp (z • (-t)) * a * exp (z • t)

omit [StarRing B] [CStarRing B] [CompleteSpace B] [StarModule ℂ B] in
@[simp] theorem kirchbergPath_zero (t a : B) : kirchbergPath t a 0 = a := by
  simp [kirchbergPath]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_KirchbergIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fundamental-theorem-of-calculus estimate in Kirchberg's
Proposition 1, page 61. -/

noncomputable section
namespace KadisonSimilarity

open NormedSpace MeasureTheory Set
open scoped Topology

section Algebra

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

local instance kirchbergIntegralRatAlgebra : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℝ B

end Algebra
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Similarity_SimilarityUniverseTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Universe transfer for the similarity theorem

Raising the source algebra and the represented Hilbert space to a common
universe changes neither the bounded homomorphism nor its similarity
problem. The proof transports the actual invertible implementing operator
through the induced star algebra equivalence of operator algebras.
-/

noncomputable section
namespace KadisonSimilarity

universe u v w

namespace SimilarityUniverseTransfer

instance uliftStarRing {A : Type u} [Ring A] [StarRing A] :
    StarRing (ULift.{v} A) where
  star x := ⟨star x.down⟩
  star_involutive x := ULift.ext _ _ (star_star x.down)
  star_mul x y := ULift.ext _ _ (star_mul x.down y.down)
  star_add x y := ULift.ext _ _ (star_add x.down y.down)

instance uliftStarModule {A : Type u} [Ring A] [StarRing A]
    [Module ℂ A] [StarModule ℂ A] : StarModule ℂ (ULift.{v} A) where
  star_smul c x := ULift.ext _ _ (star_smul c x.down)

instance uliftCStarAlgebra {A : Type u} [CStarAlgebra A] :
    CStarAlgebra (ULift.{v} A) where
  norm_mul_self_le x := by
    change ‖x.down‖ * ‖x.down‖ ≤ ‖star x.down * x.down‖
    exact CStarRing.norm_mul_self_le x.down

instance uliftInnerProductSpace {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    InnerProductSpace ℂ (ULift.{v} H) where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := ℂ) x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y c := inner_smul_left x.down y.down c

end SimilarityUniverseTransfer
end KadisonSimilarity

end

end OAI
end


