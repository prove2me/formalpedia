-- Prove2me | Definitions.Def_OAIE3v2B130
-- name    : OAIE3v2B130
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:42:26.483763+00:00
-- url     : https://prove2.me/theorems/90f13b4e-4390-46ac-a8d2-e6bb64d78ec0
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 132 of 311
-- statement:
--   Definitions bundle 132 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B116`, `OAIE3v2B117` of this split.
--
--   Modules: `Dynamics/DilationBudgets.lean`, `Estimates/AllocatedNormalizedSiteTwist.lean`, `Estimates/AnchoredReferenceDomination.lean`, `Estimates/CenteredFiniteSliceResidualEnvelope.lean`, `Estimates/FactoredPositiveShiftContradiction.lean`, `Estimates/GroupedSiteTensor.lean`, `Estimates/ProjectedNativeCoefficient.lean`, `Estimates/ProjectedPointwiseCoefficient.lean`, `Estimates/RealProjectedCoefficientLift.lean`, `Estimates/SampledCommonSlice.lean`, `Fourier/NaturalFrequencyMultiples.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/PhysicalNormalizedSpatialFactor.lean`, `Geometry/PhysicalSupportedCubes.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/NativeProperAffineRecovery.lean`, `Lattices/PhysicalSpatialResidueSupport.lean`, `Linear/RealRankHorizontalSymbol.lean`, `Nilpotent/AdaptedBasisNilmanifold.lean`, `Nilpotent/IdealInvariantNiltestBudget.lean`, `Nilpotent/NiltestAffineProjection.lean`, `Polynomial/DegreeRankAdaptedBasis.lean`, `Polynomial/FreeDegreeRankAdaptedBounds.lean`, `Polynomial/RaisedDegreeRank.lean`, `Polynomial/RankPolynomialFactorization.lean`, `Polynomial/RealPositivePolynomialEvaluation.lean`, `Probability/FiniteProbabilityUniformResidualGood.lean`, `Probability/FiniteRelativeDensity.lean`, `Probability/IntervalDivisorProbability.lean`, `Sampling/JointSamplerProductivity.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B116
import Definitions.Def_OAIE3v2B117

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem polynomialOrbit_mul_coefficient_sub_mem_rank_two
    (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : F.associatedDegree.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      F.layer (Finsupp.weight w α) 2 := by
  let q := F.associatedDegree.polynomialOrbitCoordinates w
  have hmap := congrArg Multiplicative.toAdd (map_mul (F.rankCoefficientOrbitHom hs w α) g h)
  change F.higherHorizontalMk (Finsupp.weight w α) (F.rankLayerCoefficient w α (q (g * h)).coord) =
    F.higherHorizontalMk (Finsupp.weight w α) (F.rankLayerCoefficient w α (q g).coord) +
      F.higherHorizontalMk (Finsupp.weight w α) (F.rankLayerCoefficient w α (q h).coord) at hmap
  rw [← map_add] at hmap
  exact (F.higherHorizontalMk_eq _ _ _).mp hmap

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

variable {X C : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

variable [MeasurableSpace C]

theorem integral_normalizedDensityTest_compare (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → X → ℝ) (hD : ∀ x, Measurable (fun c => D c x))
    (hD0 : ∀ c x, 0 ≤ D c x) (hmass : ∀ c, 0 < p.mean (D c))
    (F : C → X → ℝ) (hF : ∀ x, Integrable (fun c => F c x) μ)
    (hFmass : ∀ x, (∫ c, F c x ∂μ) = 1)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ}
    (herror : ∀ c, ‖p.normalizedDensityTest (D c) f -
      p.complexMean (fun x => f x*(F c x : ℂ))‖ ≤ ε) :
    ‖(∫ c, p.normalizedDensityTest (D c) f ∂μ)-p.complexMean f‖ ≤ ε := by
  have hi := p.normalizedDensityTest_integrable μ D hD hD0 hmass f hf
  have hterm (x : X) : Integrable (fun c => f x*(F c x : ℂ)) μ := (hF x).ofReal.const_mul (f x)
  have href := p.complexMean_integrable μ (fun c x => f x*(F c x : ℂ)) hterm
  have hmean : (∫ c, p.complexMean (fun x => f x*(F c x : ℂ)) ∂μ) = p.complexMean f := by
    rw [p.integral_complexMean μ _ hterm]
    congr 1
    funext x
    rw [integral_const_mul, integral_complex_ofReal, hFmass x, Complex.ofReal_one, mul_one]
  rw [← hmean, ← integral_sub hi href]
  have h := norm_integral_le_of_norm_le (integrable_const ε (μ := μ)) (ae_of_all μ herror)
  simpa only [integral_const, probReal_univ, one_smul] using h

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

def CyclicNiltestUpperComparison.{u} (degree N : ℕ) [NeZero N]
    (P epsilon : ℝ) (f g : ZMod N → ℝ) : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s dim), s ≤ degree →
    ∀ (T : D.Niltest (fun _ : Unit => 1)), T.UnitIntervalValued → T.ComplexityLE P →
    (𝔼 x : ZMod N, (f x - g x) * (T.evalCyclic N (fun _ => x)).re) ≤ epsilon

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

def CyclicNiltestShiftBound.{u} (degree N : ℕ) [NeZero N]
    (p error : ℝ) (a J : ZMod N → ℝ) (E : Finset (ZMod N)) : Prop :=
  ∀ h ∉ E, ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s dim), s ≤ degree →
    ∀ (T : D.Niltest (fun _ : Unit => 1)), T.UnitIntervalValued → T.ComplexityLE p →
    (𝔼 x : ZMod N, a x * J (x + h) * (T.evalCyclic N (fun _ => x)).re) ≤ error

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealProjectedCoefficientLift
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r)

variable (F : NilpotentLieFiltration M t) (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

variable (b : Basis ι ℚ M) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem real_projectedCoefficient_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.realification.adaptedLieSubalgebra w)
    (v : (G.fourHorizontalLayer (Finsupp.weight w α)).baseChange ℝ)
    (hv : v.val = φ.toLinearMap.baseChange ℝ (coefficients p.val α)) :
    G.realFourHorizontalMap (Finsupp.weight w α) v =
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p) := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  have heq : v = realificationSubmoduleEquiv (G.fourHorizontalLayer (Finsupp.weight w α))
      ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x) := by
    apply Subtype.ext
    exact hv.trans (G.projectedLayerCoefficient_tensor_coe F φ hφ w α x).symm
  rw [heq, G.realFourHorizontalMap_baseChange, G.projectedLayerCoefficient_tensor_horizontal]
  change _ = (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
    (F.realSymbolOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x))
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap]

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module

variable {ι μ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

theorem horizontalImage_coordinates (B : Submodule ℚ (Fin 4 → L))
    (hB : B ≤ F.fourHorizontalLayer d) :
    (F.horizontalImageOfSubmodule B d).map (F.fourHorizontalCoordinates d f) =
      B.map (F.fourAmbientCoordinates d f) := by
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x.val, hx, (F.fourHorizontalCoordinates_map d f x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    let y : F.fourHorizontalLayer d := ⟨x, hB hx⟩
    exact ⟨F.fourHorizontalMap d y, ⟨y, hx, rfl⟩, F.fourHorizontalCoordinates_map d f y⟩

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def realFourHorizontalCoordinates :
    (ℝ ⊗[ℚ] (Fin 4 → F.HigherHorizontal d)) →ₗ[ℝ] ((Σ _ : Fin 4, ι) → ℝ) :=
  (realFourCoordinateEquiv (ι := ι)).toLinearMap.comp
    ((F.fourHorizontalCoordinates d f).baseChange ℝ)

noncomputable def realFourAmbientCoordinates :
    (ℝ ⊗[ℚ] (Fin 4 → L)) →ₗ[ℝ] ((Σ _ : Fin 4, ι) → ℝ) :=
  (realFourCoordinateEquiv (ι := ι)).toLinearMap.comp
    ((F.fourAmbientCoordinates d f).baseChange ℝ)

theorem realFourHorizontalCoordinates_tensor_map (x : ℝ ⊗[ℚ] F.fourHorizontalLayer d) :
    F.realFourHorizontalCoordinates d f ((F.fourHorizontalMap d).baseChange ℝ x) =
      F.realFourAmbientCoordinates d f ((F.fourHorizontalLayer d).subtype.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change realFourCoordinateEquiv
      ((F.fourHorizontalCoordinates d f).baseChange ℝ ((F.fourHorizontalMap d).baseChange ℝ (a ⊗ₜ[ℚ] x))) =
        realFourCoordinateEquiv
          ((F.fourAmbientCoordinates d f).baseChange ℝ
            ((F.fourHorizontalLayer d).subtype.baseChange ℝ (a ⊗ₜ[ℚ] x)))
    simp only [LinearMap.baseChange_tmul, F.fourHorizontalCoordinates_map]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFourHorizontalCoordinates_map (x : (F.fourHorizontalLayer d).baseChange ℝ) :
    F.realFourHorizontalCoordinates d f (F.realFourHorizontalMap d x) =
      F.realFourAmbientCoordinates d f x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv (F.fourHorizontalLayer d)).surjective x
  rw [F.realFourHorizontalMap_baseChange]
  exact F.realFourHorizontalCoordinates_tensor_map d f v

theorem realFourHorizontalCoordinates_image (J : Submodule ℚ (Fin 4 → F.HigherHorizontal d)) :
    (J.baseChange ℝ).map (F.realFourHorizontalCoordinates d f) =
      ((J.map (F.fourHorizontalCoordinates d f)).baseChange ℝ).map
        (realFourCoordinateEquiv (ι := ι)).toLinearMap := by
  rw [realification_map]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(F.fourHorizontalCoordinates d f).baseChange ℝ x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem realFourAmbientCoordinates_component (x : ℝ ⊗[ℚ] (Fin 4 → L)) (k : Fin 4) (i : ι) :
    F.realFourAmbientCoordinates d f x ⟨k, i⟩ =
      (f.baseChange ℝ).repr ((F.layer d 2).mkQ.baseChange ℝ ((LinearMap.proj k).baseChange ℝ x)) i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).repr
      (a ⊗ₜ[ℚ] F.fourAmbientCoordinates d f x) ⟨k, i⟩ =
        (f.baseChange ℝ).repr (a ⊗ₜ[ℚ] (F.layer d 2).mkQ (x k)) i
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, Pi.basis_repr]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx, hy]

theorem realFourHorizontalCoordinates_component
    (x : ℝ ⊗[ℚ] (Fin 4 → F.HigherHorizontal d)) (k : Fin 4) (i : ι) :
    F.realFourHorizontalCoordinates d f x ⟨k, i⟩ =
      (f.baseChange ℝ).repr
        ((F.higherHorizontalAmbient d).baseChange ℝ ((LinearMap.proj k).baseChange ℝ x)) i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change ((Pi.basis (fun _ : Fin 4 => Pi.basisFun ℚ ι)).baseChange ℝ).repr
      (a ⊗ₜ[ℚ] F.fourHorizontalCoordinates d f x) ⟨k, i⟩ =
        (f.baseChange ℝ).repr (a ⊗ₜ[ℚ] F.higherHorizontalAmbient d (x k)) i
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, Pi.basis_repr]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx, hy]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

theorem realHigherHorizontalCoordinates_component (x : ℝ ⊗[ℚ] F.HigherHorizontal d) (i : ι) :
    F.realHigherHorizontalCoordinates d f x i =
      (f.baseChange ℝ).repr ((F.higherHorizontalAmbient d).baseChange ℝ x) i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change ((Pi.basisFun ℚ ι).baseChange ℝ).repr
      (a ⊗ₜ[ℚ] F.higherHorizontalCoordinates d f x) i =
        (f.baseChange ℝ).repr (a ⊗ₜ[ℚ] F.higherHorizontalAmbient d x) i
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx, hy]

theorem realHigherHorizontalCoordinates_image (U : Submodule ℚ (F.HigherHorizontal d)) :
    (U.baseChange ℝ).map (F.realHigherHorizontalCoordinates d f) =
      realRationalCoordinateSpan (U.map (F.higherHorizontalCoordinates d f)) := by
  unfold realRationalCoordinateSpan
  rw [realification_map]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(F.higherHorizontalCoordinates d f).baseChange ℝ x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace DegreeRankLieFiltration

variable {ι μ L : Type*} [Fintype ι] [Fintype μ] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))
  (b : Basis μ ℚ L)

theorem realFourAmbientCoordinates_bound {H : ℕ}
    (hf : ∀ i j, RationalHeightLE (f.repr ((F.layer d 2).mkQ (b j)) i) H)
    (x : ℝ ⊗[ℚ] (Fin 4 → L)) {B : ℝ} (hB : 0 ≤ B)
    (hx : ∀ j, |((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x j| ≤ B)
    (k : Fin 4) (i : ι) :
    |F.realFourAmbientCoordinates d f x ⟨k, i⟩| ≤
      ((Fintype.card μ : ℝ) + 1) * (H + 1) * B := by
  let y := (LinearMap.proj k).baseChange ℝ x
  have hy : ‖(b.baseChange ℝ).equivFun y‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro j
    rw [Real.norm_eq_abs]
    change |(b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x) j| ≤ B
    rw [real_pi_projection_coordinates]
    exact hx ⟨k, j⟩
  rw [F.realFourAmbientCoordinates_component]
  calc
    _ = ‖realQuotientCoordinateMap f y i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖realQuotientCoordinateMap f y‖ := norm_le_pi_norm _ i
    _ ≤ ((Fintype.card μ : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun y‖ :=
      realQuotientCoordinateMap_norm_bound b f hf y
    _ ≤ _ := mul_le_mul_of_nonneg_left hy (by positivity)

theorem realFourAmbientCoordinates_grid (l : ℕ) (x : ℝ ⊗[ℚ] (Fin 4 → L))
    (hx : (fun j => ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x j) ∈ realDenominatorGrid l) :
    F.realFourAmbientCoordinates d f x ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  obtain ⟨z, hz⟩ := hx
  have hsource (k : Fin 4) :
      (b.baseChange ℝ).equivFun ((LinearMap.proj k).baseChange ℝ x) ∈ realDenominatorGrid l := by
    refine ⟨fun i => z ⟨k, i⟩, ?_⟩
    funext i
    exact (congrFun hz ⟨k, i⟩).trans
      (congrArg (fun y : ℝ => (l : ℝ) * y) (real_pi_projection_coordinates b x k i).symm)
  choose a ha using fun k => realQuotientCoordinateMap_grid b f l
    ((LinearMap.proj k).baseChange ℝ x) (hsource k)
  refine ⟨fun j => a j.1 j.2, ?_⟩
  funext j
  exact (congrFun (ha j.1) j.2).trans
    (congrArg (fun y : ℝ => ((matrixDenominator (quotientCoordinateMatrix b f) * l : ℕ) : ℝ) * y)
      (F.realFourAmbientCoordinates_component d f x j.1 j.2).symm)

end DegreeRankLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedPointwiseCoefficient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

section Coefficients

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem gradedSymbolPolynomial_coefficient_symbol (p : F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.gradedSymbolPolynomial e ω hF w (F.polynomialSymbolMap w p)) α =
      F.associatedGradedPieceMap (Finsupp.weight w α) ⟨coefficients p.val α, p.property α⟩ := by
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext i
  rw [F.associatedGradedPieceMap_coordinate]
  by_cases hi : Finsupp.weight w α = ω i
  · rw [if_pos hi]
    exact (F.gradedSymbolPolynomial_coefficient e ω hF w _ ⟨(α, i), hi⟩).trans
      (F.polynomialSymbolBasis_repr_map e ω hF w p ⟨(α, i), hi⟩)
  · rw [if_neg hi]
    exact F.gradedSymbolPolynomial_coefficient_of_ne e ω hF w _ α i hi

end Coefficients

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι M : Type*} [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
  (F : NilpotentLieFiltration M t)

theorem symbol_mem_pointwise_iff_refiltered_coefficients (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded) (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w p ∈ F.symbolPointwiseSubalgebra b ω hF w U ↔
      ∀ α, coefficients p.val α ∈ F.gradedRefiltrationLayer U (Finsupp.weight w α) := by
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  apply forall_congr'
  intro α
  rw [F.gradedSymbolPolynomial_coefficient_symbol]
  exact (F.mem_gradedRefiltrationLayer_iff U (Finsupp.weight w α)
    ⟨coefficients p.val α, p.property α⟩).symm

end NilpotentLieFiltration

namespace DegreeRankLieFiltration

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontalSymbolCoefficient_mem (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.PolynomialSymbol w) (hx : x ∈ F.symbolPointwiseSubalgebra b ω hF w U)
    (α : σ →₀ ℕ) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α x ∈
      G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
        (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx)) (Finsupp.weight w α) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  have hcoef := (F.symbol_mem_pointwise_iff_refiltered_coefficients b ω hF w U p).mp hx α
  apply (G.mem_layerHorizontalImage _ _ _ _ _).mpr
  refine ⟨⟨coefficients p.val α, hcoef⟩, ?_⟩
  rw [G.projectedHorizontalSymbolCoefficient_symbol]
  rfl

theorem real_projectedHorizontalSymbolCoefficient_mem (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : ℝ ⊗[ℚ] F.PolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U))
    (α : σ →₀ ℕ) :
    (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ x ∈
      (G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
        (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx))
          (Finsupp.weight w α)).baseChange ℝ := by
  let K := (F.symbolPointwiseSubalgebra b ω hF w U).toSubmodule
  let V := G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
    (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx)) (Finsupp.weight w α)
  let f := G.projectedHorizontalSymbolCoefficient F φ hφ w α
  have hmap : K.map f ≤ V := by
    rintro y ⟨z, hz, rfl⟩
    exact G.projectedHorizontalSymbolCoefficient_mem F φ hφ b ω hF w U z hz α
  apply Submodule.baseChange_mono ℝ hmap
  rw [realification_map]
  exact ⟨x, hx, rfl⟩

end DegreeRankLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def symbol (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    D.filtration.RealPolynomialSymbolGroup w :=
  D.filtration.realPolynomialSymbolHom b ω hF w ⟨⟨T.orbit.log, T.orbit.property⟩⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankAdaptedBasis
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (e : Basis ι ℚ L)

theorem exists_rank_adapted_basis_logHeight
    {η : Fin (s + 1) → Fin (s + 1) → Type*}
    (v : ∀ i j, η i j → F.layer i.val j.val)
    (hspan : ∀ i j, Submodule.span ℚ (Set.range (v i j)) = ⊤)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hv : ∀ i j a k, rationalLogHeight (e.repr (v i j a : L) k) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ L)) ℚ L,
      IsCentralLieBasis b ∧
      (∀ i j, ∃ c ≤ finrank ℚ L, F.layer i j = basisTail b c) ∧
      (∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (e i) j) ≤ (p + 3) ^ 5) ∧
      ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := hp.trans (le_add_of_nonneg_right zero_le_one)
  have hd1 : (Fintype.card ι : ℝ) ≤ p + 1 := hd.trans (le_add_of_nonneg_right zero_le_one)
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis e] using hd1
  obtain ⟨b, hcentral, hb, hlayer⟩ := F.exists_bounded_rank_adapted_basis e v hspan
    (fun i j a k => rationalHeightLE_ceil_exp (hv i j a k))
  have hinverse := inverse_basis_entries_height e b hH hb
  have hstructure := basis_change_structure_height e b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
  refine ⟨b, hcentral, hlayer, fun j i => rationalLogHeight_le_of_height (hb j i) hHp, ?_, ?_⟩
  · intro i j
    apply rationalLogHeight_le_of_height (hinverse i j)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalSolveHeight_le_budget (Fintype.card (Fin (finrank ℚ L))) H hp1 hr hHp
  · intro i j k
    apply rationalLogHeight_le_of_height (hstructure i j k)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalLieStructureHeight_inverse_budget (Fintype.card ι)
        (Fintype.card (Fin (finrank ℚ L))) H hp1 hd1 hr hHp

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FreeDegreeRankAdaptedBounds
namespace OAI

section

namespace Erdos3

namespace FreeWeightedNilpotentLieAlgebra

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

noncomputable def canonicalRankGenerators (d k : ℕ) : Finset (FreeWeightedNilpotentLieAlgebra X s w) := by
  classical
  exact layerGenerators X s w (d + 1) ∪
    finiteWeightedLieValues (rankAlphabetVector X s w) (rankAlphabetWeight X s w) d k

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AdaptedBasisNilmanifold
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem adaptedLayerBasis_height (j : ℕ) (i : Fin (finrank ℚ (F.layer j))) (k : Fin d) :
    RationalHeightLE (b.repr (F.adaptedLayerBasis b w hlayers j i) k) 1 := by
  classical
  unfold adaptedLayerBasis
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one b _ k

theorem ofAdaptedBasis_geometry (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hNp : (N : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) :
    (F.ofAdaptedBasis b w hlayers Γ N hN hin hout).GeometryComplexityLE p := by
  refine ⟨hd, hNp, hc, ?_⟩
  intro i j k
  exact rationalLogHeight_le_of_height (F.adaptedLayerBasis_height b w hlayers _ j k)
    (by simpa only [Nat.cast_one] using Real.one_le_exp hp)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem selectedResidue_trimmed_reference_compare {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1) :
    ‖(𝔼 a ∈ trimmedIntegerBox N R,
        ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
          f (a + integerPhysicalSite root z)) - 𝔼 x ∈ integerBox N, f x‖ ≤
      2 * ∑ i, 2 * (R i : ℝ) / N i := by
  let p := selectedResidueFiniteLaw modulus T W hW hZ
  have hnoise (z : rectangularWeightIndices 0 W 1) (i : I) :
      |integerPhysicalSite root z.val i| ≤ (R i : ℤ) := by
    have h := (integerPhysicalSite_abs_bound root W z.val
      (rectangularWeightIndices_zero_bound W z.property) i).trans (hwidth i)
    exact_mod_cast h
  have h := p.translated_subset_mixture_compare (trimmedIntegerBox N R) (integerBox N)
    (trimmedIntegerBox_nonempty N R hR) (fun z a => a + integerPhysicalSite root z.val)
    (fun _ _ _ _ _ he => add_right_cancel he)
    (fun z _ ha => trimmedIntegerBox_add_mem N R (fun i => (hR i).le) ha _ (hnoise z)) f hf
  have hdef := trimmedIntegerBox_card_deficit N R
    (fun i => lt_of_le_of_lt (Nat.zero_le _) (hR i)) (fun i => (hR i).le)
  have hbound := h.trans (mul_le_mul_of_nonneg_left hdef (by norm_num : (0 : ℝ) ≤ 2))
  dsimp only [p] at hbound
  have he (a : I → ℤ) := selectedResidueFiniteLaw_complexMean modulus T W hW hZ
    (fun z => f (a + integerPhysicalSite root z))
  simpa only [he] using hbound

theorem selectedResidue_trimmed_comparison_transfer {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (L : (I → ℤ) → ℂ) {ε : ℝ}
    (hL : ∀ a ∈ trimmedIntegerBox N R,
      ‖L a - ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
        f (a + integerPhysicalSite root z)‖ ≤ ε) :
    ‖(𝔼 a ∈ trimmedIntegerBox N R, L a) - 𝔼 x ∈ integerBox N, f x‖ ≤
      ε + 2 * ∑ i, 2 * (R i : ℝ) / N i := by
  have hlocal : ‖(𝔼 a ∈ trimmedIntegerBox N R, L a) -
      (𝔼 a ∈ trimmedIntegerBox N R,
        ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
          f (a + integerPhysicalSite root z))‖ ≤ ε := by
    rw [← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans
      (Finset.expect_le (trimmedIntegerBox_nonempty N R hR) hL)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hlocal (selectedResidue_trimmed_reference_compare
      root N R hR modulus T W hW hZ hwidth f hf))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem mass_above_double_cap_le {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (C : ℝ) :
    q.mass (Finset.univ.filter (fun x => 2*C*p.weight x < q.weight x)) ≤
      2 * p.excessMass q C := by
  let S := Finset.univ.filter (fun x => 2*C*p.weight x < q.weight x)
  calc
    q.mass S ≤ ∑ x ∈ S, 2 * max (q.weight x - C*p.weight x) 0 := by
      apply Finset.sum_le_sum
      intro x hx
      have h := (Finset.mem_filter.mp hx).2
      have he := le_max_left (q.weight x - C*p.weight x) 0
      nlinarith
    _ = 2 * ∑ x ∈ S, max (q.weight x - C*p.weight x) 0 := by rw [Finset.mul_sum]
    _ ≤ 2 * p.excessMass q C := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun _ _ _ => le_max_right _ _)

theorem mass_above_double_cap_le_of_excess {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) {C ε : ℝ} (h : p.excessMass q C ≤ ε) :
    q.mass (Finset.univ.filter (fun x => 2*C*p.weight x < q.weight x)) ≤ 2*ε :=
  (mass_above_double_cap_le p q C).trans (mul_le_mul_of_nonneg_left h (by norm_num))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteRelativeDensity
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

noncomputable def relativeDensity (p q : FiniteProbabilityWeights Ω) (x : Ω) : ℝ :=
  q.weight x / p.weight x

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.JointSamplerProductivity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem productive_mass_lower_bound {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (score : Ω → ℝ) (bad : Finset Ω)
    {a : ℝ} (ha : 0 ≤ a) (hscore : ∀ x, score x ≤ 1) :
    p.mean score - a - p.mass bad ≤
      p.mass (Finset.univ.filter (fun x => x ∉ bad ∧ a ≤ score x)) := by
  classical
  let productive := Finset.univ.filter (fun x => x ∉ bad ∧ a ≤ score x)
  have hpoint (x : Ω) : score x ≤ a + (if x ∈ productive then 1 else 0) +
      (if x ∈ bad then 1 else 0) := by
    by_cases hb : x ∈ bad
    · simp only [hb, ite_true]
      split_ifs <;> linarith [hscore x]
    · by_cases hs : a ≤ score x
      · have hp : x ∈ productive := by simp [productive, hb, hs]
        simp only [hb, hp, ite_true, ite_false]
        linarith [hscore x]
      · have hp : x ∉ productive := by simp [productive, hs]
        simp only [hb, hp, ite_false, add_zero]
        linarith
  have h := p.mean_mono hpoint
  rw [p.mean_add, p.mean_add, p.mean_const, p.mean_indicator, p.mean_indicator] at h
  linarith

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def sampledTestSeminorm {Ω T X : Type*} [Fintype Ω] [Fintype T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (w : ∀ z, J z → T → ℂ) : Seminorm ℂ (X → ℂ) :=
  Seminorm.of (fun v => p.mean (fun z => (⨆ j, sampledSingleTestSeminorm (F z) (w z j)) v))
    (fun u v => by
      rw [← p.mean_add]
      exact p.mean_mono (fun z => map_add_le_add _ _ _))
    (fun a v => by
      simp only [map_smul_eq_mul]
      exact p.mean_const_mul ‖a‖ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def sampledSliceSeminorm {Ω T X : Type*} [Fintype Ω] [Fintype T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) : Seminorm ℂ (X → ℂ) :=
  sampledTestSeminorm p F (fun z j => normalizedSliceTest (S z j) (w z j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledCommonSlice
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem sum_mass_choice_fibers {Ω C : Type*} [Fintype Ω] [Fintype C]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (code : Ω → C) :
    (∑ c, p.mass (G.filter (fun z => code z = c))) = p.mass G := by
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem exists_large_mass_choice_fiber {Ω C : Type*} [Fintype Ω] [Fintype C] [Nonempty C]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (code : Ω → C) :
    ∃ c, p.mass G / Fintype.card C ≤ p.mass (G.filter (fun z => code z = c)) := by
  have he : (𝔼 c, p.mass (G.filter (fun z => code z = c))) =
      p.mass G / Fintype.card C := by
    rw [Fintype.expect_eq_sum_div_card, p.sum_mass_choice_fibers]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty he.ge
  exact ⟨c, hc⟩

theorem mass_superlevel_ge {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (f : Ω → ℝ) {α ρ B : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 < B) (hcap : ∀ z, f z ≤ B) (hmean : α ≤ p.mean f) :
    (α - ρ) / B ≤ p.mass (Finset.univ.filter (fun z => ρ ≤ f z)) := by
  let G := Finset.univ.filter (fun z => ρ ≤ f z)
  have hpoint (z : Ω) : f z ≤ ρ + B * (if z ∈ G then 1 else 0) := by
    by_cases hz : ρ ≤ f z
    · simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and, hz, ite_true,
        mul_one] using (hcap z).trans (by linarith)
    · simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, hz, ite_false,
        mul_zero, add_zero]
      exact le_of_not_ge hz
  have h := p.mean_mono hpoint
  rw [p.mean_add, p.mean_const, p.mean_const_mul, p.mean_indicator] at h
  apply (div_le_iff₀ hB).mpr
  change α - ρ ≤ p.mass G * B
  nlinarith only [hmean, h]

theorem mass_mul_le_mean_of_lower_bound {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (f : Ω → ℝ) {a : ℝ}
    (hf : ∀ z, 0 ≤ f z) (hG : ∀ z ∈ G, a ≤ f z) :
    a * p.mass G ≤ p.mean f := by
  rw [← p.mean_indicator G, ← p.mean_const_mul]
  apply p.mean_mono
  intro z
  by_cases hz : z ∈ G
  · simpa only [hz, ite_true, mul_one] using hG z hz
  · simpa only [hz, ite_false, mul_zero] using hf z

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.DilationBudgets
namespace OAI

section

namespace Erdos3.DilationBudget

open RationalFilteredNilmanifold
open scoped NNReal

noncomputable def shift (q : ℤ) (p : ℝ) : ℝ := p + height q

noncomputable def ambient (t : ℕ) (q : ℤ) (p : ℝ) : ℝ :=
  shift q p + dilationPairGeometryBudget t (shift q p) + 2 * (shift q p + 1)

noncomputable def quotient (t : ℕ) (q : ℤ) (p : ℝ) : ℝ := (ambient t q p + 3) ^ 11

noncomputable def common (t : ℕ) (q : ℤ) (C : ℕ) (p : ℝ) : ℝ :=
  ambient t q p + quotient t q p + (p + C) ^ C + 4

theorem shift_bounds (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ shift q p ∧ p ≤ shift q p ∧ rationalLogHeight (q : ℚ) ≤ shift q p := by
  have hh : rationalLogHeight (q : ℚ) ≤ (height q : ℝ) := Nat.le_ceil _
  exact ⟨add_nonneg hp (Nat.cast_nonneg _), le_add_of_nonneg_right (Nat.cast_nonneg _),
    hh.trans (le_add_of_nonneg_left hp)⟩

theorem ambient_bounds (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ ambient t q p ∧ shift q p ≤ ambient t q p ∧
      dilationPairGeometryBudget t (shift q p) ≤ ambient t q p ∧
      2 * (shift q p + 1) ≤ ambient t q p := by
  have hr := (shift_bounds q hp).1
  have hG : 0 ≤ dilationPairGeometryBudget t (shift q p) := by
    unfold dilationPairGeometryBudget
    positivity
  have hc : 0 ≤ 2 * (shift q p + 1) := by positivity
  unfold ambient
  exact ⟨by positivity, by linarith, by linarith, by linarith⟩

theorem quotient_bounds (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ quotient t q p ∧ ambient t q p ≤ quotient t q p ∧
      (ambient t q p + 3) ^ 5 ≤ quotient t q p := by
  have hA := (ambient_bounds t q hp).1
  have hb : 1 ≤ ambient t q p + 3 := by linarith
  have hpow : ambient t q p + 3 ≤ (ambient t q p + 3) ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (by decide : 1 ≤ 11)
  exact ⟨by unfold quotient; positivity, (by linarith : ambient t q p ≤ ambient t q p + 3).trans hpow,
    pow_le_pow_right₀ hb (by decide : 5 ≤ 11)⟩

theorem common_bounds (t : ℕ) (q : ℤ) (C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ common t q C p ∧ p ≤ common t q C p ∧
      ambient t q p ≤ common t q C p ∧ quotient t q p ≤ common t q C p ∧
      (p + C) ^ C ≤ common t q C p := by
  have hA := (ambient_bounds t q hp).1
  have hQ := (quotient_bounds t q hp).1
  have hN : 0 ≤ (p + C) ^ C := by positivity
  have hpA := (shift_bounds q hp).2.1.trans (ambient_bounds t q hp).2.1
  unfold common
  exact ⟨by positivity, by linarith, by linarith, by linarith, by linarith⟩

theorem exists_full_bound (t : ℕ) (q : ℤ) (C N : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ p : ℝ, 0 ≤ p →
      total t q N (common t q C p) ≤ (p + Z) ^ Z ∧
        ((q ^ t).natAbs + 1 : ℝ) * p ≤ (p + Z) ^ Z := by
  let X : Polynomial ℕ := Polynomial.X
  let r := X + Polynomial.C (height q)
  let G := ((r + 4) ^ 2 + Polynomial.C (t + 2) * (r + 1) + 6) ^ 11
  let A := r + G + 2 * (r + 1)
  let B := A + (A + 3) ^ 11 + (X + Polynomial.C C) ^ C + 4
  let R := 3 * B + (B + 3) ^ 2 + Polynomial.C (q ^ t).natAbs + 6
  let P := B + (R + Polynomial.C N) ^ N + 4
  obtain ⟨Z, hZ, hz⟩ := exists_natPolynomial_eval_budget
    (P + Polynomial.C ((q ^ t).natAbs + 1) * X)
  refine ⟨Z, hZ, fun p hp => ?_⟩
  have h : total t q N (common t q C p) + ((q ^ t).natAbs + 1 : ℝ) * p ≤ (p + Z) ^ Z := by
    simpa [total, reconstruction, common, quotient, ambient, shift, dilationPairGeometryBudget,
      X, r, G, A, B, R, P, Polynomial.eval₂_pow, Nat.cast_add] using hz p hp
  have ht : 0 ≤ total t q N (common t q C p) :=
    (common_bounds t q C hp).1.trans (total_bounds t q N (common_bounds t q C hp).1).1
  have hn : 0 ≤ ((q ^ t).natAbs + 1 : ℝ) * p := by positivity
  exact ⟨by linarith, by linarith⟩

end Erdos3.DilationBudget

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealRankHorizontalSymbol
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem realHorizontalSymbolCoefficient_extended (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w) :
    (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
      (F.associatedDegree.realExtendedSymbolMap w x) =
        (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    change (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
      (a ⊗ₜ[ℚ] F.associatedDegree.polynomialSymbolMap w p) =
        (F.higherHorizontalCoefficient w α).baseChange ℝ (a ⊗ₜ[ℚ] p)
    simp only [LinearMap.baseChange_tmul, F.higherHorizontalSymbolCoefficient_map]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedNativeCoefficient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem polynomialSymbolMap_adaptedTranslateLinear (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w (F.adaptedTranslateLinear w hw h p) = F.polynomialSymbolMap w p := by
  exact F.polynomialSymbolMap_translate w hw h p

theorem realPolynomialSymbolMap_translate (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hF w (F.realification.adaptedTranslateLinear w hw h p) =
      F.realPolynomialSymbolMap b ω hF w p := by
  apply sub_eq_zero.mp
  rw [← map_sub, F.realPolynomialSymbolMap_eq_zero_iff, map_sub, sub_eq_zero]
  exact F.realification.polynomialSymbolMap_adaptedTranslateLinear w hw h p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realFilteredPolynomialSymbolMap_extended (w : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ (F.realExtendedSymbolMap w x) =
      G.realExtendedSymbolMap w ((F.filteredPolynomialMap G φ hφ w).toLinearMap.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFilteredPolynomialSymbolMap_polynomial
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (p : F.realification.adaptedLieSubalgebra w) :
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p) =
      G.realSymbolOfPolynomial c τ hG w
        (VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) p.val) := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  change (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
    (F.realSymbolOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x)) = _
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap,
    F.realFilteredPolynomialSymbolMap_extended,
    ← G.realSymbolOfPolynomial_realAdaptedPolynomialMap c τ hG,
    F.realFilteredPolynomialMap_polynomial]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem nativeHorizontalCoefficientHom_tensor (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w)
    (hx : g.log = F.associatedDegree.realAdaptedPolynomialMap w x) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  rw [F.nativeHorizontalCoefficientHom_apply, hx,
    F.associatedDegree.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  exact F.realHorizontalSymbolCoefficient_extended w α x

theorem nativeHorizontalCoefficientHom_translate (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) (h : σ → ℤ) :
    F.nativeHorizontalCoefficientHom hs b ω hF w α (g.translate hw h) =
      F.nativeHorizontalCoefficientHom hs b ω hF w α g := by
  change Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
    (F.associatedDegree.realPolynomialSymbolMap b ω hF w
      (F.associatedDegree.realification.adaptedTranslateLinear w hw (fun i => (h i : ℚ))
        ⟨g.log, g.property⟩))) = _
  rw [F.associatedDegree.realPolynomialSymbolMap_translate]
  rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontalSymbolCoefficient_native (hs : 1 ≤ s)
    (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (τ : κ → ℕ)
    (hG : ∀ j, G.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (p : F.realification.adaptedLieSubalgebra w)
    (g : G.associatedDegree.realification.PolynomialOrbit w) (k : Fin 4)
    (hg : VectorPolynomial.map
      ((realificationLieHom ((liePiEval k).comp φ)).toLinearMap.restrictScalars ℚ) p.val = g.log) :
    (LinearMap.proj k).baseChange ℝ
        ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
          (F.realPolynomialSymbolMap b ω hF w p)) =
      Multiplicative.toAdd (G.nativeHorizontalCoefficientHom hs c τ hG w α g) := by
  rw [G.real_projectedHorizontalSymbolCoefficient_component,
    G.nativeHorizontalCoefficientHom_apply]
  change (G.higherHorizontalSymbolCoefficient w α).baseChange ℝ
    ((F.filteredPolynomialSymbolMap G.associatedDegree ((liePiEval k).comp φ)
      (G.projectedComponent_mem_layer F φ hφ k) w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p)) = _
  rw [F.realFilteredPolynomialSymbolMap_polynomial G.associatedDegree ((liePiEval k).comp φ)
    (G.projectedComponent_mem_layer F φ hφ k) b ω hF c τ hG w p, hg]

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NaturalFrequencyMultiples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem rationalLogHeight_nat_mul (n : ℕ) {x : ℚ} {p : ℝ}
    (hx : rationalLogHeight x ≤ p) : rationalLogHeight ((n : ℚ) * x) ≤ p + n + 1 := by
  have hp : 0 ≤ p := (rationalLogHeight_nonneg x).trans hx
  have hn : RationalHeightLE (n : ℚ) (n + 1) := by
    simp [RationalHeightLE]
  apply rationalLogHeight_le_of_height (hn.mul (rationalHeightLE_ceil_exp hx))
  calc
    (((n + 1) * ⌈Real.exp p⌉₊ : ℕ) : ℝ) = ((n : ℝ) + 1) * (⌈Real.exp p⌉₊ : ℝ) := by push_cast; rfl
    _ ≤ Real.exp (n : ℝ) * Real.exp (p + 1) :=
      mul_le_mul (Real.add_one_le_exp _) (ceil_exp_le_exp_add_one hp)
        (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p + n + 1) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RaisedDegreeRank
namespace OAI

section

namespace Erdos3

namespace DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r t : ℕ}

def withRank (F : DegreeRankLieFiltration L s r) (ht : t ≤ s)
    (hterminal : F.layer s (t + 1) = ⊥) : DegreeRankLieFiltration L s t where
  rank_le_degree := ht
  layer := F.layer
  lex_antitone := F.lex_antitone
  one_eq_top := F.one_eq_top
  rank_zero_eq_one := F.rank_zero_eq_one
  overshoot := F.overshoot
  lie_mem := F.lie_mem
  terminal := hterminal

end DegreeRankLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupedSiteTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem vectorIntervalSiteWeight_lipschitz {D : Type*} [Fintype D] (b : ℝ)
    {r : ℝ≥0} (hr : 0 < r) (k : D → Fin (intervalSiteCount b r)) :
    LipschitzWith (Fintype.card D * ((2 * intervalSiteCount b r + 1) / r))
      (vectorIntervalSiteWeight b r k) := by
  unfold vectorIntervalSiteWeight
  apply siteFactorTensor_factor_lipschitz (fun d y => (intervalSiteWeight b r (k d) y : ℂ))
  · intro d
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp (intervalSiteWeight_lipschitz b hr (k d))
  · intro d y
    have hw := intervalSiteWeight_range b (show (0 : ℝ) < r from hr) (k d) y
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPositivePolynomialEvaluation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {bound : σ → ℕ}

noncomputable def boxedPolynomial (f : BoxedDegreeIndex bound → L) : VectorPolynomial σ ℚ L := by
  classical
  exact ∑ a, monomial (boxedDegreeMonomial a) (f a)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery
namespace OAI

section

namespace Erdos3.FreimanModel

variable {I : Type*} (q : I → ℕ) [∀ i, NeZero (q i)]

theorem isAddFreimanIso_cyclicProductLift [Fintype I]
    (A : Finset (∀ i, ZMod (q i))) {c : I → Fin 16}
    (hc : ∀ x ∈ A, cyclicProductBlock q x = c) :
    IsAddFreimanIso 8 (A : Set _) (A.image (cyclicProductLift q) : Set (I → ℤ))
      (cyclicProductLift q) := by
  refine ⟨⟨?_, (cyclicProductLift_injective q).injOn, ?_⟩, ?_⟩
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro x hx
    exact Finset.mem_image.mp hx
  · intro T U hTA hUA hT hU
    exact cyclicProductLift_sum_eq_iff q T U hT hU
      (fun x hx => hc x (hTA hx)) (fun x hx => hc x (hUA hx))

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FactoredPositiveShiftContradiction
namespace OAI


namespace Erdos3

def CyclicShiftComparison.{u} (degree : ℕ) (epsilon : ℝ) (c : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (p : ℝ), 2 ≤ p → Odd N →
    Real.exp ((p + 2) ^ c) ≤ N → ∀ f g J : ZMod N → ℝ,
    (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
    (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
    (∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) →
    CyclicNiltestUpperComparison.{u} degree N ((p + 2) ^ c)
      (Real.exp (-((p + 2) ^ c))) f g →
    ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
      CyclicNiltestShiftBound.{u} (degree - 1) N p (Real.exp (-p))
        (fun n => f n - (1 + epsilon) * g n) J E

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSpatialResidueSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem vectorIntervalSiteWeight_affine_lipschitz {X : Type*} [Fintype X]
    (b : ℝ) {r : ℝ≥0} (hr : 0 < r) (k : X → Fin (intervalSiteCount b r))
    (slope shift : X → ℝ) {L : ℝ≥0} (hslope : ∀ x, |slope x| ≤ L) :
    LipschitzWith ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L)
      (fun y : X → ℝ => vectorIntervalSiteWeight b r k (fun x => slope x * y x + shift x)) := by
  have haffine : LipschitzWith L (fun y : X → ℝ => fun x => slope x * y x + shift x) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    apply (dist_pi_le_iff (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
    intro x
    calc
      dist (slope x * y x + shift x) (slope x * z x + shift x) =
          |slope x| * dist (y x) (z x) := by
        simp only [Real.dist_eq]
        rw [show slope x * y x + shift x - (slope x * z x + shift x) =
          slope x * (y x - z x) by ring, abs_mul]
      _ ≤ (L : ℝ) * dist y z :=
        mul_le_mul (hslope x) (dist_le_pi_dist y z x) dist_nonneg L.coe_nonneg
  exact (vectorIntervalSiteWeight_lipschitz b hr k).comp haffine

theorem affineVectorInterval_normalized_lipschitz {X : Type*} [Fintype X]
    (b : ℝ) {r : ℝ≥0} (hr : 0 < r) (k : X → Fin (intervalSiteCount b r))
    (H N : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {L : ℝ≥0} (hscale : ∀ x, |N x / ((q x : ℝ) * H x)| ≤ L) :
    LipschitzWith ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L)
      (fun y : X → ℝ => vectorIntervalSiteWeight b r k
        (fun x => (N x * y x - offset x) / ((q x : ℝ) * H x))) := by
  have h := vectorIntervalSiteWeight_affine_lipschitz b hr k
    (fun x => N x / ((q x : ℝ) * H x))
    (fun x => -(offset x : ℝ) / ((q x : ℝ) * H x)) hscale
  convert h using 1
  funext y
  congr 1
  funext x
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalNormalizedSpatialFactor
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical NNReal

variable {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ)
variable (b : ℝ) (r : ℝ≥0) (H N : X → ℝ) {m : ℕ}
variable (t : X → SpatialSiteLabel α m b r) (s : Finset α)

local notation "offset" => (fun i : Unit ⊕ α =>
  physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) (spatialStarVertex i))

theorem physicalResidueSpatialSmooth_bounds (hr : 0 < r) {L : ℝ≥0}
    (hscale : ∀ x, |N x / ((q x : ℝ) * H x)| ≤ L) :
    (∀ y, ‖physicalResidueSpatialSmooth root D base residue q b r H N t s y‖ ≤ 1) ∧
      LipschitzWith (Fintype.card (Unit ⊕ α) *
        ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L))
        (physicalResidueSpatialSmooth root D base residue q b r H N t s) := by
  let f := fun (i : Unit ⊕ α) (y : X → ℝ) =>
    if spatialStarVertex i = s then vectorIntervalSiteWeight b r (fun x => (t x).2 i)
      (fun x => (N x * y x - offset i x) / ((q x : ℝ) * H x)) else 1
  have hn (i : Unit ⊕ α) (y : X → ℝ) : ‖f i y‖ ≤ (1 : ℝ≥0) := by
    dsimp only [f]
    split_ifs
    · exact vectorIntervalSiteWeight_bound b (show (0 : ℝ) < r from hr) _ _
    · simp
  have hl (i : Unit ⊕ α) :
      LipschitzWith ((Fintype.card X * ((2 * intervalSiteCount b r + 1) / r)) * L) (f i) := by
    by_cases hi : spatialStarVertex i = s
    · simpa only [f, hi, ite_true] using
        affineVectorInterval_normalized_lipschitz b hr (fun x => (t x).2 i) H N q (offset i) hscale
    · simpa only [f, hi, ite_false] using
        (LipschitzWith.const (α := X → ℝ) (1 : ℂ)).weaken (show 0 ≤ _ from zero_le)
  have hp := bounded_lipschitz_fintype_prod f (B := 1) (le_refl _) hl hn
  refine ⟨?_, ?_⟩
  · intro y
    simpa only [physicalResidueSpatialSmooth, starVertexSiteFactor, f, one_pow, NNReal.coe_one] using hp.1 y
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [physicalResidueSpatialSmooth, starVertexSiteFactor, f, one_pow, mul_one] using hp.2.dist_le_mul y z

theorem physicalResidueSpatialSmooth_pre_lipschitz (hr : 0 < r) {L : ℝ≥0}
    (hscale : ∀ x, |N x / ((q x : ℝ) * H x)| ≤ L)
    {P EX ES EL : ℝ} (hP : 0 ≤ P) (hb : 0 ≤ b)
    (hbox : b ≤ Real.exp P) (hrinv : 1 / (r : ℝ) ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp EX)
    (hS : (Fintype.card (Unit ⊕ α) : ℝ) ≤ Real.exp ES) (hL : (L : ℝ) ≤ Real.exp EL) :
    LipschitzWith ⟨Real.exp (ES + EX + (3 * P + 6) + EL), Real.exp_nonneg _⟩
      (physicalResidueSpatialSmooth root D base residue q b r H N t s) := by
  apply (physicalResidueSpatialSmooth_bounds root D base residue q b r H N t s hr hscale).2.weaken
  apply NNReal.coe_le_coe.mp
  change (Fintype.card (Unit ⊕ α) : ℝ) *
      ((Fintype.card X : ℝ) * ((2 * (intervalSiteCount b r : ℝ) + 1) / (r : ℝ)) * L) ≤ _
  have hi := intervalSiteLipschitz_le_exp hb (show (0 : ℝ) < r from hr) hP hbox hrinv
  have hxi := mul_le_mul hX hi (by positivity) (Real.exp_pos EX).le
  have hxl := mul_le_mul hxi hL L.coe_nonneg (by positivity)
  apply (mul_le_mul hS hxl (by positivity) (Real.exp_pos ES).le).trans_eq
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSupportedCubes
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

noncomputable def physicalIntegerBoxCubes {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (dim : ℕ) : Finset (X → (Unit ⊕ Fin dim) → ℤ) :=
  Finset.univ.image (fun p : SupportedCube dim (integerBox N : Set (X → ℤ)) =>
    (physicalCubeParametersEquiv X dim).symm p.val)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNormalizedSiteTwist
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

theorem normalizedSiteTwistProduct_bounds {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → ℂ) (g : Y → ℂ) {Lf Lg : ℝ≥0}
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hnf : ∀ x, ‖f x‖ ≤ 1) (hng : ∀ y, ‖g y‖ ≤ 1) :
    (∀ v, ‖normalizedSiteTwistProduct f g v‖ ≤ 1) ∧
      LipschitzWith (Lf + Lg) (normalizedSiteTwistProduct f g) := by
  have h1 : LipschitzWith Lf (fun v : X × Y => f v.1) := by
    simpa only [mul_one, Function.comp_def] using hf.comp LipschitzWith.prod_fst
  have h2 : LipschitzWith Lg (fun v : X × Y => g v.2) := by
    simpa only [mul_one, Function.comp_def] using hg.comp LipschitzWith.prod_snd
  refine ⟨?_, ?_⟩
  · intro v
    rw [normalizedSiteTwistProduct, norm_mul]
    exact (mul_le_mul (hnf _) (hng _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · have h := lipschitz_mul_of_bounds _ _ h1 h2 (Bf := 1) (Bg := 1)
      (fun v => hnf v.1) (fun v => hng v.2)
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [normalizedSiteTwistProduct, one_mul, add_comm] using h.dist_le_mul v w

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityUniformResidualGood
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

theorem exists_uniformResidualGood
    {Ω Branch : Type*} [Fintype Ω] [Fintype Branch]
    (law : FiniteProbabilityWeights Ω) (H : Finset Ω)
    (error : Branch → Ω → ℝ) {ε δ : ℝ}
    (herror : ∀ b a, 0 ≤ error b a) (hmean : ∀ b, law.mean (error b) ≤ ε)
    (hH : 0 < law.mass H) (hδ : 0 < δ)
    (hbudget : (Fintype.card Branch : ℝ) * ε ≤ δ * law.mass H / 2) :
    ∃ K : Finset Ω, K ⊆ H ∧ law.mass H / 2 ≤ law.mass K ∧
      0 < law.mass K ∧ ∀ a ∈ K, ∀ b, error b a ≤ δ := by
  classical
  let good := fun a => ∀ b, error b a ≤ δ
  let K := H.filter good
  let B := H.filter (fun a => ¬ good a)
  have htotal (a : Ω) : 0 ≤ ∑ b, error b a := Finset.sum_nonneg (fun b _ => herror b a)
  have hbad (a : Ω) (ha : a ∈ B) : δ ≤ ∑ b, error b a := by
    have hnot : ¬ ∀ b, error b a ≤ δ := (Finset.mem_filter.mp ha).2
    obtain ⟨b, hb⟩ := not_forall.mp hnot
    exact (le_of_not_ge hb).trans
      (Finset.single_le_sum (fun j _ => herror j a) (Finset.mem_univ b))
  have hmeanSum : law.mean (fun a => ∑ b, error b a) ≤
      (Fintype.card Branch : ℝ) * ε := by
    calc
      _ = ∑ b, law.mean (error b) := by
        simp only [mean, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ _b : Branch, ε := Finset.sum_le_sum (fun b _ => hmean b)
      _ = _ := by simp
  have hbadmass : δ * law.mass B ≤ (Fintype.card Branch : ℝ) * ε := by
    calc
      _ = ∑ a ∈ B, law.weight a * δ := by
        simp only [mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ ∑ a ∈ B, law.weight a * ∑ b, error b a :=
        Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hbad a ha) (law.nonneg a))
      _ ≤ law.mean (fun a => ∑ b, error b a) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
          (fun a _ _ => mul_nonneg (law.nonneg a) (htotal a))
      _ ≤ _ := hmeanSum
  have hsplit : law.mass K + law.mass B = law.mass H := by
    exact Finset.sum_filter_add_sum_filter_not H good law.weight
  have hhalf : law.mass H / 2 ≤ law.mass K := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    have hsplitδ := congrArg (fun t : ℝ => δ * t) hsplit
    nlinarith only [hbadmass, hbudget, hsplitδ]
  exact ⟨K, Finset.filter_subset good H, hhalf, (by positivity : 0 < law.mass H / 2).trans_le hhalf,
    fun a ha => (Finset.mem_filter.mp ha).2⟩

theorem exists_uniformSliceResidualGood
    {Ω Branch T X : Type*} [Fintype Ω] [Fintype Branch] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (law : FiniteProbabilityWeights Ω) (H : Finset Ω)
    (physical : Ω → T → X) (slices : ∀ a, J a → Finset T)
    (tests : ∀ a, J a → T → ℂ) (signal : Branch → X → ℂ)
    {size ε δ : ℝ} (hS : ∀ a j, (slices a j).Nonempty)
    (hsize : ∀ a j, (Fintype.card T : ℝ) / (slices a j).card ≤ size)
    (htests : ∀ a j t, ‖tests a j t‖ ≤ 1)
    (hmean : ∀ b, sampledSliceSeminorm law physical slices tests (signal b) ≤ ε)
    (hH : 0 < law.mass H) (hδ : 0 < δ)
    (hbudget : (Fintype.card Branch : ℝ) * ε ≤ δ * law.mass H / 2) :
    ∃ K : Finset Ω, K ⊆ H ∧ law.mass H / 2 ≤ law.mass K ∧
      0 < law.mass K ∧ ∀ a ∈ K, ∀ b (j : J a),
        ‖𝔼 t ∈ slices a j, signal b (physical a t) * tests a j t‖ ≤ δ := by
  obtain ⟨K, hKH, hmass, hpos, hgood⟩ := law.exists_uniformResidualGood H
    (fun b => centeredFiniteSliceResidualEnvelope physical slices tests (signal b))
    (fun b => centeredFiniteSliceResidualEnvelope_nonneg physical slices tests (signal b))
    hmean hH hδ hbudget
  refine ⟨K, hKH, hmass, hpos, ?_⟩
  intro a ha b j
  exact (centeredFiniteSliceResidualEnvelope_dominates physical slices tests hS hsize htests
    (signal b) a j).trans (hgood a ha b)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end


