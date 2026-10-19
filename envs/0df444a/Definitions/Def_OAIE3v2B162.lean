-- Prove2me | Definitions.Def_OAIE3v2B162
-- name    : OAIE3v2B162
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:12:23.912069+00:00
-- url     : https://prove2.me/theorems/3a3563e3-24ff-4443-9cb9-99bff7cfd835
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 164 of 311
-- statement:
--   Definitions bundle 164 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152` of this split.
--
--   Modules: `Dynamics/ComparisonEquivalenceBudget.lean`, `Dynamics/PhysicalEpochComparison.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AllocatedTrimmedVectorSite.lean`, `Estimates/CommonDependentWordLayers.lean`, `Estimates/CommonFixedNativeSquareFamily.lean`, `Estimates/CommonNativeSquareFactors.lean`, `Estimates/CubeSignalAlgebra.lean`, `Estimates/CubicAntisymmetricTransfer.lean`, `Estimates/CubicRootPermutation.lean`, `Estimates/CyclicProductDetection.lean`, `Estimates/DilationCost.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/NativeCrossFactorization.lean`, `Estimates/NativeMarkedDiagramOrbitLift.lean`, `Estimates/NativeOptionOriginalOrbit.lean`, `Estimates/NativeOrbitOuterControl.lean`, `Estimates/NativeProductCoefficient.lean`, `Estimates/NativeResidualMultiplier.lean`, `Estimates/NativeRetainedTargetCubeIntervals.lean`, `Estimates/NativeSeparatedSumIntervals.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/NormalizedTwistCellSelection.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Estimates/PositiveFiberMarginal.lean`, `Estimates/PositiveShiftTestingGowers.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/SourceUnitCover.lean`, `Estimates/SymmetricSquarefreeMonotonicity.lean`, `Estimates/UnconditionalStepDrop.lean`, `Geometry/MixedCoordinateTransfer.lean`, `Geometry/SpatialChoiceEnvelope.lean`, `Lattices/FixedAffineEpochTransition.lean`, `Lattices/NativeIntegerHalving.lean`, `Lattices/NativeRetainedIntegerMultilinearQuadruples.lean`, `Lattices/RelativeSliceAffineThreeFactorLaw.lean`, `Lattices/ResidueEventOrDescent.lean`, `Linear/BoundedRankIntegralModel.lean`, `Linear/CommonFreeSpanBounds.lean`, `Linear/PhysicalSiteProjection.lean`, `Nilpotent/FreeDegreeRankNilmanifold.lean`, `Polynomial/OrdinaryPhasePairFunctionalBounds.lean`, `Probability/IndependentEmbeddedMixture.lean`, `Probability/PositiveDensityRetained.lean`, `Probability/RelativeSliceParameterCellLaw.lean`, `Sampling/AllocatedDenseFiberSliceForecastGeometry.lean`, `Sampling/MarkedKernelProjectionScoreRestoration.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MarkedKernelProjectionScoreRestoration
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

variable {G Λ : Type*} [Fintype G] (p : FiniteProbabilityWeights G)

noncomputable def finiteScore (weight : G → ℂ) (observable : G → Λ → ℂ) (l : Λ) : ℝ :=
  (p.complexMean (fun x => weight x * observable x l)).re

variable [MeasurableSpace Λ]

theorem finiteScore_measurable (weight : G → ℂ) (observable : G → Λ → ℂ)
    (hobservable : ∀ x, Measurable (observable x)) :
    Measurable (p.finiteScore weight observable) :=
  (p.complexMean_measurable (fun l x => weight x * observable x l)
    (fun x => (hobservable x).const_mul (weight x))).re

theorem finiteScore_integrable (μ : Measure Λ) (weight : G → ℂ) (observable : G → Λ → ℂ)
    (hobservable : ∀ x, Integrable (observable x) μ) :
    Integrable (p.finiteScore weight observable) μ :=
  (p.complexMean_integrable μ (fun l x => weight x * observable x l)
    (fun x => (hobservable x).const_mul (weight x))).re

omit [MeasurableSpace Λ] in

theorem finiteScore_abs_le (weight : G → ℂ) (observable : G → Λ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (hobservable : ∀ x l, ‖observable x l‖ ≤ 1) (l : Λ) :
    |p.finiteScore weight observable l| ≤ B := by
  apply (RCLike.abs_re_le_norm (p.complexMean (fun x => weight x * observable x l))).trans
  apply (p.norm_complexMean_le_mean_norm _).trans
  apply (p.mean_mono (fun x => ?_)).trans_eq (p.mean_const B)
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul (hweight x) (hobservable x l) (norm_nonneg _) hB

omit [MeasurableSpace Λ] in
theorem finiteScore_le (weight : G → ℂ) (observable : G → Λ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (hobservable : ∀ x l, ‖observable x l‖ ≤ 1) (l : Λ) :
    p.finiteScore weight observable l ≤ B :=
  (le_abs_self _).trans (p.finiteScore_abs_le weight observable hB hweight hobservable l)

theorem integral_finiteScore (μ : Measure Λ) (weight : G → ℂ) (observable : G → Λ → ℂ)
    (hobservable : ∀ x, Integrable (observable x) μ) :
    (∫ l, p.finiteScore weight observable l ∂μ) =
      (p.complexMean (fun x => weight x * ∫ l, observable x l ∂μ)).re := by
  change (∫ l, RCLike.re (p.complexMean (fun x => weight x * observable x l)) ∂μ) = _
  rw [integral_re (p.complexMean_integrable μ _
    (fun x => (hobservable x).const_mul (weight x)))]
  rw [p.integral_complexMean μ _ (fun x => (hobservable x).const_mul (weight x))]
  simp only [integral_const_mul]
  rfl

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedDiagramOrbitLift
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

noncomputable def topQuotientOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit
    (D.filtration.layerIdeal (s + 1)) (t := s) le_rfl g
  NilpotentLieFiltration.polynomialOrbitOfLog q.log (by rw [hQ]; exact q.adapted)

theorem topQuotientOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (D.topQuotientOrbit Q hQ g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitEval w x g) := by
  exact D.filtration.realQuotientPolynomialOrbit_eval
    (D.filtration.layerIdeal (s + 1)) (t := s) le_rfl g x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)

theorem topQuotientMarkedMap_real_mk (x : ℝ ⊗[ℚ] L) :
    realificationLieHom (D.topQuotientMarkedMap E φ hφ)
      (realificationLieHom (lieQuotientMap (D.filtration.layerIdeal (s + 1))) x) =
    realificationLieHom (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
      (realificationLieHom φ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCrossFactorization
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

namespace NativeVectorCorrelation

noncomputable def mono {I : Type*} {degree N : ℕ} [NeZero N] {p q : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation degree N p f) (hpq : p ≤ q) :
    NativeVectorCorrelation degree N q f :=
  { W with
    complexity := W.complexity.mono hpq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans W.correlation }

end NativeVectorCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

abbrev NativeCrossWitnesses (s N : ℕ) [NeZero N] (p : ℝ)
    (f₀ f₁ : ZMod N → ℂ) (m : ZMod N → ZMod N → ℂ) (H : Finset (ZMod N)) :=
  ∀ h : H, NativeVectorCorrelation s N p (nativeCrossResidual f₀ f₁ m h.val)

namespace NativeCrossWitnesses

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def product (h : H) (x : ZMod N) : ℂ :=
  m h.val x * (U h).test.evalCyclic N (fun _ => x)

noncomputable def extension (h x : ZMod N) : ℂ :=
  if hh : h ∈ H then U.product ⟨h, hh⟩ x else 0

end NativeCrossWitnesses

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SourceUnitCover
namespace OAI

section

namespace Erdos3.RationalTorus

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

def trivialMultidegreeFiltration (s : ℕ) (bound : σ → ℕ) :
    MultidegreeLieFiltration σ (Algebra 0) s bound where
  ordinary := trivialFiltration s
  layer _ := ⊤
  antitone _ _ _ := le_rfl
  zero_eq_top := rfl
  lie_mem _ _ := Submodule.mem_top
  terminal _ _ := by
    ext x
    rw [Subsingleton.elim x 0]
    simp only [Submodule.zero_mem]
  degree_eq _ := by
    ext x
    rw [Subsingleton.elim x 0]
    simp only [Submodule.zero_mem]

noncomputable def trivialMultidegreeStructure (s : ℕ) (bound : σ → ℕ) :
    (trivialNilmanifold s).MultidegreeStructure bound := by
  letI := (basis 0).finiteDimensional_of_finite
  exact {
    filtration := trivialMultidegreeFiltration s bound
    ordinary := rfl
    basis := fun _ => Module.finBasis ℚ _
  }

theorem trivialMultidegreeStructure_complexity (s : ℕ) (bound : σ → ℕ) {p : ℝ}
    (hp : 0 ≤ p) : (trivialMultidegreeStructure s bound).ComplexityLE p := by
  refine ⟨trivialNilmanifold_geometry s hp, ?_⟩
  intro a j k
  exact Fin.elim0 k

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace UnitVerticalObservable

variable {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p q : ℝ}

noncomputable def constOne (D : RationalFilteredNilmanifold L s d) (T : Subgroup D.RealGroup)
    (hp : 0 ≤ p) : D.UnitVerticalObservable T (Fin 1) p where
  observable _ _ := 1
  unit _ := by simp
  norm _ _ := by simp
  lipBound := 0
  lip_bound := (Real.exp_pos p).le
  lipschitz := by
    let := D.metricSpace
    exact fun _ => LipschitzWith.const 1
  frequency := 0
  height _ := by simpa [rationalLogHeight] using hp
  vertical _ _ _ _ := by simp only [realifyFunctional_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, one_mul]
  integral _ _ _ := ⟨0, by simp only [realifyFunctional_zero, Int.cast_zero]⟩

end UnitVerticalObservable

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

namespace NativeMultidegreeNilcharacter

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def eval (i : Fin W.outputDim) (x : σ → ℤ) : ℂ :=
  W.vertical.observable i (QuotientGroup.mk
    (W.multi.filtration.realification.polynomialOrbitEval x W.orbit))

noncomputable def evalCyclic (N : ℕ) [NeZero N] (i : Fin W.outputDim) (x : σ → ZMod N) : ℂ :=
  W.eval i (fun j => ((x j).val : ℤ))

noncomputable def constOne (bound : σ → ℕ) (hp : 0 ≤ p) :
    NativeMultidegreeNilcharacter bound p where
  L := RationalTorus.Algebra 0
  dim := 0
  model := RationalTorus.trivialNilmanifold (∑ i, bound i)
  multi := RationalTorus.trivialMultidegreeStructure (∑ i, bound i) bound
  complexity := RationalTorus.trivialMultidegreeStructure_complexity _ _ hp
  orbit := 1
  outputDim := 1
  output_pos := by omega
  output_bound := by simpa only [Nat.cast_one] using Real.one_le_exp hp
  vertical := RationalFilteredNilmanifold.UnitVerticalObservable.constOne _ _ hp

@[simp] theorem constOne_eval (bound : σ → ℕ) (hp : 0 ≤ p) (i : Fin 1) (x : σ → ℤ) :
    (constOne bound hp).eval i x = 1 := rfl

@[simp] theorem constOne_evalCyclic (bound : σ → ℕ) (hp : 0 ≤ p) (N : ℕ) [NeZero N]
    (i : Fin 1) (x : σ → ZMod N) : (constOne bound hp).evalCyclic N i x = 1 := rfl

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3

noncomputable def nativeMixedResidual {s N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (h : ZMod N) (i : Fin mixed.outputDim) (x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (mixed.evalCyclic N i (correlationInput h x))

structure NativeMixedCorrelation (s N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-p) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p
  correlation : ∀ h ∈ shifts, Nonempty (NativeVectorCorrelation (s - 1) N p
    (nativeMixedResidual f mixed h))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionOriginalOrbit
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

attribute [local irreducible] realPolynomialGroupMap

theorem optionOriginalOrbit_score {P σ T : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w)
    (observable : P → D₀.Space → ℂ)
    (sites : Finset T) (physical : T → P) (point : T → σ → ℤ) (weight : T → ℂ) :
    (𝔼 t ∈ sites, weight t * optionOriginalObservable D₀ D observable (physical t)
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w (point t) g))) =
    𝔼 t ∈ sites, weight t * observable (physical t)
      (QuotientGroup.mk (D₀.filtration.realification.polynomialOrbitEval w (point t)
        (optionOriginalOrbit D₀ D g))) := by
  simp only [optionOriginalObservable_apply, optionOriginalOrbit_value]

theorem optionOriginalOrbit_mark_log {M₀ : Type u} [LieRing M₀] [LieAlgebra ℚ M₀]
    (Fmark : NilpotentLieFiltration M₀ s) (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w)
    (marked : ∀ i, (optionFiltrations Fmark (fun j => (D j).filtration) i).realification.PolynomialOrbit w)
    (hmark : VectorPolynomial.map
      ((realificationLieHom (optionMarkedLieMap (L := L) φ)).toLinearMap.restrictScalars ℚ) g.log =
        (piRealOrbit (optionFiltrations Fmark (fun j => (D j).filtration)) marked).log) :
    VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
      (optionOriginalOrbit D₀ D g).log = (marked none).log :=
  (congrArg (VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ))
    (optionOriginalOrbit_log D₀ D g)).trans
      (optionMarkedPolynomialProjection_none g.log φ Fmark (fun j => (D j).filtration) marked hmark)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitOuterControl
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

namespace NativePolynomialOrbitFactors

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
  (R : NativePolynomialOrbitFactors D g eta A p)

noncomputable def slowValue (x : σ → ℤ) : D.RealGroup :=
  D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.slow

noncomputable def rationalValue (x : σ → ℤ) : D.RealGroup :=
  D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.rational

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem niltest_log_bound_of_exp (x y : ℝ≥0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : (x : ℝ) ≤ Real.exp a) (hy : (y : ℝ) ≤ Real.exp b) :
    Real.log (2 + (x : ℝ) + y) ≤ a + b + 4 := by
  apply (Real.log_le_iff_le_exp (by positivity : 0 < 2 + (x : ℝ) + y)).mpr
  have hx' := hx.trans (Real.exp_le_exp.mpr (by linarith : a ≤ a + b))
  have hy' := hy.trans (Real.exp_le_exp.mpr (by linarith : b ≤ a + b))
  have h1 : 1 ≤ Real.exp (a + b) := Real.one_le_exp (by linarith)
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * Real.exp (a + b) := by linarith
    _ ≤ Real.exp 4 * Real.exp (a + b) := mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricSquarefreeMonotonicity
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}

noncomputable def tensorPower (V : D.UnitVerticalObservable T I p) (n : ℕ) :
    D.UnitVerticalObservable T (Fin n → I) (p + n + 1) where
  observable a x := ∏ j, V.observable (a j) x
  unit x := by
    simp only [norm_prod, ← Finset.prod_pow]
    calc
      _ = ∏ _j : Fin n, ∑ a : I, ‖V.observable a x‖ ^ 2 := (Fintype.prod_sum _).symm
      _ = 1 := by simp only [V.unit, Finset.prod_const_one]
  norm a x := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => V.norm (a j) x)
  lipBound := n * V.lipBound
  lip_bound := by
    change (n : ℝ) * V.lipBound ≤ Real.exp (p + n + 1)
    calc
      _ ≤ Real.exp ((n : ℝ) + 1) * Real.exp p :=
        mul_le_mul (by linarith [Real.add_one_le_exp ((n : ℝ) + 1)]) V.lip_bound
          V.lipBound.coe_nonneg (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  lipschitz := by
    let := D.metricSpace
    intro a
    have h := bounded_lipschitz_fintype_prod (fun j x => V.observable (a j) x)
      (B := 1) le_rfl (fun j => V.lipschitz (a j)) (fun j x => V.norm (a j) x)
    simpa only [Fintype.card_fin, one_pow, mul_one] using h.2
  frequency := n • V.frequency
  height i := by
    simpa only [LinearMap.smul_apply, nsmul_eq_mul] using rationalLogHeight_nat_mul n (V.height i)
  vertical a z hz x := by
    simp only [V.vertical _ z hz x, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, realifyFunctional_nsmul, AddCircle.coe_nsmul, character_nsmul]
  integral z hz hL := by
    obtain ⟨m, hm⟩ := V.integral z hz hL
    refine ⟨(n : ℤ) * m, ?_⟩
    rw [realifyFunctional_nsmul, hm]
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

noncomputable def reindex {J : Type*} [Fintype J]
    (V : D.UnitVerticalObservable T I p) (e : I ≃ J) : D.UnitVerticalObservable T J p where
  observable j := V.observable (e.symm j)
  unit x := (e.symm.sum_comp (fun i => ‖V.observable i x‖ ^ 2)).trans (V.unit x)
  norm j := V.norm (e.symm j)
  lipBound := V.lipBound
  lip_bound := V.lip_bound
  lipschitz := fun j => V.lipschitz (e.symm j)
  frequency := V.frequency
  height := V.height
  vertical j := V.vertical (e.symm j)
  integral := V.integral

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def tensorPower (n : ℕ) : NativeMultidegreeNilcharacter bound (tensorPowerBudget n p) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hb := tensorPowerBudget_bounds n hp
  exact {
    L := W.L
    dim := W.dim
    model := W.model
    multi := W.multi
    complexity := W.complexity.mono W.multi hb.1
    orbit := W.orbit
    outputDim := W.outputDim ^ n
    output_pos := pow_pos W.output_pos n
    output_bound := by
      simpa only [Nat.cast_pow] using
        (pow_le_pow_left₀ (Nat.cast_nonneg W.outputDim) W.output_bound n).trans
          (by rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr hb.2.2)
    vertical := ((W.vertical.tensorPower n).reindex (tensorIndexEquiv W.outputDim n)).mono hb.2.1 }

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerHalving
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def ofProduct {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    {σ : Type*} {w : σ → ℕ} {s d e : ℕ} {p : ℝ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (T : D.Niltest w) (U : E.Niltest w)
    (hp : 2 ≤ p) (hT : T.ComplexityLE p) (hU : U.ComplexityLE p) :
    NativeIntegerExpansion w s (productNiltestBudget p)
      (fun x => T.eval x * U.eval x) := by
  have hp0 : 0 ≤ p := by linarith
  let K : Bool → Type := BoolLieFamily L M
  let dims : Bool → ℕ := fun b => Bool.rec e d b
  let models : ∀ b, RationalFilteredNilmanifold (K b) s (dims b) := fun b => by
    cases b
    · exact E
    · exact D
  let tests : ∀ b, (models b).Niltest w := fun b => by
    cases b
    · exact U
    · exact T
  have htests : ∀ b, (tests b).ComplexityLE p := by
    intro b
    cases b
    · exact hU
    · exact hT
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests
  have heval (x : σ → ℤ) : S.eval x =
      T.eval x * U.eval x := by
    change (RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests).eval
      x = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    rfl
  exact ofTest S
    (RationalFilteredNilmanifold.piNiltest_complexity models tests hp0 hcard htests)
    (fun x => (heval x).symm)

noncomputable def mul {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ} {f g : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p f) (F : NativeIntegerExpansion w s p g)
    (hp : 2 ≤ p) :
    NativeIntegerExpansion w s (productNiltestBudget p + 2 * p) (fun x => f x * g x) := by
  let c : Fin E.count × Fin F.count → ℂ := fun ij => E.coefficient ij.1 * F.coefficient ij.2
  let v : Fin E.count × Fin F.count → (σ → ℤ) → ℂ := fun ij x =>
    (E.test ij.1).eval x * (F.test ij.2).eval x
  let R : ∀ ij, NativeIntegerExpansion w s (productNiltestBudget p) (v ij) :=
    fun ij => ofProduct (E.model ij.1) (F.model ij.2) (E.test ij.1) (F.test ij.2)
      hp (E.complexity ij.1) (F.complexity ij.2)
  have hexp : Real.exp p * Real.exp p = Real.exp (2 * p) := by
    rw [← Real.exp_add, two_mul]
  have hcard : (Fintype.card (Fin E.count × Fin F.count) : ℝ) ≤ Real.exp (2 * p) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul E.count_bound F.count_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq hexp
  have hc : (∑ ij, ‖c ij‖) ≤ Real.exp (2 * p) := by
    calc
      _ = (∑ i, ‖E.coefficient i‖) * (∑ j, ‖F.coefficient j‖) := by
        simp only [c, norm_mul, Fintype.sum_prod_type, Finset.sum_mul_sum]
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul E.cost F.cost (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Real.exp_nonneg _)
      _ = _ := hexp
  have heq : (fun x => ∑ ij, c ij * v ij x) = (fun x => f x * g x) := by
    funext x
    rw [E.eval x, F.eval x]
    simp only [c, v, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact heq ▸ weightedSum R c (by linarith) hcard hc

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem trans {σ J K M : Type*} [Fintype J] [Fintype K] [Fintype M]
    {s : ℕ} {p : ℝ}
    {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ} {psi : M → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p chi eta) (F : NativeIntegerVectorEquivalence s p eta psi)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) (hp : 2 ≤ p) :
    NativeIntegerVectorEquivalence s (productNiltestBudget p + 2 * p + p) chi psi := by
  classical
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ productNiltestBudget p :=
    (sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0)
  have hpq : p ≤ productNiltestBudget p + 2 * p + p := by linarith
  refine {
    left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
    right_dimension := F.right_dimension.trans (Real.exp_le_exp.mpr hpq)
    expansion := ?_
  }
  intro j l
  let A : ∀ k, NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => chi j x * star (eta k x)) :=
    fun k => Classical.choice (E.expansion j k)
  let B : ∀ k, NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => eta k x * star (psi l x)) :=
    fun k => Classical.choice (F.expansion k l)
  let R := fun k => (A k).mul (B k) hp
  have hc : (∑ _ : K, ‖(1 : ℂ)‖) ≤ Real.exp p := by
    simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using E.right_dimension
  let S := NativeIntegerExpansion.weightedSum R (fun _ => 1) hp0 E.right_dimension hc
  have heq : (fun x => ∑ k, (1 : ℂ) *
      ((chi j x * star (eta k x)) * (eta k x * star (psi l x)))) =
      (fun x => chi j x * star (psi l x)) := by
    funext x
    calc
      _ = ∑ k, ((chi j x * star (psi l x)) * star (eta k x)) * eta k x := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := (complex_unit_vector_resolution (fun k => eta k x) (hunit x) _).symm
  exact ⟨heq ▸ S⟩

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DilationCost
namespace OAI

section

namespace Erdos3.DilationBudget

open scoped TensorProduct NNReal

theorem niltest_complexity {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s n : ℕ} (Q : RationalFilteredNilmanifold L s n) {w : σ → ℕ} (T : Q.Niltest w)
    (t : ℕ) (q : ℤ) (d H : ℕ) (A : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hQ : Q.GeometryComplexityLE p) (hd : (d : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (p + 1))
    (hA : (A : ℝ) ≤ Real.exp (reconstruction t q p))
    (hnorm : T.normBound = 1)
    (hlip : T.lipBound = rationalReconstructionLipschitzBound s d n H A 1) :
    T.ComplexityLE (total t q (MultilinearityBudget.reconstructionExponent s) p) := by
  have hR := reconstruction_bounds t q hp
  have hpR : p ≤ reconstruction t q p := (by linarith : p ≤ p + 1).trans hR.2
  have hTlip : (T.lipBound : ℝ) ≤ Real.exp
      ((reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
        MultilinearityBudget.reconstructionExponent s) := by
    rw [hlip]
    exact MultilinearityBudget.reconstructionExponent_control s d n H A 1 _ hR.1
      (hd.trans hpR) (hQ.1.trans hpR) (hH.trans (Real.exp_le_exp.mpr hR.2)) hA
      (by simpa only [NNReal.coe_one] using Real.one_le_exp hR.1)
  have hpower : 0 ≤ (reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
      MultilinearityBudget.reconstructionExponent s :=
    pow_nonneg (add_nonneg hR.1 (Nat.cast_nonneg _)) _
  have hlog := niltest_log_bound_of_exp T.normBound T.lipBound (a := 0) (by norm_num) hpower
    (by simp only [hnorm, NNReal.coe_one, Real.exp_zero, le_refl]) hTlip
  refine ⟨hQ.mono Q (total_bounds t q _ hp).1, ?_⟩
  have hlog' : Real.log (2 + (T.normBound : ℝ) + T.lipBound) ≤
      (reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
        MultilinearityBudget.reconstructionExponent s + 4 := by
    simpa only [zero_add] using hlog
  exact hlog'.trans (total_bounds t q _ hp).2

end Erdos3.DilationBudget

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def antisymmetricKernel {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x y : ℤ) : ℂ :=
  star (W.eval i (correlationInput x y)) * W.eval j (correlationInput y x)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

def HasNativeBiasedSquareInModel {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (A : Finset (σ → ℤ)) (h : σ → ℤ) (q : ℝ) : Prop :=
  ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
    (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp q) ∧
    ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
        let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
          (D.filtration.squareLattice D.lattice) N hN hin hout
        ∃ (ξ : (D.filtration.squareLieSubalgebra ⧸
            D.filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
          (V : Q.Niltest (fun _ : σ => 1)),
          V.orbit = D.filtration.squareFiltration.nativeReducedPolynomialOrbit (fun _ => 1) r ∧
          V.ComplexityLE q ∧
          (∀ i, rationalLogHeight (ξ (Q.basis i)) ≤ q) ∧
          (∀ z ∈ D.filtration.squareFiltration.quotientTop.realification.subgroup s, ∀ x,
            V.observable (z • x) =
              character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
          (∀ z : Q.RealGroup, z ∈ D.filtration.squareFiltration.quotientTop.realification.subgroup s →
            z ∈ Q.realLattice → ∃ n : ℤ, realifyFunctional ξ z.coord = n) ∧
          (∀ x : D.filtration.layer (s + 1),
            ξ (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
              (D.filtration.squareRelativeLayer s hs x).val) = η x) ∧
          Real.exp (-q) ≤ ‖𝔼 x ∈ A, V.eval x‖

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct BigOperators

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem topQuotientModel_basis_layers (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) (j : ℕ) :
    (F.topQuotientModel b w hF Γ N hN hin hout).filtration.layer j =
      Submodule.span ℚ ((F.topQuotientModel b w hF Γ N hN hin hout).basis ''
        {i | j ≤ quotientFinWeight w {i | s + 1 ≤ w i} i}) :=
  F.quotientFinBasis_layers b w hF (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hF (s + 1)) j

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

universe uσ uL

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)

variable {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

def HasNativeFactoredSquareInModel (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (S : σ → ℝ) (h : σ → ℤ) (p q : ℝ) : Prop :=
  ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
    (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp p) ∧
    ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
      ∃ ξ : (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ,
        (∀ i, rationalLogHeight (ξ ((Q).basis i)) ≤ p) ∧
        (∀ x : D.filtration.layer (s + 1),
          ξ (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
            (D.filtration.squareRelativeLayer s hs x).val) = η x) ∧
        (Q).filtration.ControlledSymbolFactorization (Q).basis
          (quotientFinWeight v {i | s + 1 ≤ v i}) hQ ξ S
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) q

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

def HasFixedNativeSquareFactors (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (S : σ → ℝ) (h : σ → ℤ) (p : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded) : Prop :=
  ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
    (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp p) ∧
    ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
      ∃ ξ : (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ,
        (∀ i, rationalLogHeight (ξ ((Q).basis i)) ≤ p) ∧
        (∀ x : D.filtration.layer (s + 1),
          ξ (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
            (D.filtration.squareRelativeLayer s hs x).val) = η x) ∧
        (∀ x ∈ W, basisGradeProjection
            ((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ)
            (quotientFinWeight v {i | s + 1 ≤ v i}) s x = x →
          (Q).filtration.gradedFrequency (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ ξ x = 0) ∧
        (Q).filtration.SymbolFactorizationIn (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ S
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) p l W

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFixedNativeSquareFamily
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def CommonNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        ∃ H : Finset (σ → ℤ), H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ H.card ∧
          ∀ h ∈ H,
            (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            (∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
            D.HasNativeBiasedSquareInModel
              (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
              (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
              (derivativeSupport (translatedIntegerBox origin lengths) h) h ((p + C) ^ C)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def InductiveNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        ∃ H : Finset (σ → ℤ), H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ H.card ∧
          ∀ h ∈ H,
            (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            (∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
            D.HasNativeFactoredSquareInModel
              (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
              (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
              (fun i => (lengths i : ℝ)) h ((p + C) ^ C) ((p + C) ^ C)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def CommonFixedNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        let Q := D.filtration.squareFiltration.topQuotientModel
          (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers e ω hF)
          (D.filtration.squareLattice D.lattice) N hN hin hout
        let ν := quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}
        let hQ := D.filtration.squareFiltration.topQuotientModel_basis_layers
          (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers e ω hF)
          (D.filtration.squareLattice D.lattice) N hN hin hout
        ∃ (H : Finset (σ → ℤ)) (l : ℕ) (W : LieSubalgebra ℚ Q.filtration.AssociatedGraded)
          (u : Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i}) → Q.filtration.AssociatedGraded),
          H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ H.card ∧
          0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
          BasisGradedSubmodule (Q.filtration.associatedGradedBasis Q.basis ν hQ) ν W.toSubmodule ∧
          BasisFamilyLogHeight (Q.filtration.associatedGradedBasis Q.basis ν hQ) u ((p + C) ^ C) ∧
          ∀ h ∈ H,
            (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            (∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
            D.HasFixedNativeSquareFactors
              (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
              (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
              (fun i => (lengths i : ℝ)) h ((p + C) ^ C) l W

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

namespace NativePolynomialOrbitFactors

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}

noncomputable def frozenMiddleValue (R : NativePolynomialOrbitFactors D g eta A p)
    (a r : D.RealGroup) (x : σ → ℤ) : D.RealGroup :=
  a * D.filtration.adaptedPolynomialRealValueHom
    (fun _ : σ => 1) (fun i => (x i : ℝ)) R.middle * r

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueEventOrDescent
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

noncomputable def ResiduePairDimensionDrop {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u v : σ → ℤ) (J : σ → ℕ) (B : ℝ) : Prop :=
  ∃ (flag : Bool) (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (z : Fin d → D.filtration.AssociatedGraded),
    0 < l ∧ (l : ℝ) ≤ Real.exp B ∧
    Submodule.span ℚ (Set.range z) = U.toSubmodule ∧
    BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
    (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (z i) j) ≤ B) ∧
    finrank ℚ ↥(W ⊓ U) < finrank ℚ W ∧
    D.filtration.SymbolFactorizationIn D.basis ω hF
      (fun i => (residueIndexLength (lo i) (lo i + N i) (M * residuePairStep J flag i : ℕ)
        (residuePairValue u v flag i) : ℝ))
      ((T.affinePullback (residueStepMatrix (residuePairStep J flag))
        (commonStrideIndex u M (residuePairValue u v flag))).symbol D.basis ω hF) B l U

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalEpochComparison
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {σ L : Type*}
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure EpochSymbolRecord (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) where
  fast : LieSubalgebra ℚ D.filtration.AssociatedGraded
  spanning : Fin d → D.filtration.AssociatedGraded
  budget : ℝ
  denominator : ℕ
  modulus : ℕ
  auxiliary : ℕ
  shift : σ → ℚ
  sides : σ → ℝ
  denominator_pos : 0 < denominator
  modulus_pos : 0 < modulus
  auxiliary_pos : 0 < auxiliary
  sides_pos : ∀ i, 0 < sides i
  denominator_le : (denominator : ℝ) ≤ Real.exp budget
  span_eq : Submodule.span ℚ (Set.range spanning) = fast.toSubmodule
  graded : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω fast.toSubmodule
  height_le : ∀ i j, rationalLogHeight
    ((D.filtration.associatedGradedBasis D.basis ω hF).repr (spanning i) j) ≤ budget
  factorization : D.filtration.SymbolFactorizationIn D.basis ω hF sides
    ((T.scalarAffinePullback ((modulus : ℚ) * auxiliary) shift).symbol D.basis ω hF)
    budget denominator fast

namespace EpochSymbolRecord

variable {D : RationalFilteredNilmanifold L s d} {ω : Fin d → ℕ}
  {hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})}
  {T : D.Niltest (fun _ : σ => 1)}

def Controlled (r : EpochSymbolRecord D ω hF T) (W : σ → ℝ) (p : ℝ) : Prop :=
  r.budget ≤ p ∧ (r.auxiliary : ℝ) ≤ Real.exp p ∧
    ∀ i, Real.exp (-p) * W i ≤ ((r.modulus : ℝ) * r.auxiliary) * r.sides i

end EpochSymbolRecord

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {σ L : Type*}
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {ω : Fin d → ℕ}
  {hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})}
  {T : D.Niltest (fun _ : σ => 1)}

noncomputable def epochRecordIntersection : List (EpochSymbolRecord D ω hF T) →
    LieSubalgebra ℚ D.filtration.AssociatedGraded
  | [] => ⊤
  | r :: rs => r.fast ⊓ epochRecordIntersection rs

inductive EpochRecordHistory : List (EpochSymbolRecord D ω hF T) → Prop
  | nil : EpochRecordHistory []
  | cons {r : EpochSymbolRecord D ω hF T} {rs : List (EpochSymbolRecord D ω hF T)}
      (history : EpochRecordHistory rs)
      (drop : finrank ℚ ↥(epochRecordIntersection rs ⊓ r.fast) <
        finrank ℚ (epochRecordIntersection rs)) : EpochRecordHistory (r :: rs)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

structure PhysicalEpochSource (σ : Type u) [Fintype σ] (s bound : ℕ) where
  Carrier : Type v
  [lieRing : LieRing Carrier]
  [lieAlgebra : LieAlgebra ℚ Carrier]
  [topology : TopologicalSpace (ℝ ⊗[ℚ] Carrier)]
  [topologicalAddGroup : IsTopologicalAddGroup (ℝ ⊗[ℚ] Carrier)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] Carrier)]
  [t2Space : T2Space (ℝ ⊗[ℚ] Carrier)]
  dimension : ℕ
  dimension_le : dimension ≤ bound
  model : RationalFilteredNilmanifold Carrier s dimension
  weights : Fin dimension → ℕ
  adapted : ∀ j, model.filtration.layer j = Submodule.span ℚ (model.basis '' {i | j ≤ weights i})
  fixedMap : model.Niltest (fun _ : σ => 1)
  lower : σ → ℤ
  sides : σ → ℕ
  sides_pos : ∀ i, 0 < sides i
  incomingBudget : ℝ
  recordBudget : ℝ
  incoming_nonneg : 0 ≤ incomingBudget
  incoming_le_record : incomingBudget ≤ recordBudget
  geometry : model.GeometryComplexityLE incomingBudget
  coordinates_le : (Fintype.card σ : ℝ) ≤ incomingBudget

attribute [instance] PhysicalEpochSource.lieRing PhysicalEpochSource.lieAlgebra
  PhysicalEpochSource.topology PhysicalEpochSource.topologicalAddGroup
  PhysicalEpochSource.continuousSMul PhysicalEpochSource.t2Space

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityRetained
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem fiberLaw_weight_eq_mass (p : FiniteProbabilityWeights X) (F : X → R) (r : R) :
    (p.fiberLaw F).weight r = p.mass (Finset.univ.filter (fun x => F x = r)) := by
  simpa only [fiberLaw_weight, fiberMean, Finset.mem_filter, Finset.mem_univ, true_and]
    using p.mean_indicator (Finset.univ.filter (fun x => F x = r))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedPrincipalSides_pos (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    0 < allocatedPrincipalSides B U basis S j :=
  layerSamplerSides_pos B U basis R S.positive (.inr j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialChoiceEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedPrincipalSides_le_scale (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    allocatedPrincipalSides B U basis S j ≤ S.value :=
  layerSamplerSides_le (G := G) B U basis R S.positive (.inr j)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem layeredSiteWeight_physicalCube {I K : Type*} [Fintype K] {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) (base : I → ℤ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (z : Option K × I → ℤ) :
    layeredSiteWeight 0 (fun s => affineSite root difference s)
        (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ)) =
      physicalCubeSiteTest test (physicalCubeRootDifferences root (Matrix.of difference) base z) := by
  simp only [layeredSiteWeight, map_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, one_mul, physicalCubeSiteTest]
  apply Finset.prod_congr rfl
  intro s _
  rw [integerSiteValue_affine_physical]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedParameterSite_bound (t : integerBox sides) (k : LayerSamplerVariables G I n B) :
    |(t.val k : ℝ)| ≤ S.value := by
  have ht := (mem_integerBox sides t.val).mp t.property k
  have hk : sides k ≤ S.value := by
    cases k with
    | inl g => exact le_rfl
    | inr j => exact allocatedPrincipalSides_le_scale B U b S j
  have hk' : (sides k : ℤ) ≤ (S.value : ℤ) := by exact_mod_cast hk
  have ht' : |t.val k| ≤ (S.value : ℤ) := by
    rw [abs_of_nonneg ht.1]
    exact ht.2.le.trans hk'
  exact_mod_cast ht'

theorem allocatedParameterSite_sum_bound (t : integerBox sides) :
    (∑ k, |(t.val k : ℝ)|) ≤ allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  calc
    _ ≤ ∑ _k : LayerSamplerVariables G I n B, (S.value : ℝ) :=
      Finset.sum_le_sum (fun k _ => allocatedParameterSite_bound B U b S t k)
    _ = _ := by simp [allocatedPhysicalRootBudget]

theorem allocatedParameterBox_nonempty : (integerBox sides).Nonempty := by
  have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U b S j
  let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
  exact integerBox_nonempty sides

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3

noncomputable def untranslatedMixedProduct {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (h₁ h₂ h₃ h₄ n : ℤ) : ℂ :=
  star (V.eval (k 0) (fun j => correlationInput h₁ n j.1)) *
    V.eval (k 1) (fun j => correlationInput h₂ n j.1) *
    V.eval (k 2) (fun j => correlationInput h₃ n j.1) *
    star (V.eval (k 3) (fun j => correlationInput h₄ n j.1))

noncomputable def mixedParallelogramProduct {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (k : Fin 4 → Fin V.outputDim) (x : Fin 4 → ℤ) : ℂ :=
  untranslatedMixedProduct V k (x 0) (x 1) (x 2) (x 1 + x 2 - x 0) (x 3)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

abbrev MixedExpansionIndex {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p) :=
  BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length

structure NativeMixedReductionData {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (P : ℝ) where
  budget_two : 2 ≤ P
  translation : NativeIntegerVectorEquivalence s P
    (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
    (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
      (mixedTranslationSample s x))
  lower : ∀ h δ : ℤ, ∀ a : MixedExpansionIndex V,
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) P
      (fun x => translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a
        (mixedTranslationSample s ![h, x (), δ]))
  parallelogram : ∀ k : Fin 4 → Fin V.outputDim,
    NativeIntegerExpansion (fun _ : Fin 4 => 1) s P (mixedParallelogramProduct V k)

end Erdos3

end

section

namespace Erdos3

namespace NativeMixedReductionData

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

structure TranslationCode (k : Fin 4 → Fin V.outputDim) where
  second : MixedExpansionIndex V
  fourth : MixedExpansionIndex V
  secondTerm : Fin (D.translation.selectedExpansion (k 1) second).count
  fourthTerm : Fin (D.translation.selectedExpansion (k 3) fourth).count

structure LowerCode {k : Fin 4 → Fin V.outputDim} (t : D.TranslationCode k) (h₂ h₄ δ : ℤ) where
  second : Fin (D.lower h₂ δ t.second).count
  fourth : Fin (D.lower h₄ δ t.fourth).count

end NativeMixedReductionData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def NativeMultidegreeNilcharacter.cubicAntisymmetricPair {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
    (i j : Fin V.outputDim × Fin V.outputDim) (h n k : ℤ) : ℂ :=
  (star (V.eval i.1 (cubicTrilinearInput h n k)) * V.eval j.1 (cubicTrilinearInput n h k)) *
    (star (V.eval i.2 (cubicTrilinearInput h n k)) * V.eval j.2 (cubicTrilinearInput n h k))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3.NativeCrossWitnesses

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f₀ f₁ : ZMod N → ℂ}
  {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
  (U : NativeCrossWitnesses s N p f₀ f₁ m H)

noncomputable def integerLower (h : H) (n : ℤ) : ℂ := (U h).test.eval (fun _ => n)

noncomputable def integerProduct (M : ZMod N → ℤ → ℂ) (h : H) (n : ℤ) : ℂ :=
  M h.val n * U.integerLower h n

end Erdos3.NativeCrossWitnesses

end

section

namespace Erdos3

open scoped BigOperators

structure NativeIntegerQuadrupleWitness {s N : ℕ} [NeZero N] {p : ℝ}
    {f₀ f₁ : ZMod N → ℂ} {m : ZMod N → ZMod N → ℂ} {H : Finset (ZMod N)}
    (U : NativeCrossWitnesses s N p f₀ f₁ m H) (M : ZMod N → ℤ → ℂ)
    (q : ℝ) (t : ZMod N × ZMod N × ZMod N) where
  first_mem : t.2.1 ∈ H
  second_mem : t.2.1 - t.1 ∈ H
  third_mem : t.2.2 ∈ H
  fourth_mem : t.2.2 - t.1 ∈ H
  integer_relation :
    -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0
  cyclic_correlation : Real.exp (-q) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2
  branch : Bool
  start : ℕ
  length : ℕ
  length_pos : 0 < length
  endpoint_le : start + length ≤ N
  length_short : 2 * ((length : ℤ) - 1) < N
  correlation : Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (start : ℤ) (start + length),
    fourPointProduct
      (U.integerProduct M ⟨t.2.1, first_mem⟩)
      (U.integerProduct M ⟨t.2.1 - t.1, second_mem⟩)
      (U.integerProduct M ⟨t.2.2, third_mem⟩)
      (U.integerProduct M ⟨t.2.2 - t.1, fourth_mem⟩)
      (cyclicBranchOffset t.1 branch) n‖
  length_ratio : Real.exp (-q) ≤ (length : ℝ) / N

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductCoefficient
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

theorem exists_controlled_horizontal_lifts
    {μ κ σ : Type*} [Fintype μ] [Fintype κ]
    (b : Basis μ ℚ L) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = F.layer d 1)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hfH : ∀ j i, RationalHeightLE (F.ambientHorizontalCoordinates d f (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧ l ∣ m ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (x y z : ℝ ⊗[ℚ] F.HigherHorizontal d)
        (a q : ι → ℝ), F.realHigherHorizontalCoordinates d f (x - y - z) = a + q →
        ‖a‖ ≤ Real.exp p / monomialScale T α → q ∈ realDenominatorGrid l →
        ∃ E Q : (F.layer d 1).baseChange ℝ,
          F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d E) = a ∧
          F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d Q) = q ∧
          x - y - F.realHorizontalMap d E - F.realHorizontalMap d Q = z ∧
          ‖(b.baseChange ℝ).equivFun E.val‖ ≤
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          (b.baseChange ℝ).equivFun Q.val ∈ realDenominatorGrid m := by
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_controlled_coordinate_lifts b (F.layer d 1) v hv
    (F.ambientHorizontalCoordinates d f) hH hl hvH hfH hp hμ hι hκ hHp hlp T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα x y z a q heq ha hq
  have hsum := F.realHigherHorizontalCoordinates_mem d f (x - y - z)
  rw [heq] at hsum
  obtain ⟨E, Q, hE, hQ, hEa, hQq, hslow, hgrid⟩ := hsolve α hα a q hsum ha hq
  let E' : (F.layer d 1).baseChange ℝ := ⟨E, hE⟩
  let Q' : (F.layer d 1).baseChange ℝ := ⟨Q, hQ⟩
  have hEa' : F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d E') = a :=
    (F.realHigherHorizontalCoordinates_map d f E').trans hEa
  have hQq' : F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d Q') = q :=
    (F.realHigherHorizontalCoordinates_map d f Q').trans hQq
  refine ⟨E', Q', hEa', hQq', ?_, hslow, hgrid⟩
  apply F.realHigherHorizontalCoordinates_injective d f
  simp only [map_sub] at heq ⊢
  rw [hEa', hQq']
  linear_combination heq

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ)

theorem realFourLayerComponent_grid {ι : Type*} (b : Basis ι ℚ L)
    (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) (l : ℕ)
    (hx : (fun j => ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x.val j) ∈ realDenominatorGrid l) :
    (fun i => (b.baseChange ℝ).repr (F.realFourLayerComponent d k x).val i) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => z ⟨k, i⟩, ?_⟩
  funext i
  exact (congrFun hz ⟨k, i⟩).trans (congrArg (fun a : ℝ => (l : ℝ) * a)
    (real_pi_projection_coordinates b x.val k i).symm)

end DegreeRankLieFiltration
end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem rankLayerCoefficient_tensor_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w) :
    (F.layer (Finsupp.weight w α) 1).subtype.baseChange ℝ
        ((F.rankLayerCoefficient w α).baseChange ℝ x) =
      coefficients (F.associatedDegree.realAdaptedPolynomialMap w x) α := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply,
      F.rankLayerCoefficient_coe, F.associatedDegree.realAdaptedPolynomialMap_coefficient_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem rankLayerCoefficient_tensor_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w) :
    (F.higherHorizontalMk (Finsupp.weight w α)).baseChange ℝ
        ((F.rankLayerCoefficient w α).baseChange ℝ x) =
      (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ)

def horizontalPreimage (U : Submodule ℚ (F.HigherHorizontal d)) : Submodule ℚ L :=
  (U.comap (F.higherHorizontalMk d)).map (F.layer d 1).subtype

theorem horizontalPreimage_le (U : Submodule ℚ (F.HigherHorizontal d)) :
    F.horizontalPreimage d U ≤ F.layer d 1 := by
  rintro x ⟨v, _, rfl⟩
  exact v.property

theorem horizontalPreimage_mono {U V : Submodule ℚ (F.HigherHorizontal d)} (h : U ≤ V) :
    F.horizontalPreimage d U ≤ F.horizontalPreimage d V :=
  Submodule.map_mono (Submodule.comap_mono h)

theorem mem_horizontalPreimage (U : Submodule ℚ (F.HigherHorizontal d))
    (v : F.layer d 1) :
    v.val ∈ F.horizontalPreimage d U ↔ F.higherHorizontalMk d v ∈ U := by
  constructor
  · rintro ⟨w, hw, h⟩
    have he : w = v := Subtype.ext h
    exact he ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem horizontalPreimage_coordinates {ι : Type*} [Fintype ι]
    (f : Basis ι ℚ (L ⧸ F.layer d 2)) (U : Submodule ℚ (F.HigherHorizontal d)) :
    F.horizontalPreimage d U = F.layer d 1 ⊓
      (U.map (F.higherHorizontalCoordinates d f)).comap (F.ambientHorizontalCoordinates d f) := by
  ext x
  constructor
  · intro hx
    have hxl := F.horizontalPreimage_le d U hx
    exact ⟨hxl, ⟨F.higherHorizontalMk d ⟨x, hxl⟩,
      (F.mem_horizontalPreimage d U ⟨x, hxl⟩).mp hx, rfl⟩⟩
  · rintro ⟨hxl, y, hy, he⟩
    apply (F.mem_horizontalPreimage d U ⟨x, hxl⟩).mpr
    have he' : y = F.higherHorizontalMk d ⟨x, hxl⟩ :=
      F.higherHorizontalCoordinates_injective d f he
    exact he' ▸ hy

theorem mem_real_horizontalPreimage (U : Submodule ℚ (F.HigherHorizontal d))
    (v : (F.layer d 1).baseChange ℝ) :
    v.val ∈ (F.horizontalPreimage d U).baseChange ℝ ↔
      F.realHorizontalMap d v ∈ U.baseChange ℝ := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer d 1)).surjective v
  rw [F.realHorizontalMap_baseChange, realificationSubmoduleEquiv_coe,
    horizontalPreimage, realification_map, realification_comap]
  constructor
  · rintro ⟨y, hy, he⟩
    have hyx : y = x := realification_subtype_injective (F.layer d 1) he
    exact hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeDegreeRankNilmanifold
namespace OAI

section

namespace Erdos3

theorem scaledIntegerGrid_le_denominatorGrid {ι : Type*} (a b : ℕ) :
    (scaledIntegerGrid a : Set (ι → ℚ)) ⊆ denominatorGrid b := by
  rintro x ⟨z, rfl⟩
  exact ((show IntegralVector (fun i => (z i : ℚ)) from ⟨z, fun _ => rfl⟩).nat_smul a).nat_smul b

namespace DegreeRankLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis (Fin d) ℚ L)
  (htail : ∀ i j, ∃ c ≤ d, F.layer i j = basisTail b c)

variable (B : ℕ) (hB : 0 < B)
  (hstable : ∀ x ∈ coordinateGridModule b B, ∀ y ∈ coordinateGridModule b B,
    lieBCH s x y ∈ coordinateGridModule b B)

noncomputable def integralGridNilmanifold : RationalFilteredNilmanifold L s d where
  filtration := F.associatedDegree
  basis := b
  layerBasis i := F.tailLayerBasis b htail (i.val + 1) 0
  lattice := coordinateGridBCHSubgroup b B F.associatedDegree.lowerCentralSeries_eq_bot hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
  outer_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
    exact scaledIntegerGrid_le_denominatorGrid B B

noncomputable def integralGridDegreeRank :
    (F.integralGridNilmanifold b htail B hB hstable).DegreeRankStructure r where
  filtration := F
  associated := rfl
  basis i j := F.tailLayerBasis b htail i.val j.val

theorem integralGridNilmanifold_coordinates :
    bchSubgroupCoordinates (F.integralGridNilmanifold b htail B hB hstable).basis
      (F.integralGridNilmanifold b htail B hB hstable).lattice = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates b B F.associatedDegree.lowerCentralSeries_eq_bot hstable

theorem integralGridDegreeRank_complexity {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hgrid : (B : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) :
    (F.integralGridDegreeRank b htail B hB hstable).ComplexityLE p := by
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp p := by
    simpa only [Nat.cast_one, Real.exp_zero] using Real.exp_le_exp.mpr hp
  refine ⟨⟨hd, hgrid, hc, ?_⟩, ?_⟩
  · intro i a k
    exact rationalLogHeight_le_of_height (F.tailLayerBasis_height b htail (i.val + 1) 0 a k) hone
  · intro i j a k
    exact rationalLogHeight_le_of_height (F.tailLayerBasis_height b htail i.val j.val a k) hone

end DegreeRankLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {X : Type*} [Fintype X] {s r : ℕ} {w : X → ℕ} {hw : ∀ x, 0 < w x}

structure FreeCoordinateFrame
    (b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
      (FreeDegreeRankLieAlgebra X s r w hw)) (p : ℝ) where
  tree_height : ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
    rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ p
  sourceBasis : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ
    (FreeNilpotentLieAlgebra X s)
  sourceBasis_trees : ∀ i, sourceBasis i ∈ FreeNilpotentLieAlgebra.treeGenerators X s
  sourceDimension : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ p
  sectionMatrix : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
    (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
  section_right_inverse : LinearMap.toMatrix sourceBasis b
    (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * sectionMatrix = 1
  section_height : ∀ i j, rationalLogHeight (sectionMatrix i j) ≤ p

namespace FreeCoordinateFrame

variable {b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
    (FreeDegreeRankLieAlgebra X s r w hw)} {p q : ℝ}

def mono (F : FreeCoordinateFrame b p) (hpq : p ≤ q) : FreeCoordinateFrame b q where
  tree_height x hx i := (F.tree_height x hx i).trans hpq
  sourceBasis := F.sourceBasis
  sourceBasis_trees := F.sourceBasis_trees
  sourceDimension := F.sourceDimension.trans hpq
  sectionMatrix := F.sectionMatrix
  section_right_inverse := F.section_right_inverse
  section_height i j := (F.section_height i j).trans hpq

end FreeCoordinateFrame
end Erdos3

end

section

namespace Erdos3

open Module

theorem FreeCoordinateFrame.generator_height
    {X : Type*} [Fintype X] {s r : ℕ} {w : X → ℕ} {hw : ∀ x, 0 < w x}
    {b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
      (FreeDegreeRankLieAlgebra X s r w hw)} {p : ℝ}
    (F : FreeCoordinateFrame b p) (hs : 1 ≤ s) (x : X) (i) :
    rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.of X s r w hw x) i) ≤ p :=
  F.tree_height (FreeNilpotentLieAlgebra.of X s x)
    (FreeNilpotentLieAlgebra.of_mem_treeGenerators X s hs x) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem NilpotentLieFiltration.top_rank_map_mem_degreeLengthSpan {s k : ℕ}
    (F : NilpotentLieFiltration L s) (φ : L →ₗ⁅ℚ⁆ M) (v : X → M) (w : X → ℕ)
    (hspan : ∀ d, 0 < d → ∀ x ∈ F.layer d, φ x ∈ weightedLieDegreeLengthSpan v w d 1)
    {x : L} (hx : x ∈ F.rankLayer s k) :
    φ x ∈ weightedLieDegreeLengthSpan v w s k := by
  rw [NilpotentLieFiltration.rankLayer, F.terminal, bot_sup_eq] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hkl, a, rfl⟩ := hx
    exact weightedLieDegreeLengthSpan_antitone v w le_rfl hkl
      (a.map_eval_mem_degreeLengthSpan φ v w hspan)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem FreeWeightedNilpotentLieAlgebra.lift_layer_mem_degreeLengthSpan {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : X → ℕ) (hw : ∀ i, 0 < w i)
    (f : X → L) (hf : ∀ i, f i ∈ F.layer (w i))
    {d : ℕ} {x : FreeWeightedNilpotentLieAlgebra X s w}
    (hx : x ∈ (filtration X s w hw).layer d) :
    lift F w f hf x ∈ weightedLieDegreeLengthSpan f w d 1 := by
  obtain ⟨a, ha, rfl⟩ := hx
  change FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot a ∈
    weightedLieDegreeLengthSpan f w d 1
  have h := weightedLieUpperSpan_map_le_degreeLengthSpan
    (FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot)
    (FreeNilpotentLieAlgebra.of X s) w d ⟨a, ha, rfl⟩
  change FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot a ∈
    weightedLieDegreeLengthSpan
      (fun i => FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot
        (FreeNilpotentLieAlgebra.of X s i)) w d 1 at h
  have heq : (fun i => FreeNilpotentLieAlgebra.lift f F.lowerCentralSeries_eq_bot
      (FreeNilpotentLieAlgebra.of X s i)) = f :=
    funext (fun i => FreeNilpotentLieAlgebra.lift_of f F.lowerCentralSeries_eq_bot i)
  rw [heq] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeSignalAlgebra
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

noncomputable def mixedCubeWithShift {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : (Fin d → Bool) → ℤ) (a : (Fin d → Bool) → Fin M.outputDim)
    (x : Fin (d + 2) → ℤ) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω)
    (M.eval (a ω) (mixedCubeInput ω x + ![0, c ω]))

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicRootPermutation
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicPairComponent (out : Fin W.outputDim × Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) : W.model.Niltest (fun _ : Fin 3 => 1) :=
  ((W.tensorPower 2).component ((tensorIndexEquiv W.outputDim 2) ![out.1, out.2])).affinePullback
    (fun j l => if l = (if j.1 = 0 then h else if j.2.val = 0 then y else k) then 1 else 0)
    (fun j => if j.1 = 0 then 0 else if j.2.val = 0 then 0 else shift)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicProductDetection
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

def CyclicProductNiltestDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {ι : Type v} [Fintype ι] {L : ι → Type u}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (p : ℝ),
    0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
    ∀ (w : Fin 1 → ℕ), (∀ j, 0 < w j) →
    ∀ (T : ∀ i, (D i).Niltest w), (∀ i, (T i).ComplexityLE p) →
    ∀ (N : ℕ) [NeZero N] (h : ι → ZMod N) (f : ZMod N → ℂ),
    (∀ x, ‖f x‖ ≤ 1) →
    Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
      (translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n)))‖ →
    Real.exp (-F p) ≤ gowersNorm (s + 1) f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedReplicated_totalDegree (n : ℕ) :
    (∑ _ : MixedReplicatedIndex (n + 1), (1 : ℕ)) = n + 2 := by
  have hc : Fintype.card (MixedReplicatedIndex (n + 1)) = n + 2 := replicatedMixed_card (n + 1)
  rw [Finset.sum_const, Finset.card_univ, hc]
  simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedRankIntegralModel
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (e : Basis (Fin d) ℚ L)
  (b : ∀ i : Fin (s + 1), Basis (Fin (finrank ℚ (F.associatedDegree.layer (i.val + 1))))
    ℚ (F.associatedDegree.layer (i.val + 1)))
  (c : ∀ i j : Fin (s + 1), Basis (Fin (finrank ℚ (F.layer i.val j.val)))
    ℚ (F.layer i.val j.val))
  (B : ℕ) (hB : 0 < B)
  (hstable : ∀ x ∈ coordinateGridModule e B, ∀ y ∈ coordinateGridModule e B,
    lieBCH s x y ∈ coordinateGridModule e B)

noncomputable def boundedRankIntegralModel : RationalFilteredNilmanifold L s d where
  filtration := F.associatedDegree
  basis := e
  layerBasis := b
  lattice := coordinateGridBCHSubgroup e B F.associatedDegree.lowerCentralSeries_eq_bot hstable
  grid := B
  grid_pos := hB
  inner_grid := by rw [coordinateGridBCHSubgroup_coordinates]
  outer_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
    exact scaledIntegerGrid_le_denominatorGrid B B

noncomputable def boundedRankIntegralStructure :
    (F.boundedRankIntegralModel e b B hB hstable).DegreeRankStructure r where
  filtration := F
  associated := rfl
  basis := c

theorem boundedRankIntegralModel_coordinates :
    bchSubgroupCoordinates (F.boundedRankIntegralModel e b B hB hstable).basis
      (F.boundedRankIntegralModel e b B hB hstable).lattice = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates e B F.associatedDegree.lowerCentralSeries_eq_bot hstable

theorem boundedRankIntegralStructure_complexity {H : ℕ}
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    {p : ℝ} (hd : (d : ℝ) ≤ p) (hgrid : (B : ℝ) ≤ Real.exp p)
    (hheight : (H : ℝ) ≤ Real.exp p) :
    (F.boundedRankIntegralStructure e b c B hB hstable).ComplexityLE p :=
  ⟨⟨hd, hgrid, fun i j k => rationalLogHeight_le_of_height (hbracket i j k) hheight,
    fun i a j => rationalLogHeight_le_of_height (hb i a j) hheight⟩,
    fun i j a k => rationalLogHeight_le_of_height (hc i j a k) hheight⟩

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedTargetCubeIntervals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def HasWeightedTargetCubeIntervals {J : Type*} [Fintype J] {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin 2 → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (w : (Fin (d + 1) → Bool) → J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            (cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
              star (mixedCubeObservable η w (mixedDifferencePoint t n))) *
              ∏ i, A i (mixedDifferencePoint t n)‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSeparatedSumIntervals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def HasMixedTargetIntervals {J : Type*} {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)‖

def HasCommonMixedTargetInterval {J : Type*} {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)‖

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem HasMixedTargetIntervals.common {J : Type*} {d N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin (d + 3) → ℤ) → ℂ} (H : HasMixedTargetIntervals f M η q)
    (hq : 0 ≤ q) (hN : Real.exp (2 * q + 8) ≤ (N : ℝ))
    (hf : ∀ x, ‖f x‖ ≤ 1) (hη : ∀ j x, ‖η j x‖ ≤ 1) :
    HasCommonMixedTargetInterval f M η (5 * q + 10) := by
  classical
  obtain ⟨j, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  have hdata (t : Q) := hcorr t.val t.property
  choose hshift start len hlen hend hshort hvol hcor using hdata
  let signal (t : Q) (n : ℤ) :=
    star (f ((∑ k, mixedDifferencePoint t.val n k : ℤ) : ZMod N)) *
      star (η j (mixedDifferencePoint t.val n)) * ∏ i, A i (mixedDifferencePoint t.val n)
  let : Nonempty Q := hQ.to_subtype
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hsignal (t : Q) (n : ℤ) : ‖signal t n‖ ≤ 1 := by
    dsimp only [signal]
    rw [norm_mul, norm_mul, norm_star, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hη j _))).trans
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hA i _)
  obtain ⟨S, _, hS, hSdense, a, len', hlen', hend', hshort', hvol', hScor⟩ :=
    exists_common_integer_interval hq hN Finset.univ Finset.univ_nonempty start len
      (fun t _ => hend t) (fun t _ => hshort t)
      (fun t _ => (le_div_iff₀ hNpos).mp (hvol t)) signal
      (fun t _ n => hsignal t n) (fun t _ => hcor t)
  let embed : Q ↪ ((Fin (d + 1) → ZMod N) × ZMod N) := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hsize : Real.exp (-(4 * q + 10)) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  have hbudget : q + 1 ≤ 5 * q + 10 := by linarith
  refine ⟨j, A, hA, hAi, a, len', hlen', hend', hshort', ?_, Q', hS.map, ?_, ?_⟩
  · apply (le_div_iff₀ hNpos).mpr
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbudget)) hNpos.le).trans hvol'
  · calc
      _ = Real.exp (-(4 * q + 10)) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(4 * q + 10)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact ⟨hshift t', (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans (hScor t' ht')⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem HasCommonMixedTargetInterval.positive {J : Type*} {d N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin (d + 3) → ℤ) → ℂ} (H : HasCommonMixedTargetInterval f M η q)
    (hq : 0 ≤ q) : HasPositiveMixedTargetInterval f η (2 * q) := by
  classical
  obtain ⟨j, A, hA, hAi, a, len, hlen, hend, hshort, hvol, Q, _, hdense, hcorr⟩ := H
  let row (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :=
    star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
      star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)
  have hdensity : Real.exp (-q) * Fintype.card ((Fin (d + 1) → ZMod N) × ZMod N) ≤
      (Q.card : ℝ) := by
    simpa only [mixedProfile_card, Nat.cast_pow] using hdense
  obtain ⟨w, hw, _, hpositive⟩ := exists_dense_row_phase_alignment Q
    (Finset.Ico (a : ℤ) (a + len)) row (Real.exp_nonneg (-q)) hdensity
      (fun t ht => (hcorr t ht).2)
  let phase (x : Fin (d + 3) → ℤ) :=
    w (mixedProfileFromCoordinates (fun k => (x k : ZMod N)))
  let B (i : Fin (d + 3)) (x : Fin (d + 3) → ℤ) :=
    (if i = 1 then phase x else 1) * A i x
  have hB : ∀ i x, ‖B i x‖ ≤ 1 := by
    intro i x
    by_cases hi : i = 1
    · simp only [B, hi, ite_true, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw _) (norm_nonneg _)).trans (by
        simpa only [one_mul] using hA 1 x)
    · simpa only [B, hi, ite_false, one_mul] using hA i x
  have hBi : ∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y := by
    intro i x y hxy
    by_cases hi : i = 1
    · subst i
      simp only [B, ite_true]
      rw [hAi 1 x y hxy]
      congr 1
      apply congrArg w
      exact mixedProfileFromCoordinates_independent _ _ (fun k hk => congrArg (fun z : ℤ => (z : ZMod N)) (hxy k hk))
    · simpa only [B, hi, ite_false, one_mul] using hAi i x y hxy
  have hphase (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
      phase (mixedDifferencePoint t n) = w t := by
    exact congrArg w (mixedProfileFromCoordinates_point t n)
  have hprod (x : Fin (d + 3) → ℤ) : (∏ i, B i x) = phase x * ∏ i, A i x := by
    simp only [B, Finset.prod_mul_distrib]
    simp
  have hpoint (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
      star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
        star (η j (mixedDifferencePoint t n)) * ∏ i, B i (mixedDifferencePoint t n) = w t * row t n := by
    rw [hprod, hphase]
    dsimp only [row]
    ring
  refine ⟨j, B, hB, hBi, a, len, hlen, hend, hshort,
    (Real.exp_le_exp.mpr (by linarith : -(2 * q) ≤ -q)).trans hvol, ?_⟩
  have hscore : Real.exp (-(2 * q)) ≤
      (𝔼 t, 𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), w t * row t n).re := by
    have heq : Real.exp (-(2 * q)) = Real.exp (-q) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hpositive
  simpa only [hpoint] using hscore

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistCellSelection
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def fiberComplexMean {X R : Type*} [Fintype X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (r : R) (f : X → ℂ) : ℂ :=
  p.complexMean (fun x => if F x = r then f x else 0)

theorem sum_fiberComplexMean_on {X R : Type*} [Fintype X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (S : Finset R) (f : X → ℂ) :
    (∑ r ∈ S, p.fiberComplexMean F r f) = p.complexMean (fun x => if F x ∈ S then f x else 0) := by
  unfold fiberComplexMean complexMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  by_cases h : F x ∈ S <;> simp [eq_comm, h]

theorem mass_mul_condition_complexMean {X : Type*} [Fintype X] [DecidableEq X]
    (p : FiniteProbabilityWeights X) (G : Finset X) (hG : 0 < p.mass G) (f : X → ℂ) :
    (p.mass G : ℂ) * (p.condition G hG).complexMean f =
      p.complexMean (fun x => if x ∈ G then f x else 0) := by
  have h := p.mass_mul_condition_correlation G hG f (fun _ => 1)
  simpa only [correlation, complexMean, finiteMask_apply, star_one, mul_one] using h

theorem fiberComplexMean_eq_condition {X R : Type*} [Fintype X] [DecidableEq X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (r : R) (f : X → ℂ)
    (hG : 0 < p.mass (Finset.univ.filter (fun x => F x = r))) :
    p.fiberComplexMean F r f =
      (p.mass (Finset.univ.filter (fun x => F x = r)) : ℂ) *
        (p.condition (Finset.univ.filter (fun x => F x = r)) hG).complexMean f := by
  rw [p.mass_mul_condition_complexMean]
  simp only [fiberComplexMean, Finset.mem_filter, Finset.mem_univ, true_and]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X C : Type*} [Fintype X] [DecidableEq X]
  [Fintype C] [DecidableEq C] [Nonempty C]

theorem exists_large_correlating_fiber (p : FiniteProbabilityWeights X)
    (cell : X → C) (f : X → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hbias : δ ≤ ‖p.complexMean f‖) :
    ∃ (c : C) (hc : 0 < p.mass (Finset.univ.filter (fun x => cell x = c))),
      δ / (2 * Fintype.card C) ≤ p.mass (Finset.univ.filter (fun x => cell x = c)) ∧
      δ / 2 ≤ ‖(p.condition (Finset.univ.filter (fun x => cell x = c)) hc).complexMean f‖ := by
  let mass := fun c => p.mass (Finset.univ.filter (fun x => cell x = c))
  let term := fun c => p.fiberComplexMean cell c f
  have hmass : (∑ c, mass c) = 1 := by
    simpa only [mass, ← p.fiberLaw_weight_eq_mass cell] using (p.fiberLaw cell).total
  have hsum : (∑ c, term c) = p.complexMean f := by
    simpa only [term, Finset.mem_univ, ite_true] using
      p.sum_fiberComplexMean_on cell Finset.univ f
  have hcap (c : C) : ‖term c‖ ≤ mass c := by
    apply (p.norm_complexMean_le_mean_norm _).trans
    dsimp only [mass]
    rw [← p.mean_indicator (Finset.univ.filter (fun x => cell x = c))]
    apply p.mean_mono
    intro x
    by_cases hx : cell x = c
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hx, ite_true] using hf x
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx, ite_false, norm_zero, le_refl]
  have hcard : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hscore : δ / (2 * Fintype.card C) ≤
      𝔼 c, (‖term c‖ - δ / 2 * mass c) := by
    rw [Fintype.expect_eq_sum_div_card, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, mul_one]
    have hn := (norm_sum_le _ _).trans' (hsum.symm ▸ hbias)
    apply (le_div_iff₀ hcard).mpr
    have he : δ / (2 * Fintype.card C) * Fintype.card C = δ / 2 := by
      field_simp
    rw [he]
    linarith
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hscore
  have hsmall : 0 < δ / (2 * Fintype.card C) := div_pos hδ (by positivity)
  have hmass0 : 0 ≤ mass c := p.mass_nonneg _
  have hmasslower : δ / (2 * Fintype.card C) ≤ mass c := by
    nlinarith [hcap c]
  have hmasspos : 0 < mass c := hsmall.trans_le hmasslower
  refine ⟨c, hmasspos, hmasslower, ?_⟩
  have hid : ‖term c‖ = mass c *
      ‖(p.condition (Finset.univ.filter (fun x => cell x = c)) hmasspos).complexMean f‖ := by
    dsimp only [term]
    rw [p.fiberComplexMean_eq_condition cell c f hmasspos, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hmass0]
  rw [hid] at hc
  nlinarith

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IndependentEmbeddedMixture
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
  [∀ j, DecidableEq (R j)]

theorem pi_fiber_mass (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (r : ∀ j, R j) :
    (pi p).mass (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) =
      ∏ j, (p j).mass (Finset.univ.filter (fun x => F j x = r j)) := by
  rw [pi_fiber_set, piRestriction_mass]

theorem pi_fiber_mass_pos (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (r : ∀ j, R j)
    (hr : ∀ j, 0 < (p j).mass (Finset.univ.filter (fun x => F j x = r j))) :
    0 < (pi p).mass (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) := by
  rw [pi_fiber_mass]
  exact Finset.prod_pos (fun j _ => hr j)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveFiberMarginal
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
variable [∀ j, DecidableEq (R j)]
variable (p : ∀ j, FiniteProbabilityWeights (X j))
variable (F : ∀ j, X j → R j) (r : ∀ j, R j)
variable (hcell : 0 < (pi p).mass
  (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)))

include hcell in
theorem coordinate_fiber_mass_pos (j : J) :
    0 < (p j).mass (Finset.univ.filter (fun x => F j x = r j)) := by
  have hp : 0 < ∏ k, (p k).mass (Finset.univ.filter (fun x => F k x = r k)) := by
    simpa only [pi_fiber_mass] using hcell
  have hn := Finset.prod_ne_zero_iff.mp hp.ne' j (Finset.mem_univ j)
  exact lt_of_le_of_ne ((p j).mass_nonneg _) hn.symm

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftTestingGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

def CyclicShiftTestingDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {ι : Type v} [Nonempty ι] {L : ι → Type u}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (p : ℝ),
    2 ≤ p → ∀ (w : Fin 1 → ℕ), (∀ j, 0 < w j) →
    ∀ (T : ∀ i, (D i).Niltest w), (∀ i, (T i).ComplexityLE p) →
    ∀ (N : ℕ) [NeZero N], (∀ i (x : ZMod N), ‖(T i).eval (fun _ => (x.val : ℤ))‖ ≤ 1) →
    ∀ (v B : ZMod N → ℂ), (∀ x, ‖v x‖ ≤ 1) → (∀ x, ‖B x‖ ≤ Real.exp p) →
    Real.exp (-p) ≤ shiftTestingSeminorm B (fun i x => (T i).eval (fun _ => (x.val : ℤ))) v →
    Real.exp (-F p) ≤ gowersNorm (s + 2) v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

def CyclicTranslatedShiftTestingDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {ι : Type v} [Nonempty ι] {L : ι → Type u}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (p : ℝ),
    2 ≤ p → ∀ (w : Fin 1 → ℕ), (∀ j, 0 < w j) →
    ∀ (T : ∀ i, (D i).Niltest w), (∀ i, (T i).ComplexityLE p) →
    ∀ (N : ℕ) [NeZero N], (∀ i (x : ZMod N), ‖(T i).eval (fun _ => (x.val : ℤ))‖ ≤ 1) →
    ∀ (v B : ZMod N → ℂ), (∀ x, ‖v x‖ ≤ 1) → (∀ x, ‖B x‖ ≤ Real.exp p) →
    Real.exp (-p) ≤ shiftTestingSeminorm B
      (translatedTestFamily (fun i x => (T i).eval (fun _ => (x.val : ℤ)))) v →
    Real.exp (-F p) ≤ gowersNorm (s + 2) v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSliceParameterCellLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem complexMean_finitePushforward_relativeSlice {U T : Type*} [Fintype U] [Fintype T]
    (p : FiniteProbabilityWeights U) (f : U → T) (g : T → ℂ) :
    (p.finitePushforward f).complexMean g = p.complexMean (fun u => g (f u)) := by
  simp only [complexMean, finitePushforward, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp [apply_ite, ite_mul]

theorem uniform_finitePushforward_complexMean {U T : Type*}
    [Fintype U] [Nonempty U] [Fintype T] (f : U → T) (g : T → ℂ) :
    ((uniform U).finitePushforward f).complexMean g = 𝔼 u, g (f u) := by
  rw [complexMean_finitePushforward_relativeSlice, uniform_complexMean]

theorem uniform_condition_complexMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (G : Finset Ω) (hG : 0 < (uniform Ω).mass G) (f : Ω → ℂ) :
    ((uniform Ω).condition G hG).complexMean f = 𝔼 x ∈ G, f x := by
  have hc : (Fintype.card Ω : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hg : (G.card : ℂ) ≠ 0 := by
    have hgNat : G.card ≠ 0 := by
      intro hz
      rw [uniform_mass, hz, Nat.cast_zero, zero_div] at hG
      exact (lt_irrefl _ hG)
    exact_mod_cast hgNat
  have hm : (((uniform Ω).mass G : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  apply (mul_left_cancel₀ hm)
  rw [mass_mul_condition_complexMean, uniform_complexMean, uniform_mass,
    Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  have hsum : (∑ x, if x ∈ G then f x else 0) = ∑ x ∈ G, f x := by simp
  rw [hsum, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
  field_simp

end FiniteProbabilityWeights

namespace ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

theorem fullSliceLaw_complexMean (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i)
    (f : integerBox N → ℂ) :
    (S.fullSliceLaw hlen).complexMean f = 𝔼 u, f (S.fullSlicePointInIntegerBox u) := by
  let : ∀ i, Nonempty (Fin (S.length i)) := fun i => ⟨⟨0, hlen i⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)

variable (hH : ∀ j, 0 < H j)

noncomputable def principalAffineIntervalLaw : FiniteProbabilityWeights (PrincipalIntegerTuples B h Empty L) := by
  letI : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  exact (FiniteProbabilityWeights.uniform (∀ j, Fin (H j))).finitePushforward
    (principalAffineIntervalPoint B h L H step start hinside)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PhysicalSiteProjection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

noncomputable def physicalEuclideanSitePoint (w : X → ℝ) (j : Fin m) : euclideanSubspace (U j) :=
  (euclideanSubspaceArrayEquiv (U j)).symm
    (fun _ : Unit => eval w (restrictCoefficients (U j) (p j) (hm j)))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPhasePairFunctionalBounds
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module _root_.MvPolynomial PolynomialTranslationLie

noncomputable def constantCoefficient (s : ℕ) : weightedSubalgebra weight s →ₗ[ℚ] ℚ where
  toFun x := x.val.polynomial.coeff 0
  map_add' x y := by change (x.val.polynomial + y.val.polynomial).coeff 0 = _; simp
  map_smul' r x := by change (r • x.val.polynomial).coeff 0 = _; simp

@[simp] theorem constantCoefficient_apply (s : ℕ) (x : weightedSubalgebra weight s) :
    constantCoefficient s x = x.val.polynomial.coeff 0 := rfl

@[simp] theorem constantCoefficient_centralRationalElement (s : ℕ) (hs : 0 < s) (q : ℚ) :
    constantCoefficient s (centralRationalElement weight s hs q) = q := by
  change (C q : MvPolynomial (Fin 0) ℚ).coeff 0 = q
  simp

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3
open scoped TensorProduct BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

structure UniversalLocalMajorSliceTest (N : I → ℕ) (degree : ℕ)
    (cost budget : ℝ) where
  stride : ℕ
  stride_pos : 0 < stride
  slice : ResidueBoxSlice N stride
  dense : IsDenseCommonStrideBox N cost slice.integerPoints
  value : (I → ℤ) → ℂ
  native : Nonempty (NativeSampleModel (fun _ : I => 1) degree budget id value)

namespace UniversalLocalMajorSliceTest

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {N : I → ℕ} {degree : ℕ} {cost budget : ℝ}

noncomputable def weight (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) : ℂ :=
  star (packet.value
    (commonStrideIndex (fun i => (packet.slice.start i : ℤ)) packet.stride x))

end UniversalLocalMajorSliceTest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineEpochTransition
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

noncomputable def FixedAffineEpochTransition
    {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ)
    (V : RationalFilteredNilmanifold K t e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (work cost : ℝ) (P C B : ℕ) : Prop :=
  ∀ p : ℝ, 0 ≤ p → p ≤ work → ∀ (r : ℤ) (h : σ → ℤ) (A' : σ → ℝ),
    (∀ i, 0 < A' i) → (∀ i, |(h i : ℝ)| ≤ A i) →
    (∀ i, |(r : ℝ)| * A' i ≤ A i) →
    ∀ S : D.Niltest (fun _ : σ => 1),
      S.orbit = D.filtration.realification.scalarAffineOrbitHom (r : ℚ)
        (fun i => (h i : ℚ)) T.orbit →
      S.UnitIntervalValued → S.ComplexityLE p →
      ∀ q rho : ℝ, p ≤ q → (Fintype.card σ : ℝ) ≤ q →
        verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
        ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ), 0 < M →
          ∀ (u v : σ → ℤ) (J : σ → ℕ), (∀ i, 0 < J i) →
          (∀ i, v i ≡ u i [ZMOD (M : ℤ)]) →
          (∀ i, (M * (M * P)).Coprime (J i)) →
          (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ)) →
          ∀ Δ ε δ : ℝ, 0 < δ → δ ≤ 1 → ε < 1 / 2 →
          2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤ Δ / 2 →
          8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) ≤ Δ / 4 →
          (∀ i, 8 ≤ δ * (N i : ℝ)) →
          (∀ i, (u i : ℝ) - (M : ℝ) * A' i ≤ (lo i : ℝ) ∧
            (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A' i) →
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8 →
          Δ ≤ ‖residuePairMean S.eval lo N M u v J false - residuePairMean S.eval lo N M u v J true‖ →
          ResiduePairDimensionDrop D ω hF S W lo N M u v J ((q + B) ^ B) ∨
          AnchoredChildResidueComparison V
            (V.filtration.realification.scalarAffineOrbitHom (r : ℚ) (fun i => (h i : ℚ)) child)
            cost (Δ / 4) δ lo N M P u v J

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedDenseFiberSliceForecastGeometry
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

theorem denseCoordinate_geometry {X : Type*} {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice N q) (i : X) {cost : ℝ}
    (hq : 0 < q) (hN : 0 < N i)
    (hdense : Real.exp (-cost) * (N i : ℝ) ≤ S.length i)
    (hfloor : 2 ≤ Real.exp (-cost) * (N i : ℝ)) :
    2 ≤ S.length i ∧
      0 ≤ (S.start i : ℝ) / N i ∧
      Real.exp (-cost) / 2 ≤ (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i ∧
      (S.start i : ℝ) / N i +
        (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i < 1 ∧
      (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i ≤ 1 ∧
      (q : ℝ) ≤ 2 * Real.exp cost := by
  have hlenR : (2 : ℝ) ≤ S.length i := hfloor.trans hdense
  have hlen : 2 ≤ S.length i := by exact_mod_cast hlenR
  have hinside (t : Fin (S.length i)) :
      0 ≤ (S.start i : ℤ) + (q : ℤ) * (t.val : ℤ) ∧
      (S.start i : ℤ) + (q : ℤ) * (t.val : ℤ) < N i := by
    constructor
    · positivity
    · exact_mod_cast S.inside i t.val t.isLt
  have hbounds := affineInterval_normalized_bounds hN hlen hq hinside
  have hNR : (0 : ℝ) < N i := by exact_mod_cast hN
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsub : ((S.length i - 1 : ℕ) : ℝ) = (S.length i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hhalf : Real.exp (-cost) * (N i : ℝ) / 2 ≤
      ((S.length i - 1 : ℕ) : ℝ) := by
    rw [hsub]
    linarith
  have hscaled : (q : ℝ) * Real.exp (-cost) / 2 ≤
      (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i := by
    apply (le_div_iff₀ hNR).mpr
    have h := mul_le_mul_of_nonneg_left hhalf hq0
    nlinarith
  have hwidth : Real.exp (-cost) / 2 ≤
      (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) / N i := by
    calc
      Real.exp (-cost) / 2 ≤ (q : ℝ) * Real.exp (-cost) / 2 := by
        nlinarith [Real.exp_pos (-cost)]
      _ ≤ _ := hscaled
  have hprod : (q : ℝ) * Real.exp (-cost) ≤ 2 := by
    linarith [hscaled.trans hbounds.2.2.2]
  have hcancel : Real.exp (-cost) * Real.exp cost = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hstep : (q : ℝ) ≤ 2 * Real.exp cost := by
    calc
      (q : ℝ) = ((q : ℝ) * Real.exp (-cost)) * Real.exp cost := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod (Real.exp_pos cost).le
  exact ⟨hlen, by simpa only [Int.cast_natCast] using hbounds.1, hwidth,
    by simpa only [Int.cast_natCast] using hbounds.2.2.1, hbounds.2.2.2, hstep⟩

theorem fiberParameter_dense_geometry {X : Type*} {keep : X → Prop}
    [DecidablePred keep] {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ) (i : X) (hi : keep i) {cost : ℝ}
    (hq : 0 < q) (hN : 0 < N i)
    (hdense : Real.exp (-cost) * (N i : ℝ) ≤ S.length ⟨i, hi⟩)
    (hfloor : 2 ≤ Real.exp (-cost) * (N i : ℝ)) :
    let lower := (S.fiberParameterStart fixed i : ℝ) / N i
    let width := (fiberParameterStride (keep := keep) (q := q) i : ℝ) *
      ((S.fiberParameterLength i - 1 : ℕ) : ℝ) / N i
    2 ≤ S.fiberParameterLength i ∧ 0 ≤ lower ∧
      Real.exp (-cost) / 2 ≤ width ∧ lower + width < 1 ∧
      |lower| + |width| ≤ 1 := by
  dsimp only
  simp only [fiberParameterLength, fiberParameterStart, fiberParameterStride,
    dif_pos hi, if_pos hi, Int.cast_natCast]
  have h := S.denseCoordinate_geometry ⟨i, hi⟩ hq hN hdense hfloor
  have hw : 0 ≤ (q : ℝ) * ((S.length ⟨i, hi⟩ - 1 : ℕ) : ℝ) / N i :=
    (by positivity : (0 : ℝ) ≤ Real.exp (-cost) / 2).trans h.2.2.1
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  rw [abs_of_nonneg h.2.1, abs_of_nonneg hw]
  exact h.2.2.2.1.le

end Erdos3.ResidueBoxSlice

end

end OAI
end


