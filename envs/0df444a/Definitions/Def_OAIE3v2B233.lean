-- Prove2me | Definitions.Def_OAIE3v2B233
-- name    : OAIE3v2B233
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:36:55.100663+00:00
-- url     : https://prove2.me/theorems/8770700c-0e83-4429-b761-7102f153fce1
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 238 of 311
-- statement:
--   Definitions bundle 238 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B204`, `OAIE3v2B205`, `OAIE3v2B206`, `OAIE3v2B208`, `OAIE3v2B212`, `OAIE3v2B213`, `OAIE3v2B214` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidateCoveredBudget.lean`, `Dynamics/NormalizedTwistNativeApproximationBudget.lean`, `Estimates/AdaptedDiagramNativeExternalNet.lean`, `Estimates/AllocatedAnchoredRecoveredSource.lean`, `Estimates/AllocatedExternalCandidateOptionJointConclusion.lean`, `Estimates/AllocatedFrozenTaggedTwistStepDrop.lean`, `Estimates/AllocatedRowsAmbientProjectedFamilyMultiple.lean`, `Estimates/FullTaggedRationalRetraction.lean`, `Estimates/NativeProductVerticalization.lean`, `Estimates/UnitVerticalNativeInverseModels.lean`, `Fourier/AllocatedRecoveredTagTorusVariation.lean`, `Geometry/CertifiedFullChartFrozenTerminal.lean`, `Geometry/NarrowSpatialSiteVariation.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Lattices/AllocatedModularRankAffineProbability.lean`, `Lattices/CertifiedAffineCutoffCost.lean`, `Linear/AllocatedCenteredMeasurableFramedBadTail.lean`, `Linear/AllocatedOriginalDensityProjectionLaw.lean`, `Linear/AllocatedOriginalSourceProjection.lean`, `Linear/SpatialFrameSlopeBudget.lean`, `Polynomial/FullTaggedProjectionPolynomial.lean`, `Sampling/ForecastLawRecoveredRationalCardinalityCap.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B204
import Definitions.Def_OAIE3v2B205
import Definitions.Def_OAIE3v2B206
import Definitions.Def_OAIE3v2B208
import Definitions.Def_OAIE3v2B212
import Definitions.Def_OAIE3v2B213
import Definitions.Def_OAIE3v2B214

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup

theorem exists_native_middle_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
      {g : (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra R.subalgebra)
          s (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra R.subalgebra)),
        E.filtration = D.filtration.gradedRefiltration R.subalgebra ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration R.subalgebra).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (E.basis i : L) j) ≤ (p + C) ^ C) ∧
        ∃ h : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
          ∀ x : σ → ℤ,
            realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot)
              (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
              (E.filtration.realification.polynomialOrbitEval (fun _ => 1) x h) =
                D.filtration.adaptedPolynomialRealValueHom
                  (fun _ : σ => 1) (fun i => (x i : ℝ)) R.middle := by
  obtain ⟨C, hC, hmodel⟩ := exists_controlled_adapted_refiltration_model
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ s d D g eta A p R hp hD
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hmodel D R.basis R.weight R.adapted R.subalgebra
    R.generator R.spanning hp hD hdim R.basis_height R.generator_height
  refine ⟨E, hEF, hEL, hE, hinc, ?_⟩
  exact D.filtration.exists_model_refiltered_polynomial R.subalgebra E hEF
    (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) R.middle
    R.middle_coefficients R.middle_zero

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductVerticalization
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_native_vertical_derivative_models :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ},
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → (B : NativeCommonDerivativeModels s N p f) →
      (∀ h, B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
        (B.test h).orbit = 1) →
      ∃ R : NativeCommonDerivativeModels s N ((p + C) ^ C) f,
        Nonempty (NativeVerticalDerivativeData R) := by
  obtain ⟨a, _, hvertical⟩ := RationalFilteredNilmanifold.exists_common_vertical_correlators
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro s N _ p f hp hf B hnormalized
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨H, S, eta, _, hH, hdense, hheight, hS, hsame, hvert, hint, hcorr⟩ :=
    hvertical B.model B.test B.shifts B.nonempty hp (fun h _ => B.complexity h)
      (fun h _ => B.norm h) B.common_observable (fun h x => multiplicativeDerivative f h x)
      (fun h _ x => multiplicativeDerivative_norm_le_one f hf h x) B.correlation
  have hfinaldensity : Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + (p + a) ^ a)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)
      _ = Real.exp (-((p + a) ^ a)) * (Real.exp (-p) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((p + a) ^ a)) * B.shifts.card :=
        mul_le_mul_of_nonneg_left B.density (Real.exp_nonneg _)
      _ ≤ _ := hdense
  let R : NativeCommonDerivativeModels s N ((p + C) ^ C) f := {
    L := B.L
    dim := B.dim
    model := B.model
    geometry := B.geometry.mono B.model hpC
    shifts := H
    nonempty := hH
    density := hfinaldensity
    test := S
    norm := fun h => (hS h).2.1
    complexity := fun h => (hS h).2.2.mono hqC
    common_observable := hsame
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh) }
  refine ⟨R, ⟨{
    normalized := ?_
    frequency := eta
    height := fun i => (hheight i).trans hqC
    vertical := hvert
    integral := hint }⟩⟩
  intro h
  change B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 (S h).orbit = 1
  rw [(hS h).1]
  exact hnormalized h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTwistNativeApproximationBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_native_approximation_with_budget
    {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ)
    {u p budget K C : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ budget)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ t, ‖signal t‖ ≤ 1) →
      (∀ t, t ∉ integerBox N → signal t = 0) →
      allocatedModelUnitThreshold u p K C ≤ sampledSliceSeminorm μ site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree budget (fun t : integerBox N => t.val) G) ∧
        Real.exp (-budget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun t => signal t.val)
            (fun t => star (W.eval N poly t.val) * G t)‖)
    {Ptail : ℝ} (hPtail : u + 2 * p + budget + 30 ≤ Ptail)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (μ.siteLaw physical) C ≤
        6 * positiveProjectionAccuracy Ptail)
    (input : integerBox N → ℂ) (hinput : ∀ t, ‖input t‖ ≤ Real.exp p) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (Q : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree budget
        (fun t : integerBox N => t.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (t : integerBox N) => W.eval N poly t.val)) ∧
      input = (∑ i, coeff i • Q i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
      sampledSliceSeminorm μ physical slices tests err ≤ Real.exp (-u) ∧
      (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * p + 30) := by
  obtain ⟨nterms, hnterms, Q, coeff, err, hQ, heq, hcoeff, herr, hterms⟩ :=
    exists_normalizedTwist_native_approximation N poly μ physical site hphysical slices tests
      w degree budget hK hC (Real.exp_pos p) (Real.exp_pos (-budget))
      (Real.exp_pos (-(u + 3))) hsize htests hdetect hexcess input hinput
  have hbounds := allocatedModel_size_bounds hu hp hbudget hK hC hKp hCp
  refine ⟨nterms, hnterms, Q, coeff, err, hQ, heq, hcoeff.trans hbounds.1,
    herr.trans ?_, hterms.trans hbounds.2⟩
  exact allocated_native_approximation_error hu hp hbudget hK (Real.exp_nonneg p)
    hKp le_rfl le_rfl hPtail le_rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_native_unit_vertical_data (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (B : NativeCommonDerivativeModels s N p f) (V : NativeVerticalDerivativeData B),
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeUnitVerticalData B V ((p + C) ^ C)) := by
  obtain ⟨C, hC, hcomplete⟩ := RationalFilteredNilmanifold.exists_native_unit_vertical_completion s
  refine ⟨C, hC, ?_⟩
  intro N _ p f B V hp hf
  obtain ⟨y, hy⟩ := B.exists_large_common_observable hf
  obtain ⟨n, _, hn, K, hK, v, hv0, hvunit, hvnorm, hvLip, hvvertical⟩ :=
    hcomplete B.model (B.test 0) hp (B.complexity 0) (B.norm 0) V.frequency
      (V.vertical 0) y hy
  refine ⟨{
    tailDim := n
    dimension := hn
    observable := v
    lipBound := K
    lip_bound := hK
    unit := hvunit
    norm := hvnorm
    lipschitz := hvLip
    scalar := ?_
    vertical := hvvertical
  }⟩
  intro h x
  rw [hv0, B.common_observable 0 h]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedOriginalSourceProjection
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators

theorem exists_allocated_narrow_density_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S))
    {X : Type*} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    {F : Type*} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P)
    (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ ε : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : ε⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (density : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ)
    (D : ℕ) (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ v, ‖(density v : ℂ) - coefficientTorusFourierSum U frequency coeff v‖ ≤ η)
    {Z : ℝ} (_hZnorm : 0 < Z),
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let pa := fun j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    ∀ (_hpositive : ∀ z : Option (LayerSamplerVariables G I n B) × X → ℤ,
      ‖affineCubeFourierProjection U root dirs frequency pa coeff (fun k d => (z (k, d) : ℝ)) -
        (f (euclideanCoefficientJetMap U root dirs
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
          (affineCoefficientCoverSample U pa hma D (fun k d => (z (k, d) : ℝ)))) : ℂ)‖ ≤ η),
    ∃ (hV : ∀ z, 0 < V z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) *
          (density (affineSampleCoefficientTorus U pa hma (fun k d => (z (k, d) : ℝ))) : ℂ))) / (Z : ℂ) -
        (∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
          physicalCubePositiveTest U D p hm f test (physicalCubeRootDifferences root dirs base z)) /
          (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
  obtain ⟨A₀, _, hprojection⟩ := exists_affine_cube_fourier_projection m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((8 * Polynomial.X + Polynomial.C (q + 130 + A₀)) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ _ J _ U basis R σ S c x P W hP hK hW hroot hWP hL M hperiod y
    X _ _ hX hdim F _ frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
    τ ξ ε hτ hτP hξ hξ1 hξP hε hεP N hsize rank hrank hRank test htest T hT density D f η hη happrox Z hZnorm
    V root dirs pa hma hpositive
  let Q := spatialSamplingBudget (2 * P) + (q + 2 : ℕ)
  have hP2 : 0 ≤ 2 * P := by positivity
  have hPQ : P ≤ Q := by dsimp [Q, spatialSamplingBudget]; linarith [Nat.cast_nonneg (α := ℝ) (q + 2)]
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hsiteQ : P + (q + 2 : ℕ) ≤ Q := by dsimp [Q, spatialSamplingBudget]; linarith
  have heval : Q + A₀ = 8 * P + (q + 130 + A₀ : ℕ) := by
    dsimp [Q, spatialSamplingBudget]
    push_cast
    ring
  have hcost : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    rw [heval]
    simpa [Polynomial.eval₂_pow] using hbudget P hP
  have hExp := Real.exp_le_exp.mpr hPQ
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  have hlin : LinearIndependent ℝ (fun i k => (dirs i k : ℝ)) :=
    linearIndependent_of_fixed_kernel_period (scalarCubeDifferenceMatrix x) dirs Sum.inl
      (fun _ _ => rfl) (by exact_mod_cast ha.ne') hperiod
  have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa j) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have hra (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa j) :=
    (hasLayerSamplingRank_translate_iff (fun d => (base d : ℝ)) (j.val + 1)
      (fun d => (N d : ℝ)) rank (U j) (p j) (hp j)).mpr (hrank j)
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hV : ∀ z, 0 < V z := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
  have hξτ : 0 < ξ * τ := mul_pos hξ hτ
  have hξτP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← two_mul]
  have hρP : 1 / spatialWidthFraction (2 * P) (ξ * τ) ≤ Real.exp Q :=
    (spatialWidthFraction_inv_le hP2 hξτ hξτP).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  have hwidth (z) : spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ V z :=
    (spatialWidthFraction_le_allocated_width hP2 hW
      (hWP.trans (Real.exp_le_exp.mpr (by linarith))) hξτ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  obtain ⟨hZ, hraw⟩ := hprojection hQ (hX.trans hPQ) (hdim.trans hPQ) U root dirs hlin
    (Real.exp_nonneg Q) (Real.exp_nonneg Q) le_rfl le_rfl
    (fun s k => (allocatedPhysicalCube_site_le_exp B U basis S c x y (hroot.trans hWP) hL s k).trans
      (Real.exp_le_exp.mpr hsiteQ)) frequency (fun a j d hd t => (hfrequency a j d hd t).trans hExp)
    coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans hExp) pa hpa hma stride hs
    (Real.exp_nonneg Q) le_rfl (spatialWidthFraction_pos (2 * P) hξτ) hε hρP
    (by simpa only [one_div] using hεP.trans hExp) (fun d => (hsP d).trans hExp)
    (fun d => (N d : ℝ)) (fun d => (Real.exp_le_exp.mpr hcost).trans (hsize d)) hra
    ((Real.exp_le_exp.mpr hcost).trans hRank) 0 (by simp)
    (fun s u => test s ((fun d => (base d : ℝ)) + u)) (fun s u => htest s _)
    T hT V hV hwidth
  have hweight (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      layeredSiteWeight 0 (fun s => affineSite root dirs s)
        (fun s u => test s ((fun d => (base d : ℝ)) + u)) (fun k d => (z (k, d) : ℝ)) =
        physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) :=
    layeredSiteWeight_physicalCube root dirs base test z
  have hdirs : Matrix.of dirs = dirs := rfl
  have hfirst := selectedResidue_positive_density_projection_error U root dirs D p hp hm
    frequency coeff test htest base stride T V hV hZ density f hη happrox hpositive
    (by simpa only [hweight, hdirs, pa] using hraw)
  refine ⟨hV, hZ, ?_⟩
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZnorm]
  exact div_le_div_of_nonneg_right hfirst hZnorm.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

universe uX uF

theorem exists_allocated_mixture_density_projection_law (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    {F : Type uF} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P)
    (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ ε : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : ε⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (density : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, uF} U
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y))
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ v, ‖(density v : ℂ) - coefficientTorusFourierSum U frequency coeff v‖ ≤ η)
    {Z : ℝ} (_hZnorm : 0 < Z),
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hV : ∀ z, 0 < V z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let source := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T V hV hmass z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z) *
          (density (affineSampleCoefficientTorus U
            (fun j => translate (fun t => (base t : ℝ)) (p j))
            (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
            (fun k t => (z (k, t) : ℝ))) : ℂ))
    let projected := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T V hV hmass z).toReal : ℂ) *
        physicalCubePositiveTest U D p hm (f y) test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z)
    ‖law.complexMean source / (Z : ℂ) - law.complexMean projected / (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_narrow_density_projection m q
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U basis R σ S c x P W hP hK hW hroot hWP hL M hperiod
    X _ _ hX hdim F _ frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
    τ ξ ε hτ hτP hξ hξ1 hξP hε hεP N hsize rank hrank hRank test htest T hT density D f
    hproject η hη happrox Z hZnorm V hV hmass law source projected
  have hpoint (y) : ‖source y / (Z : ℂ) - projected y / (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
    obtain ⟨_, _, he⟩ := hprojection B U basis S c x hP hK hW hroot hWP hL hperiod y
      hX hdim frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
      hτ hτP hξ hξ1 hξP hε hεP N hsize hrank hRank test htest T hT density D (f y)
      hη happrox hZnorm
      (fun z => (hproject y) frequency coeff
        (fun v => by rw [norm_sub_rev]; exact happrox v)
        (fun j => translate (fun t => (base t : ℝ)) (p j))
        (fun j => degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
        (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
        (fun k t => (z (k, t) : ℝ)))
    exact he
  have hmean := law.norm_complexMean_sub_le
    (fun y => source y / (Z : ℂ)) (fun y => projected y / (Z : ℂ))
    (fun _ => (2 * η + ε) / Z) (fun y _ => hpoint y)
  rw [law.mean_const] at hmean
  simpa only [FiniteProbabilityWeights.complexMean, mul_div_assoc, Finset.sum_div] using hmean

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedOriginalDensityProjectionLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_original_density_projection_law (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P W : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ),
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∀ (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y))
    {Z : ℝ} (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ Real.exp P),
    let widths := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let source := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z) *
          (density (affineSampleCoefficientTorus U
            (fun j => translate (fun t => (base t : ℝ)) (p j))
            (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
            (fun k t => (z (k, t) : ℝ))) : ℂ))
    let projected := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
        physicalCubePositiveTest U D p hm (f y) test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z)
    ‖law.complexMean source / (Z : ℂ) - law.complexMean projected / (Z : ℂ)‖ ≤ Real.exp (-P) := by
  obtain ⟨A₀, _, hprojection⟩ := exists_allocated_mixture_density_projection_law m q
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U basis R σ S c x hb o hR hσ C V hC hV
    hσ1 Cinv hCinv hchart hsmall P W hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ
    hAP hCP hVP M hperiod X _ _ hX hdim p hp hm base stride hs hsP τ ξ hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank test htest T hT D f density hproject Z hZ hZi widths hwidths hmass
    law source projected
  let Q := positiveComparisonDataBudget m q P
  obtain ⟨hQ, hPQ, haccQ, _, _⟩ := positiveComparisonDataBudget_bounds m q hP
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    calc
      _ ≤ ((P + b) ^ b + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀))
          (add_le_add (hbnd P hP) le_rfl) A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV q
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hL hCP hVP
  let _ := inst
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : (positiveProjectionAccuracy P)⁻¹ ≤ Real.exp Q := by
    simp only [positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr haccQ
  have he := hprojection B U basis S c x hQ (hK.trans hPQ) hW hroot
    (hWP.trans hExp) (hL.trans hExp) hperiod (hX.trans hPQ) (hdim.trans hPQ)
    frequency hfreq coeff hcoeff p hp hm base stride hs (fun t => (hsP t).trans hExp)
    hτ (hτP.trans hExp) hξ hξ1 (hξP.trans hExp) hη hηQ N
    (fun t => (Real.exp_le_exp.mpr hcut).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hcut).trans hRank) test htest T hT density D f hproject hη.le happ hZ
    hwidths hmass law
  apply he.trans
  calc
    (2 * positiveProjectionAccuracy P + positiveProjectionAccuracy P) / Z =
        3 * positiveProjectionAccuracy P * Z⁻¹ := by ring
    _ ≤ 3 * positiveProjectionAccuracy P * Real.exp P :=
      mul_le_mul_of_nonneg_left hZi (by positivity)
    _ = 3 * Real.exp (-(P + 4)) := by
      rw [mul_assoc, positiveProjectionAccuracy, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp 4 * Real.exp (-(P + 4)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (-P) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineProbability
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {L : ℕ} {R : Type*}

def allocatedCongruenceAffineCoefficients [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → R)
    (offset c : AllocatedCongruenceCoefficientIndex X E inactive L → R) :
    AllocatedCongruenceCoefficientIndex X E inactive L → R
  | ⟨j,.inl x,l⟩ => offset ⟨j,.inl x,l⟩ + stride x.val * c ⟨j,.inl x,l⟩
  | ⟨j,.inr o,l⟩ => c ⟨j,.inr o,l⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

theorem allocatedActualPrimeBad_eq_rankBad (p a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p a f =
      allocatedCongruenceRankBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
        (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block P C p a
        (allocatedCongruenceIntegerSelectedCoefficients inactive
          (allocatedReadNoise f) (allocatedReadDeck f)
          (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block) := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedAnchoredRecoveredSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)

def AllocatedPhysicalRankReadCertificate
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  ∀ (P : Finset ℕ) (hP : ∀ p : P, NeZero p.val), letI := hP
    ∀ (A : ℕ → ℕ) (M : ℕ) (hM : 0 < M), letI : NeZero M := ⟨hM.ne'⟩
      ∀ hdiv : ∀ p : P, p.val ^ A p.val ∣ M,
        coefficientDeckChartEvent U bW b hb o M
          (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
            (fun v => (z v : ZMod M)))
          (affineCoefficientCoverSample U poly hm M (fun k x => (z (k,x) : ℝ))) ↔
        ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)

def AllocatedCenteredRecoveredSampleReadAt
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j) (a : X → ℤ)
    (sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  ∀ z, allocatedReadNoise (read z) = z ∧
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z ≠ 0 →
      (canonicalCoefficientSample U b hb o (sample z) =
        affineSampleCoefficientTorus U (allocatedCenteredConditionalPolynomial U poly c a)
          (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
          (fun k x => (z (k,x) : ℝ))) ∧
      (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
        mixedArraySupported (allocatedLayerCenters B U b S j)
          (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
      (∀ d, |coefficientSamplerAmbientPoint U b o (sample z) d| < 1/2) ∧
      (∀ (j : Fin m) (i : Fin (n j))
        (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
        allocatedReadProjection (read z) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
      (∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
          coefficientDeckChartEvent U bW b hb o q event
            (affineCoefficientCoverSample U (allocatedCenteredConditionalPolynomial U poly c a)
              (allocatedCenteredConditionalPolynomial_mem U poly hm c a) q
              (fun k x => (z (k,x) : ℝ))) ↔
          event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) ∧
      AllocatedPhysicalRankReadCertificate B U bW b hb o
        (allocatedCenteredConditionalPolynomial U poly c a)
        (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
        inactive spatial kernel block C z (read z))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

section RecoveredSample
variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {c : ∀ j, U j} {a : X → ℤ}
variable {sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I E n B → ℤ}

theorem AllocatedCenteredRecoveredSampleReadAt.jointFrame
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedReadNoise (allocatedJointFrameRead a (read z)) =
        (fun t => jointIntegerFrame (a,z) t.1 t.2) ∧
    allocatedReadDeck (allocatedJointFrameRead a (read z)) = allocatedReadDeck (read z) ∧
    allocatedReadProjection (allocatedJointFrameRead a (read z)) = allocatedReadProjection (read z) ∧
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z ≠ 0 →
      canonicalCoefficientSample U b hb o (sample z) =
        affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (poly j))
          (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j))
          (fun k x => (jointIntegerFrame (a,z) k x : ℝ)) ∧
      (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
        mixedArraySupported (allocatedLayerCenters B U b S j)
          (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
      (∀ d, |coefficientSamplerAmbientPoint U b o (sample z) d| < 1/2) ∧
      (∀ (j : Fin m) (i : Fin (n j))
        (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
        allocatedReadProjection (allocatedJointFrameRead a (read z)) ⟨j, Sum.inr i⟩ e =
          (sample z j).2 i e)) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · rw [allocatedJointFrameRead_noise, (h z).1]
  · intro hz
    have hs := (h z).2 hz
    refine ⟨?_, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
    exact hs.1.trans (affineSampleCoefficientTorus_joint_frame U
      (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j)) a z)

end RecoveredSample
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedParameterBox_coordinate_bound (t : integerBox sides)
    (k : LayerSamplerVariables G I n B) : |(t.val k : ℝ)| ≤ S.value := by
  have ht := (mem_integerBox sides t.val).mp t.property k
  have hside : sides k ≤ S.value := by
    cases k with
    | inl g => exact le_rfl
    | inr j => exact allocatedPrincipalSides_le_scale B U b S j
  have ht0 : (0 : ℝ) ≤ t.val k := by exact_mod_cast ht.1
  rw [abs_of_nonneg ht0]
  exact (by exact_mod_cast ht.2.le : (t.val k : ℝ) ≤ sides k).trans (Nat.cast_le.mpr hside)

theorem allocatedParameterBox_root_bound (t : integerBox sides) :
    (∑ k, |(t.val k : ℝ)|) ≤ allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
    allocatedParameterBox_coordinate_bound B U b S t k)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, mul_zero, zero_add] using hsum

theorem allocatedParameterBox_slice_cost {p : ℝ} {A : Finset (integerBox sides)}
    (hA : IsDenseCommonStrideBox sides p (A.image Subtype.val)) :
    (Fintype.card (integerBox sides) : ℝ) / A.card ≤
      Real.exp (p * Fintype.card (LayerSamplerVariables G I n B)) := by
  exact dense_commonStride_slice_card_ratio Subtype.val Subtype.val_injective
    (by ext t; simp) hA

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem slice_index (j : ∀ i, Fin (C.slice.length i)) :
    commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step (C.slice.integerPoint j) =
      fun i => ((j i).val : ℤ) :=
  C.slice.commonStrideIndex_integerPoint C.step_pos j

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem slice_length_gt_of_dense_side
    {densityCost : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      densityCost C.slice.integerPoints)
    (degree : ℕ)
    (hside : ∀ i : C.Variables,
      Real.exp densityCost * ((degree + 1 : ℕ) : ℝ) ≤ (A.sides i.val : ℝ))
    (i : C.Variables) : degree < C.slice.length i :=
  C.slice.length_gt_of_dense_exp_side C.step_pos hdense degree i (hside i)

theorem slice_length_gt_of_dense_cutoff
    {densityCost cutoff : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      densityCost C.slice.integerPoints)
    (degree : ℕ)
    (hcutoff : Real.exp densityCost * ((degree + 1 : ℕ) : ℝ) ≤ cutoff)
    (hside : ∀ i, C.keep i → cutoff ≤ layerSamplerBox B U b S i)
    (i : C.Variables) : degree < C.slice.length i := by
  apply C.slice_length_gt_of_dense_side hdense degree _ i
  intro a
  exact (hcutoff.trans (hside a.val a.property)).trans_eq
    (allocatedParameterBox_side_eq B U b S a.val)

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedRecoveredTagTorusVariation
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {X : Type*} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem physicalGridFactorInput_dist_le_of_integer_remainders
    (q : ℕ) (hq : 0 < q) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (u v : X → ℝ) (center r₀ r₁ : ∀ j, J j → ℝ) (z₀ z₁ : ∀ j, J j → ℤ)
    (hu : ∀ j i, eval u (poly j) i = center j i + r₀ j i + (z₀ j i : ℝ))
    (hv : ∀ j i, eval v (poly j) i = center j i + r₁ j i + (z₁ j i : ℝ))
    (hz : ∀ j i, (((z₀ j i : ℝ) / q : ℝ) : UnitAddCircle) =
      (((z₁ j i : ℝ) / q : ℝ) : UnitAddCircle))
    {ε : ℝ} (hε : 0 ≤ ε) (herr : ∀ j i, |r₀ j i - r₁ j i| ≤ ε) :
    dist (physicalGridFactorInput q poly u) (physicalGridFactorInput q poly v) ≤ ε / q := by
  apply (dist_pi_le_iff (div_nonneg hε (Nat.cast_nonneg q))).mpr
  intro z
  change dist (((eval u (poly z.1) z.2 / q : ℝ) : UnitAddCircle))
    (((eval v (poly z.1) z.2 / q : ℝ) : UnitAddCircle)) ≤ _
  rw [hu, hv]
  exact (unitCircle_dist_div_integer_parts hq _ _ _ _ _ (hz z.1 z.2)).trans
    (div_le_div_of_nonneg_right (herr z.1 z.2) (Nat.cast_nonneg q))

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialFrameSlopeBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {G J X : Type*} [Fintype G] [Fintype J] [Fintype X]

theorem narrowSpatial_frame_normalized_slope_sum
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (T : G ⊕ J → ℝ) (hT : ∀ k, 0 ≤ T k) (hsum : ∑ k, T k ≤ W)
    (v : Option (G ⊕ J) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (x : X) :
    (∑ k, |(v (some k, x) : ℝ) / (N x : ℝ)| * T k) ≤ τ / 8 := by
  have hn : (0 : ℝ) < N x := by exact_mod_cast hN x
  have h := narrowSpatial_frame_slope_sum hW hτ hξ N hN T hT hsum v hv x
  have hd : (∑ k, |(v (some k, x) : ℝ)| * T k) / (N x : ℝ) ≤ τ / 8 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  calc
    _ = (∑ k, |(v (some k, x) : ℝ)| * T k) / (N x : ℝ) := by
      simp only [abs_div, abs_of_pos hn, div_mul_eq_mul_div, Finset.sum_div]
    _ ≤ τ / 8 := hd

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NarrowSpatialSiteVariation
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

theorem narrowSpatial_jointPhysicalSite_normalized_dist
    {G J X : Type*} [Fintype G] [Fintype J] [Fintype X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (T : G ⊕ J → ℝ) (hT : ∀ k, 0 ≤ T k) (hsum : ∑ k, T k ≤ W)
    (a : X → ℤ) (frame : Option (G ⊕ J) × X → ℤ)
    (hframe : frame ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (u v : G ⊕ J → ℤ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcell : ∀ k, |(u k : ℝ) - (v k : ℝ)| ≤ T k * δ) :
    dist (fun x => (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x)
      (fun x => (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x) ≤ τ * δ / 8 := by
  have h := jointIntegerPhysicalSite_normalized_dist_of_slope_sum N T a frame u v
    (by positivity : 0 ≤ τ / 8) hδ
    (narrowSpatial_frame_normalized_slope_sum hW hτ hξ N hN T hT hsum frame hframe) hcell
  simpa only [div_mul_eq_mul_div] using h

theorem narrowSpatial_jointPhysicalSite_normalized_dist_le_cell
    {G J X : Type*} [Fintype G] [Fintype J] [Fintype X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (T : G ⊕ J → ℝ) (hT : ∀ k, 0 ≤ T k) (hsum : ∑ k, T k ≤ W)
    (a : X → ℤ) (frame : Option (G ⊕ J) × X → ℤ)
    (hframe : frame ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (u v : G ⊕ J → ℤ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcell : ∀ k, |(u k : ℝ) - (v k : ℝ)| ≤ T k * δ) :
    dist (fun x => (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x)
      (fun x => (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x) ≤ δ := by
  apply (narrowSpatial_jointPhysicalSite_normalized_dist hW hτ hξ N hN T hT hsum
    a frame hframe u v hδ hcell).trans
  have h := mul_le_mul_of_nonneg_right hτ1 hδ
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenTaggedTwistStepDrop
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

theorem allocatedLayerSupported_polynomial_variation
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (x y : LayerSamplerVariables G I n B → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ k, |x k| ≤ layerSamplerBox B U b S k)
    (hy : ∀ k, |y k| ≤ layerSamplerBox B U b S k)
    (hxy : ∀ k, |x k - y k| ≤ layerSamplerBox B U b S k * δ) (i : J j) :
    |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x i -
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 y i| ≤
      (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) * δ := by
  rw [← mixedLiftPolynomial_eval, ← mixedLiftPolynomial_eval]
  apply abs_eval_sub_eval_normalized_mass_bound _ _
    (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)) x y
    (allocatedLayerSupported_normalized_mass_uniform B U b o hR hσ S hσ1 C hC hchart
      hsmall j a ha i) hδ hx hy hxy
  exact (mixedLiftPolynomial_degree (euclideanSubspace (U j)) (b j) (o j) Subtype.val
    a (fun d => d.property) i).trans (by omega)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist
open scoped NNReal

variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem eval_sub_eval_of_component_dist
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (u v : X → ℤ) {ε : ℝ}
    (hres : (fun i => (u i : ZMod W.modulus)) = (fun i => (v i : ZMod W.modulus)))
    (hspatial : dist (fun i => (u i : ℝ) / N i) (fun i => (v i : ℝ) / N i) ≤ ε)
    (htag : dist (physicalGridFactorInput W.cover poly (fun i => (u i : ℝ)))
      (physicalGridFactorInput W.cover poly (fun i => (v i : ℝ))) ≤ ε) :
    ‖W.eval N poly u - W.eval N poly v‖ ≤ (L : ℝ) * ε := by
  have hdist := W.smooth_lipschitz.dist_le_mul
    (fun i => (u i : ℝ) / N i, physicalGridFactorInput W.cover poly (fun i => (u i : ℝ)))
    (fun i => (v i : ℝ) / N i, physicalGridFactorInput W.cover poly (fun i => (v i : ℝ)))
  have hbound : ‖W.smooth (fun i => (u i : ℝ) / N i,
      physicalGridFactorInput W.cover poly (fun i => (u i : ℝ))) -
      W.smooth (fun i => (v i : ℝ) / N i,
      physicalGridFactorInput W.cover poly (fun i => (v i : ℝ)))‖ ≤ (L : ℝ) * ε := by
    rw [dist_eq_norm, Prod.dist_eq] at hdist
    exact hdist.trans (mul_le_mul_of_nonneg_left (max_le hspatial htag) L.coe_nonneg)
  simp only [eval, hres, ← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_right (W.mask_bound _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hbound)

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateCoveredBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem finiteFreezing_initial_score_surplus
    {Bweight Bobs Lip p scoreThreshold : ℝ} (hp : 0 ≤ p)
    (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : Bweight ≤ Real.exp p) (hobs : Bobs ≤ Real.exp p)
    (hlip : Lip ≤ Real.exp p) (hscore : Real.exp (-p) ≤ scoreThreshold) :
    Real.exp (-p) / 2 + Bweight * (Lip * finiteFreezingInitialPrecision p) +
      (Bweight * Bobs) * finiteFreezingInitialDiscard p < scoreThreshold := by
  apply finiteFreezing_exp_score_surplus hBobs hLip hweight hobs hlip
  · have h := finiteFreezing_initial_precision_exponent hp
    linarith
  · have h := finiteFreezing_initial_discard_exponent hp
    linarith
  · exact hscore

theorem finiteFreezing_uniform_recursive_budget (k : ℕ)
    {p cost densityCost mass a b : ℝ} (hp : 0 ≤ p) {C : ℕ} (hC : 2 ≤ C)
    (hcost : cost ≤ (p + C) ^ C) (hdensity : densityCost ≤ (p + C) ^ C)
    (hb0 : 0 ≤ b) (hb : b ≤ (p + C) ^ C) (hk : (k : ℝ) ≤ (p + C) ^ C)
    (ha : a ≤ (p + C) ^ C) (hmass : Real.exp (-a) ≤ mass) :
    max cost (densityCost + Real.log
      ((4 * Real.exp b * max 1 (Real.exp b) * (k + 1 : ℝ)) /
        finiteFreezingInitialDiscard p)) ≤ finiteFreezingRecursiveParameter C p ∧
      Real.exp (-finiteFreezingRecursiveParameter C p) ≤ mass / (Real.exp b) ^ 2 ∧
      Real.exp (-finiteFreezingRecursiveParameter C p) ≤ Real.exp (-p) / 2 := by
  obtain ⟨hcostRec, hmassRec, hscoreRec⟩ :=
    finiteFreezing_uniform_recursive_exponents k hp hC hb hk ha
  refine ⟨?_, finiteFreezing_exp_recursive_mass_le hmass hmassRec,
    finiteFreezing_exp_half_score_le hscoreRec⟩
  exact (finiteFreezing_exp_cost_le k hcost hdensity hb0 (by linarith : 0 ≤ 4 * p + 8)).trans
    hcostRec

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRowsAmbientProjectedFamilyMultiple
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_rows_ambient_projected_family_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μrows : Measure (CoefficientTorus (K := Fin q) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    let Row := fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}
    let Tuple := PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S)
    ∃ g : Tuple → EuclideanJetLayers U Row → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧
      (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S c x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : Row j → Finset (Fin q)))) = realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection U (allocatedPhysicalCubeRoot B U b S c x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density
        (fun z => g y ((physicalRowsStandardEquiv U).symm z))) ∧
      (∀ y, ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
        LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
        (∀ z, ‖F z‖ ≤ cap) ∧
        ∀ z, (g y z : ℂ) = F (coveredJetAmbientTorus U 1 z)) ∧
      ∀ law : FiniteProbabilityWeights Tuple,
        ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
          LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
          (∀ z, ‖F z‖ ≤ cap) ∧
          ∀ z, law.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z) := by
  obtain ⟨A, hA, hcover⟩ := exists_allocated_ambient_projected_density_multiple m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hcover⟩ := hcover B U b S c x hP hG hc hL hperiod period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    _ _ _ μrows _ _ density cap cover ξ densityLip sectionLip reconstructionLip Row Tuple
  have hex (y : Tuple) := hcover y hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  choose g F hgc hgb hgi hgm hglaw hprojection hFb hFl hvalue using hex
  let rowG := fun (y : Tuple) (z : EuclideanJetLayers U Row) => g y (physicalRowsToStandard U z)
  have hpres := physicalRowsToStandard_measurePreserving U μrows ν
  refine ⟨rowG, fun y => (hgc y).comp (physicalRowsToStandard_continuous U),
    fun y z => hgb y _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    convert hpres.integrable_comp_of_integrable (hgi y) using 1
    congr! (transparency := .reducible)
    dsimp only [ξ]
    congr! (transparency := .reducible)
  · intro y
    have he := hpres.integral_comp (physicalRowsStandardEquiv U).measurableEmbedding (g y)
    convert he.trans (hgm y) using 1
    congr! (transparency := .reducible)
  · intro y
    exact physicalRows_projected_density_law U μrows ν _ _ _ (g y) (hglaw y)
  · intro y
    exact hprojection y
  · intro y
    let pointLaw := FiniteProbabilityWeights.pointWeights y
    obtain ⟨Fmean, hFm, hFmb, hFmv⟩ := exists_physicalRowsProjectedMean_ambient U pointLaw g F
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      hFl (by simpa only [NNReal.coe_pow] using hFb) hvalue
    refine ⟨Fmean, hFm, ?_, ?_⟩
    · simpa only [NNReal.coe_pow] using hFmb
    · intro z
      simpa only [physicalRowsProjectedMean, pointLaw, FiniteProbabilityWeights.pointWeights_complexMean] using hFmv z
  · intro law
    obtain ⟨Fmean, hFm, hFmb, hFmv⟩ := exists_physicalRowsProjectedMean_ambient U law g F
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      hFl (by simpa only [NNReal.coe_pow] using hFb) hvalue
    refine ⟨Fmean, ?_, ?_, hFmv⟩
    · exact hFm
    · simpa only [NNReal.coe_pow] using hFmb

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullTaggedRationalRetraction
namespace OAI

section

namespace Erdos3

variable {T S : Type*} [Fintype T] [Fintype S]

theorem rationalMatrix_real_fixes_coordinateSpan
    (P : Matrix T T ℚ) (W : Submodule ℚ (T → ℚ))
    (hfix : ∀ x ∈ W, P.mulVecLin x = x)
    (x : T → ℝ) (hx : x ∈ realRationalCoordinateSpan W) :
    Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x := by
  have hspan : Submodule.span ℚ (Set.range (fun w : W => (w : T → ℚ))) = W := by
    have he : Set.range (fun w : W => (w : T → ℚ)) = (W : Set (T → ℚ)) := by
      ext y
      simp
    rw [he, Submodule.span_eq]
  rw [← hspan, realRationalCoordinateSpan_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      funext i
      have he := congrArg (fun z : T → ℚ => (z i : ℝ)) (hfix w w.property)
      change (∑ j, (P i j : ℝ) * ((w : T → ℚ) j : ℝ)) = ((w : T → ℚ) i : ℝ)
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Rat.cast_sum, Rat.cast_mul] using he
  | zero => exact map_zero _
  | add y z _ _ hey hez => rw [map_add, hey, hez]
  | smul a y _ hey => rw [map_smul, hey]

theorem rationalMatrix_real_retraction
    (P : Matrix T T ℚ) (W : Submodule ℚ (T → ℚ))
    (hrange : LinearMap.range P.mulVecLin = W)
    (hfix : ∀ x ∈ W, P.mulVecLin x = x) :
    LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
        realRationalCoordinateSpan W ∧
      ∀ x ∈ realRationalCoordinateSpan W,
        Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x := by
  refine ⟨?_, rationalMatrix_real_fixes_coordinateSpan P W hfix⟩
  rw [rationalMatrix_real_range_eq_coordinateSpan, hrange]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_rational_tag_retraction
    {T I : Type*} [Fintype T] [Fintype I]
    (W : Submodule ℚ (T → ℚ)) (b : Basis I ℚ W)
    {p : ℝ} (hp : 0 ≤ p) (hI : (Fintype.card I : ℝ) ≤ p)
    (hb : ∀ a t, rationalLogHeight ((b a : T → ℚ) t) ≤ p) :
    ∃ P : Matrix T T ℚ,
      LinearMap.range P.mulVecLin = W ∧
      (∀ x ∈ W, P *ᵥ x = x) ∧
      P * P = P ∧
      ∀ i j, rationalLogHeight (P i j) ≤ (p + 2) ^ 8 := by
  classical
  let B : Matrix T I ℚ := fun t a => (b a : T → ℚ) t
  let H := ⌊Real.exp p⌋₊
  have hH : 1 ≤ H := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hp)
  have hHp : (H : ℝ) ≤ Real.exp p := Nat.floor_le (Real.exp_nonneg p)
  have hB : ∀ t a, RationalHeightLE (B t a) H := by
    intro t a
    obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff _ _).mp (hb a t)
    exact ⟨Nat.le_floor hn, Nat.le_floor hd⟩
  have hli : LinearIndependent ℚ B.col :=
    b.linearIndependent.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  obtain ⟨C, hCB, hC⟩ := exists_bounded_rational_left_inverse B hli hH hB
  have hBrange : LinearMap.range B.mulVecLin = W := by
    rw [Matrix.range_mulVecLin]
    change Submodule.span ℚ (Set.range (W.subtype ∘ b)) = W
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hfix : ∀ x ∈ W, (B * C) *ᵥ x = x := by
    intro x hx
    rw [← hBrange] at hx
    obtain ⟨y, rfl⟩ := hx
    change (B * C) *ᵥ (B *ᵥ y) = B *ᵥ y
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hCB, Matrix.mul_one]
  have hmem : ∀ x, (B * C) *ᵥ x ∈ W := by
    intro x
    rw [← hBrange, ← Matrix.mulVec_mulVec]
    exact ⟨C *ᵥ x, rfl⟩
  refine ⟨B * C, ?_, hfix, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hmem y
    · intro hx
      exact ⟨x, hfix x hx⟩
  · calc
      B * C * (B * C) = B * (C * B) * C := by simp only [Matrix.mul_assoc]
      _ = B * C := by rw [hCB, Matrix.mul_one]
  · have hsolve := rationalSolveHeight_le_budget (Fintype.card I) H hp hI hHp
    have hprod : ((H * rationalSolveHeight (Fintype.card I) H : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ 6) := by
      rw [Nat.cast_mul]
      calc
        _ ≤ Real.exp p * Real.exp ((p + 2) ^ 5) :=
          mul_le_mul hHp hsolve (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = Real.exp (p + (p + 2) ^ 5) := (Real.exp_add _ _).symm
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hp5 := le_power_budget hp (by decide : 1 ≤ 5)
          calc
            _ ≤ 2 * (p + 2) ^ 5 := by linarith
            _ ≤ (p + 2) * (p + 2) ^ 5 :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ = (p + 2) ^ 6 := by ring
    intro i j
    apply rationalLogHeight_le_of_height (rationalHeightLE_matrix_mul B C hB hC i j)
    exact rational_sum_cost_le_exp (Fintype.card I)
      (H * rationalSolveHeight (Fintype.card I) H) hp 6 1 hprod
      (by simpa using hI.trans (show p ≤ p + 2 by linarith))

theorem exists_bounded_real_rational_tag_retraction
    {T I : Type*} [Fintype T] [Fintype I]
    (W : Submodule ℚ (T → ℚ)) (b : Basis I ℚ W)
    {p : ℝ} (hp : 0 ≤ p) (hI : (Fintype.card I : ℝ) ≤ p)
    (hb : ∀ a t, rationalLogHeight ((b a : T → ℚ) t) ≤ p) :
    ∃ P : Matrix T T ℚ,
      LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
        realRationalCoordinateSpan W ∧
      (∀ x ∈ realRationalCoordinateSpan W, (fun i j => (P i j : ℝ)) *ᵥ x = x) ∧
      ∀ i j, rationalLogHeight (P i j) ≤ (p + 2) ^ 8 := by
  obtain ⟨P, hrange, hfix, _, hheight⟩ :=
    exists_bounded_rational_tag_retraction W b hp hI hb
  obtain ⟨hrangeR, hfixR⟩ := rationalMatrix_real_retraction P W hrange hfix
  exact ⟨P, hrangeR, hfixR, hheight⟩

theorem exists_bounded_real_rational_tag_retraction_grid
    {T I : Type*} [Fintype T] [Fintype I]
    (W : Submodule ℚ (T → ℚ)) (b : Basis I ℚ W)
    {p : ℝ} (hp : 0 ≤ p) (hT : (Fintype.card T : ℝ) ≤ p)
    (hI : (Fintype.card I : ℝ) ≤ p)
    (hb : ∀ a t, rationalLogHeight ((b a : T → ℚ) t) ≤ p) :
    ∃ (P : Matrix T T ℚ) (D : ℕ),
      LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
        realRationalCoordinateSpan W ∧
      (∀ x ∈ realRationalCoordinateSpan W, (fun i j => (P i j : ℝ)) *ᵥ x = x) ∧
      (∀ i j, rationalLogHeight (P i j) ≤ (p + 2) ^ 8) ∧
      0 < D ∧ (D : ℝ) ≤ Real.exp ((p + 2) ^ 10) ∧
      (∀ i j, ∃ z : ℤ, (D : ℝ) * (P i j : ℝ) = (z : ℝ)) ∧
      ∀ (l : ℕ) (x : T → ℝ), x ∈ realDenominatorGrid l →
        (fun i j => (P i j : ℝ)) *ᵥ x ∈ realDenominatorGrid (D * l) := by
  obtain ⟨P, hrange, hfix, hheight⟩ :=
    exists_bounded_real_rational_tag_retraction W b hp hI hb
  obtain ⟨_, hpos, hden, hint⟩ := rational_matrix_entry_budget P hp 8 hT hT
    (fun i j => (rationalLogHeight_le_iff _ _).mp (hheight i j))
  exact ⟨P, matrixDenominator P, hrange, hfix, hheight, hpos, hden, hint,
    fun l x hx => real_matrix_denominator_grid P l x hx⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical Matrix

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem RationalTaggedConstraintCertificate.exists_bounded_rational_retractions
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    let q := p + ((p + 2) ^ 2 + 2) ^ 63
    ∃ (W : ∀ j, Submodule ℚ (J j → ℚ))
      (P : ∀ j, Matrix (J j) (J j) ℚ) (D : Fin m → ℕ),
      K = {x | ∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ realRationalCoordinateSpan (W j)} ∧
      ∀ j,
        LinearMap.range (fullTaggedRealMatrixProjection J P j) = realRationalCoordinateSpan (W j) ∧
        (∀ x ∈ realRationalCoordinateSpan (W j), fullTaggedRealMatrixProjection J P j x = x) ∧
        (∀ i a, rationalLogHeight (P j i a) ≤ (q + 2) ^ 8) ∧
        0 < D j ∧ (D j : ℝ) ≤ Real.exp ((q + 2) ^ 10) ∧
        (∀ i a, ∃ z : ℤ, (D j : ℝ) * (P j i a : ℝ) = (z : ℝ)) ∧
        ∀ (l : ℕ) (x : J j → ℝ), x ∈ realDenominatorGrid l →
          fullTaggedRealMatrixProjection J P j x ∈ realDenominatorGrid (D j * l) := by
  intro q
  obtain ⟨W, n, b, hn, hb, hK⟩ := hcert.exists_bounded_tag_bases_univ hp hdim hblocks
  have hpq : p ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (by positivity)
  have hq : 0 ≤ q := hp.trans hpq
  have hheight : ((p + 2) ^ 2 + 2) ^ 63 ≤ q := by dsimp [q]; linarith
  choose P D hP using fun j => exists_bounded_real_rational_tag_retraction_grid
    (W j) (b j) hq ((hdim j).trans hpq)
    (by simpa only [Fintype.card_fin] using ((Nat.cast_le.mpr (hn j)).trans (hdim j)).trans hpq)
    (fun a i => (hb j a i).trans hheight)
  refine ⟨W, P, D, ?_, hP⟩
  rw [hK]
  ext x
  simp only [Set.mem_ofPred_eq]
  simp_rw [realRationalCoordinateSpan_basis (W _) (b _)]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem candidateSideCutoffCost_exp_bound {p : ℝ} (hp : 0 ≤ p) :
    candidateSideCutoffCost (Real.exp p) ≤ p+2 := by
  have hside := candidateSideCutoff_pos (Real.exp p)
  rw [candidateSideCutoffCost, max_eq_left hside]
  apply (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hside)).mpr
  have hcut := candidateSideCutoff_lt_max_add_two (Real.exp p)
  rw [max_eq_left (Real.exp_nonneg _)] at hcut
  have hlarge := Real.one_le_exp hp
  calc
    _ ≤ Real.exp p + 2 := hcut.le
    _ ≤ 3 * Real.exp p := by linarith only [hlarge]
    _ ≤ Real.exp 2 * Real.exp p :=
      mul_le_mul_of_nonneg_right (by linarith only [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (p+2) := by rw [← Real.exp_add, add_comm]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FullTaggedProjectionPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {X J : Type*} [Fintype J]

theorem sum_projection_coordinate_eq
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x)
    (poly : VectorPolynomial X ℝ (J → ℝ))
    (hm : ∀ α, coefficients poly α ∈ U) (i : J) :
    (∑ a : J, P (Pi.single a 1) i •
      coordinate (LinearMap.proj a : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly) =
      coordinate (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly := by
  ext α
  simp only [coeff_sum, coeff_smul, coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    LinearMap.proj_apply, smul_eq_mul]
  rw [← linearMap_pi_apply_eq_sum, hP _ (hm α)]

theorem sum_projection_coordinate_sub_C_eq
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x)
    (poly : VectorPolynomial X ℝ (J → ℝ))
    (hm : ∀ α, coefficients poly α ∈ U)
    (c : J → ℝ) (hc : c ∈ U) (i : J) :
    (∑ a : J, P (Pi.single a 1) i •
      (coordinate (LinearMap.proj a : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly - C (c a))) =
      coordinate (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly - C (c i) := by
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [sum_projection_coordinate_eq P U hP poly hm i, sum_projection_C_eq P U hP c hc i]

theorem sum_projection_remainder_eq
    {K : Type*}
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x)
    (poly : VectorPolynomial X ℝ (J → ℝ))
    (hm : ∀ α, coefficients poly α ∈ U)
    (c : J → ℝ) (hc : c ∈ U)
    (spatial : X → MvPolynomial K ℝ) (tag error : J → MvPolynomial K ℝ)
    (heq : ∀ a, aeval spatial
      (coordinate (LinearMap.proj a : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly) - C (c a) =
        error a + tag a) (i : J) :
    (∑ a : J, P (Pi.single a 1) i • tag a) -
        aeval spatial
          (coordinate (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly - C (c i)) =
      -(∑ a : J, P (Pi.single a 1) i • error a) := by
  have hcenter := congrArg (aeval spatial)
    (sum_projection_coordinate_sub_C_eq P U hP poly hm c hc i)
  simp only [map_sum, map_smul, map_sub, aeval_C, MvPolynomial.algebraMap_eq] at hcenter
  simp_rw [heq, smul_add] at hcenter
  rw [Finset.sum_add_distrib] at hcenter
  rw [map_sub, aeval_C, MvPolynomial.algebraMap_eq, heq i, ← hcenter]
  abel

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawRecoveredRationalCardinalityCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

noncomputable def forecastLawRecoveredRationalFactor
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) : ℝ :=
  rationalInactiveForecast law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N volume
    (fun a _ => forecastRecoveredIntegerLabels U basis hb bW β (selected a).1
      (Sum.inl (selected a).2))
    (forecastCongruenceOutput short r
      (fun j i => (forecastRecoveredIntegerLabels U basis hb bW β j i : ZMod N)))

noncomputable def forecastLawRecoveredKernel
    (v : X → ℝ) (r : X → ZMod N) (β : (Σ j, J j) → ℤ)
    (y : (Σ j, J j) → ℝ) : ℝ :=
  density (forecastNormalizedSpatialCoordinates base physicalN τ v,
    forecastNormalizedActiveCoordinates short
      (allocatedFullMixedSiteValue (R := R) U basis
        (forecastFrozenIntegerMixedValue U basis o
          (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i)) y))) *
    forecastLawRecoveredRationalFactor B U basis S law selected sample x active Y N volume hb bW r β

end Erdos3.VectorPolynomial

end

end OAI
end


