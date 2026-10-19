-- Prove2me | Definitions.Def_OAIE3v2B116
-- name    : OAIE3v2B116
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:36:15.177007+00:00
-- url     : https://prove2.me/theorems/e0ab4c69-a82f-4dba-8e4c-6582ef53a3e1
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 118 of 311
-- statement:
--   Definitions bundle 118 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102`, `OAIE3v2B103`, `OAIE3v2B104` of this split.
--
--   Modules: `Dynamics/DilationBudgets.lean`, `Estimates/BoundedCoefficientExpansion.lean`, `Estimates/CoefficientRowEvaluation.lean`, `Estimates/ConstantCenterUniformLifts.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Estimates/PinnedSectionMeans.lean`, `Estimates/QuantitativeNoninjectivity.lean`, `Estimates/RationalPowerHeight.lean`, `Estimates/RealProjectedCoefficientLift.lean`, `Estimates/RegularCylinderDecomposition.lean`, `Estimates/ShiftedSmoothSelectedMarginal.lean`, `Estimates/SubspaceLayeredModeSmoothRemoval.lean`, `Fourier/AffineFrequencyLift.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/FactoredPolynomialCharacter.lean`, `Fourier/LayeredFourierCharacter.lean`, `Fourier/SiteFourierHaarMean.lean`, `Geometry/ControlledCoordinateLifts.lean`, `Geometry/CoordinateProductCap.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Geometry/WeightedCoordinateExtraction.lean`, `Lattices/AffineCoefficientCoverTilt.lean`, `Lattices/AffineCoefficientResidueWidths.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Lattices/AffineCubePositiveComparison.lean`, `Lattices/ResidueLinearPointCap.lean`, `Lattices/RetainedAffineCommonCover.lean`, `Lattices/SelectedResidueCenterMix.lean`, `Lattices/SmoothResidueWindowMass.lean`, `Linear/BooleanJetMatrixFactor.lean`, `Nilpotent/BoxNiltestDetection.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Polynomial/BoundedArrayPolynomial.lean`, `Polynomial/DegreeRankAdaptedBasis.lean`, `Polynomial/PolynomialSiteAbsorption.lean`, `Polynomial/RankPolynomialFactorization.lean`, `Probability/IntervalDivisorProbability.lean`, `Sampling/NativeGridRightDictionary.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B102
import Definitions.Def_OAIE3v2B103
import Definitions.Def_OAIE3v2B104

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem shiftedSmoothProductMass_coordinate_pos {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) (i : I) :
    0 < shiftedSmoothSampleSum (a i) (S i) := by
  have hp : (∏ j, shiftedSmoothSampleSum (a j) (S j)) ≠ 0 := by
    rw [← shiftedSmoothProductMass_eq_prod a S hS]
    exact hZ.ne'
  have hn := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  have h0 : 0 ≤ shiftedSmoothSampleSum (a i) (S i) :=
    tsum_nonneg (fun k => (smoothProbabilityProfile_range _).1)
  exact lt_of_le_of_ne h0 hn.symm

theorem shiftedSmoothProductPMF_eq_independent {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S) :
    shiftedSmoothProductPMF a S hS hZ = independentProductPMF
      (fun i => shiftedSmoothCoefficientPMF (a i) (S i) (hS i)
        (shiftedSmoothProductMass_coordinate_pos a S hS hZ i)) := by
  ext x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [shiftedSmoothProductPMF_toReal, independentProductPMF_toReal]
  simp_rw [shiftedSmoothCoefficientPMF_apply]
  rw [Finset.prod_div_distrib, ← shiftedSmoothProductMass_eq_prod a S hS]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def rankCoefficientOrbitHom (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.PolynomialOrbit w →* Multiplicative (F.HigherHorizontal (Finsupp.weight w α)) where
  toFun g := Multiplicative.ofAdd (F.higherHorizontalCoefficient w α
    (F.associatedDegree.polynomialOrbitCoordinates w g).coord)
  map_one' := by
    change Multiplicative.ofAdd (F.higherHorizontalCoefficient w α 0) = 1
    rw [map_zero]
    rfl
  map_mul' g h := by
    change Multiplicative.ofAdd (F.higherHorizontalCoefficient w α
      (F.associatedDegree.polynomialOrbitCoordinates w (g * h)).coord) =
      Multiplicative.ofAdd (F.higherHorizontalCoefficient w α
        (F.associatedDegree.polynomialOrbitCoordinates w g).coord +
        F.higherHorizontalCoefficient w α (F.associatedDegree.polynomialOrbitCoordinates w h).coord)
    rw [map_mul]
    exact congrArg Multiplicative.ofAdd (linearMap_lieBCH_eq_add
      (F.higherHorizontalCoefficient w α) (F.higherHorizontalCoefficient_lie w α) hs _ _)

theorem rankCoefficientOrbitHom_eq_iff (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : F.associatedDegree.PolynomialOrbit w) :
    F.rankCoefficientOrbitHom hs w α g = F.rankCoefficientOrbitHom hs w α h ↔
      coefficients g.log α - coefficients h.log α ∈ F.layer (Finsupp.weight w α) 2 :=
  F.higherHorizontalMk_eq _ _ _

theorem rankCoefficientOrbitHom_eq_one_iff (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.PolynomialOrbit w) :
    F.rankCoefficientOrbitHom hs w α g = 1 ↔
      coefficients g.log α ∈ F.layer (Finsupp.weight w α) 2 := by
  have h := F.rankCoefficientOrbitHom_eq_iff hs w α g 1
  simpa only [map_one, show (1 : F.associatedDegree.PolynomialOrbit w).log = 0 from rfl,
    map_zero, Finsupp.zero_apply, sub_zero] using h

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

theorem exists_polynomialOrbit_factorization_rank_two
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (hs : 1 ≤ s) (w : σ → ℕ)
    (α : ι → σ →₀ ℕ) (g E A U Q : F.associatedDegree.PolynomialOrbit w)
    (hg : F.associatedDegree.polynomialOrbitEval w 0 g = 1)
    (hE : F.associatedDegree.polynomialOrbitEval w 0 E = 1)
    (hA : F.associatedDegree.polynomialOrbitEval w 0 A = 1)
    (hU : F.associatedDegree.polynomialOrbitEval w 0 U = 1)
    (hQ : F.associatedDegree.polynomialOrbitEval w 0 Q = 1)
    (hcoeff : ∀ i, coefficients g.log (α i) -
      (coefficients E.log (α i) + coefficients A.log (α i) +
        coefficients U.log (α i) + coefficients Q.log (α i)) ∈
          F.layer (Finsupp.weight w (α i)) 2) :
    ∃ K : F.associatedDegree.PolynomialOrbit w,
      F.associatedDegree.polynomialOrbitEval w 0 K = 1 ∧ E * A * K * U * Q = g ∧
      ∀ i, coefficients K.log (α i) ∈ F.layer (Finsupp.weight w (α i)) 2 := by
  let K := A⁻¹ * E⁻¹ * g * Q⁻¹ * U⁻¹
  have hhom (i : ι) :
      F.rankCoefficientOrbitHom hs w (α i) g =
        F.rankCoefficientOrbitHom hs w (α i) E * F.rankCoefficientOrbitHom hs w (α i) A *
          F.rankCoefficientOrbitHom hs w (α i) U * F.rankCoefficientOrbitHom hs w (α i) Q := by
    let z (v : F.associatedDegree.PolynomialOrbit w) :=
      F.rankLayerCoefficient w (α i) (F.associatedDegree.polynomialOrbitCoordinates w v).coord
    change F.higherHorizontalMk _ (z g) =
      F.higherHorizontalMk _ (z E) + F.higherHorizontalMk _ (z A) +
        F.higherHorizontalMk _ (z U) + F.higherHorizontalMk _ (z Q)
    rw [← map_add, ← map_add, ← map_add]
    exact (F.higherHorizontalMk_eq _ _ _).mpr (hcoeff i)
  refine ⟨K, ?_, ?_, ?_⟩
  · simp only [K, map_mul, map_inv, hg, hE, hA, hU, hQ, inv_one, one_mul]
  · dsimp only [K]
    group
  · intro i
    apply (F.rankCoefficientOrbitHom_eq_one_iff hs w (α i) K).mp
    simp only [K, map_mul, map_inv]
    rw [hhom i]
    group

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

noncomputable def raisedLayerBasis (i : Fin (t + 1)) :
    Basis (Fin (Module.finrank ℚ ((D.filtration.raiseStep hst).layer (i.val + 1)))) ℚ
      ((D.filtration.raiseStep hst).layer (i.val + 1)) := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact if hi : i.val < s + 1 then D.layerBasis ⟨i.val, hi⟩ else
    Module.finBasis ℚ ((D.filtration.raiseStep hst).layer (i.val + 1))

noncomputable def raiseStep : RationalFilteredNilmanifold L t d where
  filtration := D.filtration.raiseStep hst
  basis := D.basis
  layerBasis := D.raisedLayerBasis hst
  lattice := D.lattice.map (NilpotentLieBCHGroup.changeStep D.filtration.lowerCentralSeries_eq_bot
    (D.filtration.raiseStep hst).lowerCentralSeries_eq_bot).toMonoidHom
  grid := D.grid
  grid_pos := D.grid_pos
  inner_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.inner_grid
  outer_grid := by
    rw [bchSubgroupCoordinates_changeStep]
    exact D.outer_grid

theorem raiseStep_lattice_back :
    (D.raiseStep hst).lattice ≤ D.lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (hL := (D.filtration.raiseStep hst).lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact hx

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3

theorem rationalLogHeight_nonneg (q : ℚ) : 0 ≤ rationalLogHeight q := by
  apply Real.log_nonneg
  have hd : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  exact hd.trans (le_max_right _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueDensityMass_singleton_window_bound {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (r : ColumnResiduePattern K X q)
    (V : K × X → ℝ) (hV : ∀ i, 0 < V i)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V i)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q {r} V z)
    (D : (K × X → ℤ) → ℝ) (hD : ∀ z, 0 ≤ D z)
    (window : Finset (K × X → ℤ))
    (hresidue : ∀ z ∈ window, columnResiduePattern q z = r)
    (hsmall : ∀ z ∈ window, ∀ i, |(z i : ℝ) / V i| ≤ 1 / 2) :
    (∑ z ∈ window, D z) ≤
      ((3 / 2 : ℝ) ^ Fintype.card (K × X) * (∏ i, residueProfileWidth q V i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (K × X)) *
          selectedResidueDensityMass q {r} V D := by
  classical
  have hm : 0 ≤ selectedResidueDensityMass q {r} V D := by
    apply tsum_nonneg
    intro z
    exact mul_nonneg (div_nonneg (selectedResidueSmoothWeight_nonneg q {r} V z) hZ.le) (hD z)
  apply (selectedResidueDensityMass_window_bound q {r} V hV hZ D hD window
    (fun z hz => Finset.mem_singleton.mpr (hresidue z hz)) hsmall).trans
  apply mul_le_mul_of_nonneg_right _ hm
  exact div_le_div_of_nonneg_right (selectedResidueSmoothWeight_singleton_mass_upper q hq r V hV hscale)
    (pow_pos smoothProbabilityProfile_pos_zero _).le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem reweightPositive_mean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) (f : X → ℝ) :
    (p.reweightPositive w hw hm).mean f = p.mean (fun x => w x * f x) / p.mean w := by
  simp only [mean, reweightPositive_weight, div_mul_eq_mul_div, mul_assoc, Finset.sum_div]

theorem reweightPositive_complexMean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) (f : X → ℂ) :
    (p.reweightPositive w hw hm).complexMean f =
      p.complexMean (fun x => (w x : ℂ) * f x) / (p.mean w : ℂ) := by
  simp only [complexMean, reweightPositive_weight, Complex.ofReal_div, Complex.ofReal_mul,
    div_mul_eq_mul_div, mul_assoc, Finset.sum_div]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem reweightPositive_test_le {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < p.mean D) (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    {C ε a : ℝ} (ha : 0 < a) (hlower : a ≤ p.mean D)
    (he : p.mean (fun x => D x * φ x) ≤ C * p.mean φ + ε) :
    (p.reweightPositive D hD0 hD).mean φ ≤ (C * p.mean φ + ε) / a := by
  rw [p.reweightPositive_mean]
  have hnum : 0 ≤ C * p.mean φ + ε :=
    (p.mean_nonneg (fun x => mul_nonneg (hD0 x) (hφ x))).trans he
  exact (div_le_div_of_nonneg_right he hD.le).trans
    (div_le_div_of_nonneg_left hnum ha hlower)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

variable {X C : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem normalizedDensityTest_norm_le_one (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (hmass : 0 < p.mean D) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.normalizedDensityTest D f‖ ≤ 1 := by
  rw [normalizedDensityTest, norm_div, Complex.norm_real, Real.norm_of_nonneg hmass.le]
  exact (div_le_one hmass).mpr (p.norm_density_weighted_complexMean_le D hD f hf)

variable [MeasurableSpace C]

theorem normalizedDensityTest_measurable (D : C → X → ℝ)
    (hD : ∀ x, Measurable (fun c => D c x)) (f : X → ℂ) :
    Measurable (fun c => p.normalizedDensityTest (D c) f) :=
  (p.complexMean_measurable (fun c x => (D c x : ℂ)*f x)
    (fun x => (Complex.continuous_ofReal.measurable.comp (hD x)).mul_const (f x))).div
    (Complex.continuous_ofReal.measurable.comp (p.mean_measurable D hD))

theorem normalizedDensityTest_integrable (μ : Measure C) [IsFiniteMeasure μ]
    (D : C → X → ℝ) (hD : ∀ x, Measurable (fun c => D c x))
    (hD0 : ∀ c x, 0 ≤ D c x) (hmass : ∀ c, 0 < p.mean (D c))
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    Integrable (fun c => p.normalizedDensityTest (D c) f) μ :=
  Integrable.of_bound (p.normalizedDensityTest_measurable D hD f).aestronglyMeasurable 1
    (ae_of_all μ (fun c => p.normalizedDensityTest_norm_le_one (D c) (hD0 c) (hmass c) f hf))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem reweightPositive_complexMean_eq_normalizedDensityTest
    (p : FiniteProbabilityWeights X) (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (hmass : 0 < p.mean D) (f : X → ℂ) :
    (p.reweightPositive D hD hmass).complexMean f = p.normalizedDensityTest D f :=
  p.reweightPositive_complexMean D hD hmass f

theorem normalizedDensityTest_remove_normalization (p : FiniteProbabilityWeights X)
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x) (hmass : 0 < p.mean D)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.normalizedDensityTest D f - p.complexMean (fun x => (D x : ℂ)*f x)‖ ≤ |p.mean D-1| :=
  complex_remove_normalization hmass (p.norm_density_weighted_complexMean_le D hD f hf)

theorem joint_normalization_compare (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (D : X × Y → ℝ) (hD : ∀ z, 0 ≤ D z)
    (hlocal : ∀ x, 0 < q.mean (fun y => D (x,y))) (hglobal : 0 < (p.prod q).mean D)
    (f : X × Y → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) {ε : ℝ}
    (hclose : ∀ x, |q.mean (fun y => D (x,y))-1| ≤ ε) :
    ‖(p.prod q).normalizedDensityTest D f -
      p.complexMean (fun x => q.normalizedDensityTest (fun y => D (x,y)) (fun y => f (x,y)))‖ ≤ 2*ε := by
  have hmass : |(p.prod q).mean D-1| ≤ ε := by
    rw [mean_prod]
    exact p.abs_mean_sub_const_le _ 1 ε hclose
  have hj := ((p.prod q).normalizedDensityTest_remove_normalization D hD hglobal f hf).trans hmass
  have hl := p.norm_complexMean_sub_le
    (fun x => q.normalizedDensityTest (fun y => D (x,y)) (fun y => f (x,y)))
    (fun x => q.complexMean (fun y => (D (x,y) : ℂ)*f (x,y))) (fun _ => ε)
    (fun x _ => (q.normalizedDensityTest_remove_normalization _ (fun y => hD (x,y))
      (hlocal x) _ (fun y => hf (x,y))).trans (hclose x))
  rw [p.mean_const, ← complexMean_prod p q (fun z => (D z : ℂ)*f z)] at hl
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((p.prod q).normalizedDensityTest D f)
    ((p.prod q).complexMean (fun z => (D z : ℂ)*f z))
    (p.complexMean (fun x => q.normalizedDensityTest (fun y => D (x,y)) (fun y => f (x,y))))
  rw [norm_sub_rev ((p.prod q).complexMean _)] at ht
  linarith

theorem uniformFinset_complexMean {A : Type*} (S : Finset A) (hS : S.Nonempty) (f : A → ℂ) :
    (uniformFinset S hS).complexMean (fun x => f x.val) = 𝔼 x ∈ S, f x := by
  let : Nonempty S := hS.to_subtype
  rw [uniformFinset, uniform_complexMean]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Finset.sum_coe_sort, Fintype.card_coe]

end Erdos3.FiniteProbabilityWeights

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

theorem projectedLayerCoefficient_tensor_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (G.fourHorizontalLayer (Finsupp.weight w α)).subtype.baseChange ℝ
        ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x) =
      φ.toLinearMap.baseChange ℝ (coefficients (F.realAdaptedPolynomialMap w x) α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    simp only [LinearMap.baseChange_tmul, G.projectedLayerCoefficient_coe,
      F.realAdaptedPolynomialMap_coefficient_tmul, Submodule.subtype_apply]
    rfl
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable (b : Basis ι ℚ M) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hφ hF in
theorem real_projectedCoefficient_mem (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.realification.adaptedLieSubalgebra w) :
    φ.toLinearMap.baseChange ℝ (coefficients p.val α) ∈
      (G.fourHorizontalLayer (Finsupp.weight w α)).baseChange ℝ := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  rw [F.realAdaptedPolynomialTensor_coe, ← G.projectedLayerCoefficient_tensor_coe F φ hφ]
  exact (realificationSubmoduleEquiv (G.fourHorizontalLayer (Finsupp.weight w α))
    ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x)).property

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

noncomputable def higherHorizontalCoordinates : F.HigherHorizontal d →ₗ[ℚ] (ι → ℚ) :=
  f.equivFun.toLinearMap.comp (F.higherHorizontalAmbient d)

noncomputable def ambientHorizontalCoordinates : L →ₗ[ℚ] (ι → ℚ) :=
  f.equivFun.toLinearMap.comp (F.layer d 2).mkQ

theorem higherHorizontalCoordinates_injective : Function.Injective (F.higherHorizontalCoordinates d f) :=
  f.equivFun.injective.comp (F.higherHorizontalAmbient_injective d)

noncomputable def fourHorizontalCoordinates :
    (Fin 4 → F.HigherHorizontal d) →ₗ[ℚ] (Fin 4 → ι → ℚ) :=
  LinearMap.pi (fun k => (F.higherHorizontalCoordinates d f).comp (LinearMap.proj k))

noncomputable def fourAmbientCoordinates : (Fin 4 → L) →ₗ[ℚ] (Fin 4 → ι → ℚ) :=
  LinearMap.pi (fun k => (F.ambientHorizontalCoordinates d f).comp (LinearMap.proj k))

theorem fourHorizontalCoordinates_map (x : F.fourHorizontalLayer d) :
    F.fourHorizontalCoordinates d f (F.fourHorizontalMap d x) =
      F.fourAmbientCoordinates d f x.val := by
  ext k i
  rfl

theorem fourAmbientCoordinates_height [Fintype μ] (b : Basis μ ℚ L) {H K : ℕ}
    (hf : ∀ i j, RationalHeightLE (f.repr ((F.layer d 2).mkQ (b j)) i) H)
    (x : Fin 4 → L) (hx : ∀ k j, RationalHeightLE (b.repr (x k) j) K)
    (k : Fin 4) (i : ι) :
    RationalHeightLE (F.fourAmbientCoordinates d f x k i)
      ((Fintype.card μ + 1) * (K * H) ^ Fintype.card μ) :=
  linearMap_coordinate_height b f (F.layer d 2).mkQ (fun j i => hf i j) (x k) (hx k) i

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def realHigherHorizontalCoordinates : (ℝ ⊗[ℚ] F.HigherHorizontal d) →ₗ[ℝ] (ι → ℝ) :=
  realRationalCoordinateEquiv.toLinearMap.comp ((F.higherHorizontalCoordinates d f).baseChange ℝ)

theorem realHigherHorizontalCoordinates_injective :
    Function.Injective (F.realHigherHorizontalCoordinates d f) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact realRationalCoordinateEquiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
      (F.higherHorizontalCoordinates d f) (F.higherHorizontalCoordinates_injective d f))

end Erdos3.DegreeRankLieFiltration

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

theorem exists_bounded_rank_adapted_basis
    {η : Fin (s + 1) → Fin (s + 1) → Type*}
    (v : ∀ i j, η i j → F.layer i.val j.val)
    (hspan : ∀ i j, Submodule.span ℚ (Set.range (v i j)) = ⊤) {H : ℕ}
    (hv : ∀ i j a k, RationalHeightLE (e.repr (v i j a : L) k) H) :
    ∃ b : Basis (Fin (finrank ℚ L)) ℚ L,
      IsCentralLieBasis b ∧ (∀ a k, RationalHeightLE (e.repr (b a) k) H) ∧
      ∀ i j, ∃ c ≤ finrank ℚ L, F.layer i j = basisTail b c := by
  let := e.finiteDimensional_of_finite
  let N := (s + 1) * (s + 1)
  let S : Set L := {x | ∀ k, RationalHeightLE (e.repr x k) H}
  let P : Fin (N + 1) → Submodule ℚ L := fun n => F.rankFlag n.val
  have hP : Antitone P := fun _ _ h => F.rankFlag_antitone h
  have hSP (n : Fin (N + 1)) : Submodule.span ℚ (S ∩ (P n : Set L)) = P n := by
    by_cases hn : n.val < (s + 1) * (s + 1)
    · obtain ⟨hi, hj⟩ := rankFlag_decode_lt hn
      let i : Fin (s + 1) := ⟨n.val / (s + 1), Nat.lt_succ_of_le hi⟩
      let j : Fin (s + 1) := ⟨n.val % (s + 1), Nat.lt_succ_of_le hj⟩
      exact span_inter_eq_of_spanning_family _ (v i j) (hspan i j) S (hv i j)
    · have heq : n.val = (s + 1) * (s + 1) := by dsimp only [N] at n; omega
      change Submodule.span ℚ (S ∩ (F.rankFlag n.val : Set L)) = F.rankFlag n.val
      rw [heq, F.rankFlag_terminal]
      exact le_antisymm (Submodule.span_le.mpr (fun _ hx => hx.2)) bot_le
  have hS : Submodule.span ℚ S = ⊤ := by
    apply top_unique
    calc
      ⊤ = P 0 := F.rankFlag_zero.symm
      _ = Submodule.span ℚ (S ∩ (P 0 : Set L)) := (hSP 0).symm
      _ ≤ Submodule.span ℚ S := Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, w, hw, _, hb, hflag⟩ := exists_sorted_flag_basis_from_spanning_set P hP S hS hSP
  refine ⟨b, centralLieBasis_of_finite_flag F.rankFlag b w F.rankFlag_zero F.rankFlag_terminal
    (fun _ {_ _} hy => F.rankFlag_lie_mem hy) hw hflag, hb, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := F.layer_eq_rankFlag i j
  exact ⟨weightCut w k.val, weightCut_le w k.val,
    hk.trans ((hflag k).trans (span_weight_gt_eq_basisTail b w hw k.val))⟩

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeGridRightDictionary
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

structure NativeGridRightDictionary
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (inputDenominator : ℕ) (B : ℝ) where
  denominator : ℕ
  count : ℕ
  denominator_pos : 0 < denominator
  count_pos : 0 < count
  denominator_bound : (denominator : ℝ) ≤ B
  count_bound : (count : ℝ) ≤ B
  representative : Fin count → D.RealGroup
  representative_bounds : ∀ j,
    (∀ i, |(D.basis.baseChange ℝ).repr (representative j).coord i| ≤ B) ∧
    (D.basis.baseChange ℝ).equivFun (representative j).coord ∈
      realDenominatorGrid denominator
  cover : ∀ g : D.RealGroup,
    (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid inputDenominator →
    ∃ j : Fin count, ∃ γ ∈ D.realLattice, g = representative j * γ

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open scoped TensorProduct

instance instRealContinuousSMul (d : ℕ) : ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d) :=
  ModuleTopology.continuousSMul ℝ _

end Erdos3.RationalTorus

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FactoredPolynomialCharacter
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem factored_polynomial_mode_character {I K S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (site : S → K → ℝ)
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (M : (S → W) →ₗ[ℝ] ℝ)
    (hfactor : ∀ q, DegreeLE (1 : K → ℕ) h q → Λ q = M (siteEvaluation site q))
    (p : VectorPolynomial I ℝ W) (hp : DegreeLE (1 : I → ℕ) h p)
    (f : I → MvPolynomial K ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    character (Λ (substitute f p) : CircleFourier.Circle) =
      ∏ s, siteFunctionalCharacter M s (eval (fun i => MvPolynomial.aeval (site s) (f i)) p) := by
  rw [hfactor _ (degreeLE_substitute_affine f hf p hp), character_linear_site_sum]
  apply Finset.prod_congr rfl
  intro s _
  change siteFunctionalCharacter M s (eval (site s) (substitute f p)) = _
  rw [eval_substitute]

theorem homogeneously_factored_polynomial_character {I K S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (site : S → K → ℝ)
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (M : (S → W) →ₗ[ℝ] ℝ)
    (hfactor : ∀ q, Homogeneous h q → Λ (substitute dehomogenizingSubstitution q) =
      M (siteEvaluation (fun s (i : Option K) => i.elim 1 (site s)) q))
    (p : VectorPolynomial I ℝ W) (hp : DegreeLE (1 : I → ℕ) h p)
    (f : I → MvPolynomial K ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    character (Λ (substitute f p) : CircleFourier.Circle) =
      ∏ s, siteFunctionalCharacter M s (eval (fun i => MvPolynomial.aeval (site s) (f i)) p) :=
  factored_polynomial_mode_character h site Λ M
    ((homogeneous_site_factorization_iff h site Λ M).mp hfactor) p hp f hf

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSiteAbsorption
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem exists_absorbed_polynomial_site_tests {A I K S G : Type*} {W : A → Type*}
    [Fintype A] [Fintype S] [DecidableEq S]
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℝ (W a)]
    (h : A → ℕ) (site : S → K → ℝ)
    (Λ : ∀ a, VectorPolynomial K ℝ (W a) →ₗ[ℝ] ℝ)
    (hfactor : ∀ a, ∃ M : (S → W a) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (h a) q → Λ a (substitute dehomogenizingSubstitution q) =
        M (siteEvaluation (fun s (i : Option K) => i.elim 1 (site s)) q))
    (p : ∀ a, VectorPolynomial I ℝ (W a)) (hp : ∀ a, DegreeLE (1 : I → ℕ) (h a) (p a))
    (f : G → I → MvPolynomial K ℝ) (hf : ∀ g i, (f g i).totalDegree ≤ 1)
    (low : G → ℝ) (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ g,
      character ((low g + ∑ a, Λ a (substitute (f g) (p a)) : ℝ) : CircleFourier.Circle) *
        (∏ s, test s (fun i => MvPolynomial.aeval (site s) (f g i))) =
      character (low g : CircleFourier.Circle) *
        (∏ s, test' s (fun i => MvPolynomial.aeval (site s) (f g i))) := by
  classical
  choose M hM using hfactor
  let χ : A → S → (I → ℝ) → ℂ := fun a s x => siteFunctionalCharacter (M a) s (eval x (p a))
  refine ⟨absorbedSiteTests χ test, ?_, ?_⟩
  · intro s x
    rw [absorbedSiteTests_norm χ (fun a s x => siteFunctionalCharacter_norm _ _ _) test]
    exact htest s x
  · intro g
    apply absorb_factored_phases χ test
      (fun g s i => MvPolynomial.aeval (site s) (f g i))
      (fun a g => Λ a (substitute (f g) (p a))) _ low g
    intro a g
    exact homogeneously_factored_polynomial_character (h a) site (Λ a) (M a) (hM a) (p a) (hp a) (f g) (hf g)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem exists_absorbed_integer_site_tests {A I K S : Type*} {W : A → Type*}
    [Fintype A] [Fintype K] [Fintype S] [DecidableEq S]
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℝ (W a)]
    (h : A → ℕ) (site : S → K → ℤ)
    (L : ∀ a, VectorPolynomial K ℝ (W a) →ₗ[ℝ] ℝ)
    (hfactor : ∀ a, ∃ M : (S → W a) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (h a) q →
        L a q = M (siteEvaluation (fun s k => (site s k : ℝ)) q))
    (p : ∀ a, VectorPolynomial I ℝ (W a)) (hp : ∀ a, DegreeLE (1 : I → ℕ) (h a) (p a))
    (low : (K → I → ℝ) → ℝ)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
      character ((low b + ∑ a, L a (substitute (fun i => rowPolynomial (fun k => b k i)) (p a)) : ℝ) :
        CircleFourier.Circle) * (∏ s, test s (integerSiteValue (site s) b)) =
      character (low b : CircleFourier.Circle) * (∏ s, test' s (integerSiteValue (site s) b)) := by
  have hf (a : A) : ∃ M : (S → W a) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (h a) q → L a (substitute dehomogenizingSubstitution q) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (fun k => (site s k : ℝ))) q) := by
    obtain ⟨M, hM⟩ := hfactor a
    exact ⟨M, (homogeneous_site_factorization_iff (h a)
      (fun s k => (site s k : ℝ)) (L a) M).mpr hM⟩
  obtain ⟨test', ht, he⟩ := exists_absorbed_polynomial_site_tests h
    (fun s k => (site s k : ℝ)) L hf p hp
    (fun (b : K → I → ℝ) i => rowPolynomial (fun k => b k i))
    (fun b i => (rowPolynomial_homogeneous (fun k => b k i)).totalDegree_le) low test htest
  refine ⟨test', ht, ?_⟩
  intro b
  simpa only [rowPolynomial_integer_site] using he b

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AffineFrequencyLift
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem affineModeLift_coefficientFunctional {K J : Type*} [Fintype J]
    (frequency : (K →₀ ℕ) → J → ℝ) :
    affineModeLift (coefficientFunctional frequency) =
      coefficientFunctional (affineLiftFrequency frequency) := by
  apply LinearMap.ext
  intro p
  conv_lhs => rw [← sum_monomial_coefficients p]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, affineModeLift, LinearMap.comp_apply,
    dehomogenize_monomial, coefficientFunctional_monomial, affineLiftFrequency]

theorem affineModeLift_integerFrequency {K J : Type*} [Fintype J]
    (frequency : (K →₀ ℕ) → J → ℤ) :
    affineModeLift (coefficientFunctional (fun d j => (frequency d j : ℝ))) =
      coefficientFunctional (fun d j => ((affineLiftFrequency frequency d j : ℤ) : ℝ)) :=
  affineModeLift_coefficientFunctional _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SubspaceLayeredModeSmoothRemoval
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem exists_layered_mode_reduction {I K S : Type*} [Fintype K] [Fintype S] [DecidableEq S]
    {m : ℕ} {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)] (i : Fin m)
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (site : S → K → ℤ)
    (hfactor : ∀ j, i < j → ∃ M : (S → W j) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (j.val + 1) q →
        L j q = M (siteEvaluation (fun s k => (site s k : ℝ)) q))
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < i.val + 1)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ Q' : MvPolynomial (K × I) ℝ, Q'.totalDegree < i.val + 1 ∧
      ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
        layeredModeTestedPhase L p Q site test b =
          coefficientModeTestedPhase (L i) (p i) Q' site test' b := by
  classical
  let Q' := lowerLayerPolynomial i L p + Q
  have hQ' : Q'.totalDegree < i.val + 1 :=
    lt_of_le_of_lt (MvPolynomial.totalDegree_add _ _)
      (max_lt (lowerLayerPolynomial_degree i L p hp) hQ)
  let low (b : K → I → ℝ) :=
    L i (substitute (fun u => rowPolynomial (fun k => b k u)) (p i)) +
      MvPolynomial.eval (fun z => b z.1 z.2) Q'
  obtain ⟨test', ht, he⟩ := exists_absorbed_integer_site_tests
    (fun j : {j : Fin m // i < j} => j.val.val + 1) site
    (fun j => L j.val) (fun j => hfactor j.val j.property)
    (fun j => p j.val) (fun j => hp j.val) low test htest
  refine ⟨Q', hQ', test', ht, ?_⟩
  intro b
  have hsplit : (∑ j, L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j))) +
      MvPolynomial.eval (fun z => b z.1 z.2) Q = low b +
      ∑ j : {j : Fin m // i < j},
        L j.val (substitute (fun u => rowPolynomial (fun k => b k u)) (p j.val)) := by
    rw [sum_split_at_layer i]
    dsimp [low, Q']
    rw [map_add, lowerLayerPolynomial_eval]
    ring
  unfold layeredModeTestedPhase
  rw [hsplit]
  exact he b

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_subspace_layered_mode_reduction {I K S : Type*}
    [Fintype K] [Fintype S] [DecidableEq S] {m : ℕ}
    {V : Fin m → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)] (i : Fin m)
    (U : ∀ j, Submodule ℝ (V j)) (L : ∀ j, VectorPolynomial K ℝ (V j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (V j)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (site : S → K → ℤ)
    (hfactor : ∀ j, i < j → ∃ M : (S → U j) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (j.val + 1) q →
        L j (map (U j).subtype q) = M (siteEvaluation (fun s k => (site s k : ℝ)) q))
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < i.val + 1)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ Q' : MvPolynomial (K × I) ℝ, Q'.totalDegree < i.val + 1 ∧
      ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
        layeredModeTestedPhase L p Q site test b =
          coefficientModeTestedPhase (L i) (p i) Q' site test' b := by
  let p' := fun j => restrictCoefficients (U j) (p j) (hm j)
  have hp' j : DegreeLE (1 : I → ℕ) (j.val + 1) (p' j) :=
    degreeLE_restrictCoefficients (U j) (p j) (hm j) (hp j)
  obtain ⟨Q', hQ', test', ht, he⟩ := exists_layered_mode_reduction i
    (fun j => (L j).comp (map (U j).subtype)) p' hp' site hfactor Q hQ test htest
  refine ⟨Q', hQ', test', ht, ?_⟩
  intro b
  simpa only [layeredModeTestedPhase_map, coefficientModeTestedPhase_map, p',
    map_restrictCoefficients] using he b

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LayeredFourierCharacter
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem layeredCoefficientCharacter_norm {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) :
    ‖layeredCoefficientCharacter L p b‖ = 1 := norm_character _

theorem layeredModeTestedPhase_eq_weight_mul {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    layeredModeTestedPhase L p Q site test b =
      layeredSiteWeight Q site test b * layeredCoefficientCharacter L p b := by
  unfold layeredModeTestedPhase layeredSiteWeight layeredCoefficientCharacter
  rw [AddCircle.coe_add, character_add]
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientResidueWidths
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem layeredModeTestedPhase_empty_zero {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) :
    layeredModeTestedPhase L p 0 (Empty.elim : Empty → K → ℤ) Empty.elim b =
      layeredCoefficientCharacter L p b := by
  simp [layeredModeTestedPhase, layeredCoefficientCharacter]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

def affineCoefficientModeTrivial {K : Type*} {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : Prop :=
  ∀ j, ∀ P, Homogeneous (j.val + 1) P →
    affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
      (map (U j).subtype P) = 0

theorem not_affineCoefficientModeTrivial_iff {K : Type*} {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    ¬affineCoefficientModeTrivial U frequency ↔
      ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
          (map (U i).subtype P) ≠ 0 := by
  simp only [affineCoefficientModeTrivial, not_forall, exists_prop]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedCoefficientExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem affineModeLift_zero_iff_bounded {K W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (h : ℕ) :
    (∀ P, Homogeneous h P → affineModeLift L P = 0) ↔
      ∀ P, DegreeLE (1 : K → ℕ) h P → L P = 0 := by
  simpa only [affineModeLift, LinearMap.comp_apply, LinearMap.zero_apply] using
    homogeneous_site_factorization_iff h (Empty.elim : Empty → K → ℝ) L
      (0 : (Empty → W) →ₗ[ℝ] ℝ)

theorem coefficientArrayFunctional_eq_zero_iff_trivial {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    coefficientArrayFunctional U frequency = 0 ↔ affineCoefficientModeTrivial U frequency := by
  rw [coefficientArrayFunctional_eq_zero_iff]
  constructor
  · intro hz j P hP
    by_contra hn
    have hn' : coefficientFunctional
        (fun d a => ((affineLiftFrequency (frequency j) d a : ℤ) : ℝ)) (map (U j).subtype P) ≠ 0 := by
      rwa [← affineModeLift_integerFrequency]
    obtain ⟨d, hd, w, hw⟩ := exists_restricted_coefficient_nonzero (U j)
      (affineLiftFrequency (frequency j)) ⟨P, hP, hn'⟩
    exact hw (hz ⟨j, ⟨d.some, (some_degree_le d).trans hd.le⟩⟩ w)
  · intro hz s w
    let L := (coefficientFunctional (fun d a => (frequency s.1 d a : ℝ))).comp (map (U s.1).subtype)
    have hlift : ∀ P, Homogeneous (s.1.val + 1) P → affineModeLift L P = 0 := by
      simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply] using hz s.1
    have he := (affineModeLift_zero_iff_bounded L (s.1.val + 1)).mp hlift
      (monomial s.2.val w) (degreeLE_monomial_of_degree_le s.2.property w)
    simpa only [L, LinearMap.comp_apply, map_monomial, Submodule.subtype_apply,
      coefficientFunctional_monomial] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem coefficientFunctional_bounded_expansion {K J : Type*} [Fintype K] [Fintype J]
    (frequency : (K →₀ ℕ) → J → ℝ) {h : ℕ}
    (p : VectorPolynomial K ℝ (J → ℝ)) (hp : DegreeLE (1 : K → ℕ) h p) :
    coefficientFunctional frequency p =
      ∑ d : BoundedCoefficientExponent K h, ∑ a, frequency d.val a * coefficients p d.val a := by
  conv_lhs => rw [← sum_bounded_monomial_coefficients p hp]
  simp only [map_sum, coefficientFunctional_monomial]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedArrayPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem boundedArrayPolynomial_coeff {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (x : BoundedCoefficientExponent K h → W)
    (d : BoundedCoefficientExponent K h) :
    coefficients (boundedArrayPolynomial h x) d.val = x d := by
  simp only [boundedArrayPolynomial, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e _ hed
    have he : e.val ≠ d.val := fun h => hed (Subtype.ext h)
    simp [he]
  · simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem siteEvaluation_bounded_coefficients {K S W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ} (site : S → K → ℤ)
    (p : VectorPolynomial K ℝ W) (hp : DegreeLE (1 : K → ℕ) h p) :
    siteEvaluation (fun s k => (site s k : ℝ)) p =
      matrixModuleAction (fun s d => (boundedSiteMatrix h site s d : ℝ))
        (fun d => coefficients p d.val) := by
  rw [← boundedArrayPolynomial_reconstruct p hp, siteEvaluation_boundedArrayPolynomial]
  simp only [boundedArrayPolynomial_coeff]

theorem bounded_site_factorization_to_array {K S J : Type*} [Fintype K] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (site : S → K → ℤ)
    (frequency : (K →₀ ℕ) → J → ℝ) (M : (S → U) →ₗ[ℝ] ℝ)
    (hf : ∀ p : VectorPolynomial K ℝ U, DegreeLE (1 : K → ℕ) h p →
      coefficientFunctional frequency (map U.subtype p) = M (siteEvaluation (fun s k => (site s k : ℝ)) p)) :
    ∀ x, subspaceArrayFunctional U (fun d : BoundedCoefficientExponent K h => frequency d.val) x =
      M (matrixModuleAction (fun s d => (boundedSiteMatrix h site s d : ℝ)) x) := by
  intro x
  have he := hf (boundedArrayPolynomial h x) (boundedArrayPolynomial_degreeLE h x)
  rwa [coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial] at he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem coefficientTorusCharacter_integral {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [MeasurableAdd₂ (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, coefficientTorusCharacter U frequency x ∂μ) =
      if affineCoefficientModeTrivial U frequency then 1 else 0 := by
  rw [coefficientTorusCharacter, quotientLinearCharacter_integral,
    coefficientArrayFunctional_eq_zero_iff_trivial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem affineSampleCoefficientArray_val {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (b : Option K → I → ℝ) (s : CoefficientSlot K m) :
    (affineSampleCoefficientArray U p hm b s).val =
      coefficients (substitute (affineParameterSubstitution b) (p s.1)) s.2.val := by
  change (U s.1).subtype (coefficients _ s.2.val) = _
  rw [← coefficients_map, map_substitute, map_restrictCoefficients]

theorem coefficientArrayFunctional_sample {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    coefficientArrayFunctional U frequency (affineSampleCoefficientArray U p hm b) =
      ∑ j, affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
        (substitute (fun u => rowPolynomial (fun k => b k u)) (p j)) := by
  change (∑ s : CoefficientSlot K m, ∑ a,
    (frequency s.1 s.2.val a : ℝ) * (affineSampleCoefficientArray U p hm b s).val a) = _
  simp only [affineSampleCoefficientArray_val, CoefficientSlot, Fintype.sum_sigma,
    affineModeLift_substitute]
  apply Finset.sum_congr rfl
  intro j _
  exact (coefficientFunctional_bounded_expansion (fun d a => (frequency j d a : ℝ)) (h := j.val + 1) _
    (degreeLE_substitute_affine _ (affineParameterSubstitution_degree b) (p j) (hp j))).symm

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
  {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientSiteResidual_zero_iff [∀ j, Fintype (J j)]
    (site : S → K → ℤ) (q : Fin m → ℕ)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (hq : ∀ j, 0 < q j)
    (hT : ∀ j (x : BoundedCoefficientExponent K (j.val + 1) → U j),
      matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
        (matrixModuleAction (fun d s => (T j d s : ℝ))
          (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)) =
        (q j : ℝ) • matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    (coefficientArrayFunctional U frequency).comp (coefficientSiteResidual U site q T) = 0 ↔
      ∀ j, ∃ M : (S → U j) →ₗ[ℝ] ℝ,
        ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
          coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
            M (siteEvaluation (fun s k => (site s k : ℝ)) p) := by
  rw [coefficientSiteResidual, coefficientArrayFunctional_endomorphism_zero_iff]
  constructor
  · intro h j
    obtain ⟨M, hM⟩ := (scaledLinearResidual_factor_iff _ _
      (show (q j : ℝ) ≠ 0 by exact_mod_cast (hq j).ne') (hT j) _).mp (h j)
    refine ⟨M, ?_⟩
    intro p hp
    have he := DFunLike.congr_fun hM (fun d => coefficients p d.val)
    have hr := boundedArrayPolynomial_reconstruct p hp
    rw [← hr, coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial]
    exact he
  · intro h j
    obtain ⟨M, hM⟩ := h j
    apply (scaledLinearResidual_factor_iff _ _
      (show (q j : ℝ) ≠ 0 by exact_mod_cast (hq j).ne') (hT j) _).mpr
    refine ⟨M, ?_⟩
    apply LinearMap.ext
    intro x
    exact bounded_site_factorization_to_array (U j) (j.val + 1) site _ M hM x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem coefficientTorusFourierSum_integral {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, coefficientTorusFourierSum U frequency c x ∂μ) =
      ∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0 := by
  change (∫ x, ∑ a, c a * coefficientTorusCharacter U (frequency a) x ∂μ) = _
  rw [integral_finsetSum _ (fun a _ => (coefficientTorusCharacter_integrable U (frequency a) μ).const_mul (c a))]
  simp only [integral_const_mul, coefficientTorusCharacter_integral]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem not_affineCubeModeFactors_iff {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    ¬affineCubeModeFactors U root difference frequency ↔
      ∃ j, ¬∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
        ∀ P, Homogeneous (j.val + 1) P →
          affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
            (map (U j).subtype P) = M (VectorPolynomial.siteEvaluation
              (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P) := by
  classical
  simp only [affineCubeModeFactors, not_forall]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientCoverTilt
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem affineSampleCoefficientArray_smul {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (r : ℝ) (b : Option K → I → ℝ) :
    affineSampleCoefficientArray U (fun j => r • p j)
      (fun j => coefficients_smul_mem (U j) (p j) (hm j) r) b =
      r • affineSampleCoefficientArray U p hm b := by
  funext s
  apply Subtype.ext
  change (affineSampleCoefficientArray U (fun j => r • p j) _ b s).val =
    r • (affineSampleCoefficientArray U p hm b s).val
  rw [affineSampleCoefficientArray_val, affineSampleCoefficientArray_val]
  simp only [map_smul, Finsupp.smul_apply]

noncomputable def affineCoefficientCoverSample {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (b : Option K → I → ℝ) : CoefficientTorus (K := K) U :=
  QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • affineSampleCoefficientArray U p hm b)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubePositiveComparison
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped Classical

theorem affineCubeModeFactors_iff_bounded {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    affineCubeModeFactors U root difference frequency ↔
      ∀ j, ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
        ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
          coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
            M (VectorPolynomial.siteEvaluation (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p) := by
  constructor
  · exact affineCubeModeFactors_bounded U root difference frequency
  · intro h j
    obtain ⟨M, hM⟩ := h j
    refine ⟨M, ?_⟩
    let L := (coefficientFunctional (fun d a => (frequency j d a : ℝ))).comp (map (U j).subtype)
    have hh := (homogeneous_site_factorization_iff (j.val + 1)
      (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) L M).mpr hM
    change ∀ p, Homogeneous (j.val + 1) p → affineModeLift L p = _ at hh
    have he : (fun s (k : Option K) => k.elim (1 : ℝ)
        (fun k => ((affineSite root difference s (some k) : ℤ) : ℝ))) =
        (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) := by
      funext s k
      cases k <;> simp [affineSite, Int.cast_sum]
    simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply, he] using hh

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

variable {K : Type*} [Fintype K] {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
  (U : ∀ j, Submodule ℝ (J j → ℝ))
  (R : CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U)
  (hR : ∀ x ∈ coefficientIntegerLattice U, R x ∈ coefficientIntegerLattice U)
  [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem coefficientTorusFourierSum_residualAverage {F : Type*} [Fintype F]
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hfactor : ∀ frequency : ∀ j, (K →₀ ℕ) → J j → ℤ,
      (coefficientArrayFunctional U frequency).comp R = 0 ↔ affineCubeModeFactors U root difference frequency)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (x : CoefficientTorus (K := K) U) :
    linearQuotientAverage (coefficientIntegerLattice U) R hR μ (coefficientTorusFourierSum U frequency c) x =
      ∑ a, if affineCubeModeFactors U root difference (frequency a) then
        c a * coefficientTorusCharacter U (frequency a) x else 0 := by
  have hi (a : F) := coefficientResidual_section_integrable U R hR μ
    (coefficientTorusCharacter U (frequency a))
    (quotientLinearCharacter_continuous _ _ _ (coefficientArrayFunctional U (frequency a)).continuous_of_finiteDimensional)
    (fun x => (quotientLinearCharacter_norm _ _ _ x).le) x
  change (∫ y, ∑ a, c a * coefficientTorusCharacter U (frequency a)
    (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y) ∂μ) = _
  rw [integral_finsetSum _ (fun a _ => (hi a).const_mul (c a))]
  simp only [integral_const_mul]
  change (∑ a, c a * linearQuotientAverage (coefficientIntegerLattice U) R hR μ
    (quotientLinearCharacter (coefficientIntegerLattice U) (coefficientArrayFunctional U (frequency a))
      (coefficientArrayFunctional_integral U (frequency a))) x) = _
  simp only [linearQuotientAverage_character, hfactor, mul_ite, mul_zero]
  rfl

theorem coefficientTorusFourierProjection_approx_residualAverage {F : Type*} [Fintype F]
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hfactor : ∀ frequency : ∀ j, (K →₀ ℕ) → J j → ℤ,
      (coefficientArrayFunctional U frequency).comp R = 0 ↔ affineCubeModeFactors U root difference frequency)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η : ℝ}
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (x : CoefficientTorus (K := K) U)
    (hD : Integrable (fun y => D (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) μ) :
    ‖(∑ a, if affineCubeModeFactors U root difference (frequency a) then
        c a * coefficientTorusCharacter U (frequency a) x else 0) -
      ((linearQuotientAverage (coefficientIntegerLattice U) R hR μ D x : ℝ) : ℂ)‖ ≤ η := by
  rw [← coefficientTorusFourierSum_residualAverage U R hR root difference hfactor frequency c μ x]
  have hi : Integrable (fun y => coefficientTorusFourierSum U frequency c
      (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) μ := by
    apply integrable_finsetSum
    intro a _
    apply Integrable.const_mul
    exact coefficientResidual_section_integrable U R hR μ (coefficientTorusCharacter U (frequency a))
      (quotientLinearCharacter_continuous _ _ _ (coefficientArrayFunctional U (frequency a)).continuous_of_finiteDimensional)
      (fun x => (quotientLinearCharacter_norm _ _ _ x).le) x
  have he := linearQuotientAverage_approx (coefficientIntegerLattice U) R hR μ
    (coefficientTorusFourierSum U frequency c) (fun x => (D x : ℂ)) happrox x hi hD.ofReal
  simpa only [linearQuotientAverage, integral_complex_ofReal] using he

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem shiftedSmoothProductMass_pos_of_scales {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ S i) :
    0 < shiftedSmoothProductMass a S := by
  rw [shiftedSmoothProductMass_eq_prod a S (fun i => smoothSamplingScale_pos (hS i))]
  exact Finset.prod_pos (fun i _ => shiftedSmoothSampleSum_pos (a i) (hS i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateProductCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem shiftedSmoothProductPMF_coordinate_cap {D Y : Type*} [Fintype D] [DecidableEq D]
    (a S : D → ℝ) (hS : ∀ d, 0 < S d) (hZ : 0 < shiftedSmoothProductMass a S)
    (j : D) (f : (D → ℤ) → Y)
    (hf : ∀ tail, Function.Injective (fun x => f (coordinateJoin j tail x)))
    (hscale : 8*(probabilityProfileLipschitz : ℝ) ≤ S j) (y : Y) :
    ((shiftedSmoothProductPMF a S hS hZ).map f y).toReal ≤ 2/S j := by
  rw [shiftedSmoothProductPMF_eq_independent]
  exact independentProductPMF_coordinate_cap _ j f hf (div_nonneg (by norm_num) (hS j).le)
    (fun x => shiftedSmoothCoefficientPMF_le (a j) hscale x) y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueLinearPointCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueSmoothPMF_linear_cap {K I : Type*} [Fintype K] [Fintype I]
    (c residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus) (residueProfileWidth modulus W))
    (j : K × I) (hc : c j ≠ 0)
    (hscale : 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W j) (y : ℤ) :
    ((residueSmoothPMF residue modulus hmodulus W hW hZ).map (integerArrayLinearForm c) y).toReal ≤
      2*(modulus j.2 : ℝ)/W j := by
  rw [residueSmoothPMF, PMF.map_comp, residueSmoothIndexPMF]
  have hq : (modulus j.2 : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hmodulus j.2))
  have h := shiftedSmoothProductPMF_coordinate_cap (residueProfileCenter residue modulus)
    (residueProfileWidth modulus W) (residueProfileWidth_pos modulus W hmodulus hW) hZ j
    (integerArrayLinearForm c ∘ residueLatticeArray residue modulus)
    (integerArrayLinearForm_pivot_injective c residue (fun d => (modulus d.2 : ℤ)) j hc hq)
    hscale y
  simpa only [residueProfileWidth, div_div_eq_mul_div] using h

theorem selectedResidueSmoothPMF_linear_cap {K I : Type*} [Fintype K] [Fintype I]
    (c : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern K I modulus)) (hT : T.Nonempty)
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    (j : K × I) (hc : c j ≠ 0) (y : ℤ) :
    ((selectedResidueSmoothPMF modulus T W hW hZ).map (integerArrayLinearForm c) y).toReal ≤
      2*(modulus j.2 : ℝ)/W j := by
  have hcell (r : T) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus W) := shiftedSmoothProductMass_pos_of_scales _ _ hscale
  obtain ⟨_, h⟩ := selectedResidueSmoothPMF_bound_of_cells (ε := 2*(modulus j.2 : ℝ)/W j)
    modulus hmodulus T hT W hW hcell
    (fun z => if integerArrayLinearForm c z = y then (1 : ℂ) else 0)
    (by
      intro r
      exact (pmf_point_indicator_norm _ (integerArrayLinearForm c) y).trans_le
        (residueSmoothPMF_linear_cap c (columnResidueRepresentative modulus r.val)
          modulus hmodulus W hW (hcell r) j hc (hscale j) y))
  exact (pmf_point_indicator_norm _ (integerArrayLinearForm c) y).symm.trans_le h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueCenterMix
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem selectedResidueDensityPMF_normalizedDensityTest {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus T W D) (f : (K × I → ℤ) → ℂ) :
    (∑' z, ((selectedResidueDensityPMF modulus T W hW hZ D hD0 hD z).toReal : ℂ)*f z) =
      (selectedResidueFiniteLaw modulus T W hW hZ).normalizedDensityTest
        (fun z => D z.val) (fun z => f z.val) := by
  rw [selectedResidueDensityPMF_complexMean, FiniteProbabilityWeights.normalizedDensityTest,
    selectedResidueFiniteLaw_densityMass,
    selectedResidueFiniteLaw_complexMean modulus T W hW hZ (fun z => (D z : ℂ)*f z)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

theorem jointIntegerPhysicalSite_mem_box {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (N R : I → ℕ) (hR : ∀ i, 2 * R i ≤ N i)
    (W : Option K × I → ℝ) (hwidth : ∀ i, physicalSiteWidth root W i ≤ (R i : ℝ))
    (z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) :
    jointIntegerPhysicalSite root (z.1.val, z.2.val) ∈ integerBox N := by
  apply trimmedIntegerBox_add_mem N R hR z.1.property
  intro i
  have h := (integerPhysicalSite_abs_bound root W z.2.val
    (rectangularWeightIndices_zero_bound W z.2.property) i).trans (hwidth i)
  exact_mod_cast h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedResidue_site_collision_le {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (r s : K → ℤ) (k : K) (hk : r k ≠ s k) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z) :
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0) ≤
        2*(modulus i : ℝ)/W (some k,i) := by
  let c := rowDifferenceCoefficients r s i
  have hc : c (some k,i) ≠ 0 := by
    simpa [c, rowDifferenceCoefficients] using sub_ne_zero.mpr hk
  have hp := selectedResidueSmoothPMF_linear_cap c modulus hmodulus T hT W hW hZ hscale (some k,i) hc 0
  have he : (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerArrayLinearForm c z.val = 0 then 1 else 0) ≤
        2*(modulus i : ℝ)/W (some k,i) :=
    (selectedResidueFiniteLaw_mean modulus T W hW hZ
      (fun z => if integerArrayLinearForm c z = 0 then 1 else 0)).trans_le
      ((pmf_map_toReal_indicator _ (integerArrayLinearForm c) 0).symm.trans_le hp)
  refine le_trans ((selectedResidueFiniteLaw modulus T W hW hZ).mean_mono ?_) he
  intro z
  by_cases h : integerPhysicalSite r z.val = integerPhysicalSite s z.val
  · have hz : integerArrayLinearForm c z.val = 0 := by
      rw [rowDifferenceCoefficients_linear, congrFun h i, sub_self]
    simp only [if_pos h, if_pos hz, le_refl]
  · simp only [if_neg h]
    split_ifs <;> norm_num

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedResidue_distinct_collision_le {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (r s : K → ℤ) (hrs : r ≠ s) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i)) :
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0) ≤
        2*(modulus i : ℝ)/L := by
  have hdiff : ∃ k, r k ≠ s k := by
    by_contra h
    apply hrs
    funext k
    by_contra hk
    exact h ⟨k,hk⟩
  obtain ⟨k,hk⟩ := hdiff
  exact (selectedResidue_site_collision_le r s k hk i modulus hmodulus T hT W hW hZ hscale).trans
    (div_le_div_of_nonneg_left (by positivity) hL (hwidth k))

end Erdos3.BooleanCubeKernel

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

noncomputable def height (q : ℤ) : ℕ := ⌈rationalLogHeight (q : ℚ)⌉₊

end Erdos3.DilationBudget

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConstantCenterUniformLifts
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {X Y R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def subtractConstant (c : V) (p : VectorPolynomial X R V) :
    VectorPolynomial X R V := p - monomial 0 c

theorem eval_subtractConstant (c : V) (p : VectorPolynomial X R V) (x : X → R) :
    eval x (subtractConstant c p) = eval x p - c := by
  simp [subtractConstant]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def ProductBoundedMarginals (f : (∀ i, X i) → ℝ) (K : ℝ) (r : ℕ) : Prop :=
  ∀ J : Finset I, J.card ≤ r → ∀ x : ∀ i, X i,
    (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      productConditionalMean μ J f x ≤ K ^ J.card

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

noncomputable def normalizedSection (c : ProductCylinder X) (x : ∀ i, X i) : ℝ :=
  (c.mass μ base f)⁻¹ * productSectionAverage μ c.1 c.1 (c.assignment base) f x

end Erdos3.ProductCylinder

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem standardPhysicalJetMap_measurePreserving :
    MeasurePreserving (standardPhysicalJetMap (q := q) U) μ
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))) := by
  have hperiod : integerScalarLattice (Fin q) (1 : ℤ) ≤
      (1 : Matrix (Fin q) (Fin q) ℤ).mulVecLin.range := by
    intro v _
    exact ⟨v, by simp⟩
  exact euclideanCoefficientJetMap_measurePreserving U (fun _ => 0)
    (1 : Matrix (Fin q) (Fin q) ℤ) 1 one_ne_zero hperiod
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    (fun _ => Subtype.val_injective) (fun _ s => s.property) μ ν

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3

inductive CylinderRemovalChain {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (K τ : ℝ) (j r : ℕ) :
    (Ω → ℝ) → (Ω → ℝ) → List (ProductCylinder X) → Prop where
  | nil (w : Ω → ℝ) : CylinderRemovalChain μ base p F K τ j r w w []
  | cons {w v : Ω → ℝ} {cs : List (ProductCylinder X)} (c : ProductCylinder X)
      (hsize : c.1.card ≤ j)
      (hmass : τ < c.mass μ base (observedProductDensity μ p F w))
      (hbounded : ProductBoundedMarginals μ
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F w) c) K r)
      (rest : CylinderRemovalChain μ base p F K τ j r (c.erase F w) v cs) :
      CylinderRemovalChain μ base p F K τ j r w v (c :: cs)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix NNReal

theorem exists_controlled_coordinate_lifts
    {μ ι κ σ V : Type*} [Fintype μ] [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (φ : V →ₗ[ℚ] (ι → ℚ))
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hφH : ∀ j i, RationalHeightLE (φ (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧ l ∣ m ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a q : ι → ℝ),
        a + q ∈ realRationalCoordinateSpan (U.map φ) →
        ‖a‖ ≤ Real.exp p / monomialScale T α → q ∈ realDenominatorGrid l →
        ∃ E Q : ℝ ⊗[ℚ] V, E ∈ U.baseChange ℝ ∧ Q ∈ U.baseChange ℝ ∧
          realRationalCoordinateEquiv (φ.baseChange ℝ E) = a ∧
          realRationalCoordinateEquiv (φ.baseChange ℝ Q) = q ∧
          ‖(b.baseChange ℝ).equivFun E‖ ≤
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m := by
  let A : Matrix ι κ ℚ := fun i j => φ (v j) i
  let B : Matrix μ κ ℚ := fun i j => b.repr (v j) i
  have hvφ : Submodule.span ℚ (Set.range (fun j => φ (v j))) = U.map φ := by
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hspan := realRationalCoordinateSpan_eq_image (U.map φ) (fun j => φ (v j)) hvφ
  have hvU (j : κ) : v j ∈ U := hv ▸ Submodule.subset_span (Set.mem_range_self j)
  obtain ⟨S, m, hm, hmp, hsolve⟩ := exists_controlled_linear_splitting A hH hl
    (fun i j => hφH j i) hp hι hκ hHp hlp T hT
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) := hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hden : (matrixDenominator B : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power B hp 1 hμ hκ
      (fun i j => (Nat.cast_le.mpr (hvH j i).2).trans hHp')
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hnorm (x : κ → ℝ) :
      ‖(fun i j => (B i j : ℝ)) *ᵥ x‖ ≤ Real.exp ((p + 2) ^ 3) * ‖x‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hvH j i).abs_real_le) x).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg x))
  have hBm : 0 < matrixDenominator B * m := Nat.mul_pos (matrixDenominator_pos B) hm
  have hBmp : ((matrixDenominator B * m : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) := by
    rw [Nat.cast_mul]
    exact (mul_le_mul hden hmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  refine ⟨l * (matrixDenominator B * m), Nat.mul_pos hl hBm, ?_, dvd_mul_right _ _, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hlp hBmp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  · intro α hα a q hsum ha hq
    rw [hspan] at hsum
    obtain ⟨x, hx⟩ := hsum
    obtain ⟨hSa, hSq, hslow, hgrid, _⟩ := hsolve α hα a q x ha hq hx
    let ca := (fun i j => (S i j : ℝ)) *ᵥ a
    let cq := (fun i j => (S i j : ℝ)) *ᵥ q
    refine ⟨realGeneratorCombination v ca, realGeneratorCombination v cq,
      realGeneratorCombination_mem U v hvU ca, realGeneratorCombination_mem U v hvU cq,
      ?_, ?_, ?_, ?_⟩
    · rw [realGeneratorCombination_map_coordinates]
      exact hSa
    · rw [realGeneratorCombination_map_coordinates]
      exact hSq
    · rw [realGeneratorCombination_coordinates]
      calc
        ‖(fun i j => (b.repr (v j) i : ℝ)) *ᵥ ca‖ ≤ Real.exp ((p + 2) ^ 3) * ‖ca‖ := hnorm ca
        _ ≤ Real.exp ((p + 2) ^ 3) * (Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
          mul_le_mul_of_nonneg_left hslow (Real.exp_pos _).le
        _ = _ := by rw [← mul_div_assoc, ← Real.exp_add]; congr 2; ring
    · rw [realGeneratorCombination_coordinates]
      exact realDenominatorGrid_subset_of_dvd hBm (dvd_mul_left _ _)
        (real_matrix_denominator_grid B m cq hgrid)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedCoordinateExtraction
namespace OAI

section

namespace Erdos3

structure CoordinateDerivativeSystem {σ : Type*} [Fintype σ] [DecidableEq σ] {m a : ℕ}
    (ha : a ≤ m)
    (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (scale : Fin m → ℝ) (bound : ℝ) where
  K : Submodule ℝ (Fin a → ℝ)
  k : ℕ
  heightBound : ℕ
  height_le : (heightBound : ℝ) ≤ bound
  basisMatrix : Matrix (Fin a) (Fin k) ℚ
  basis_height : ∀ i j, RationalHeightLE (basisMatrix i j) heightBound
  independent_rat : LinearIndependent ℚ basisMatrix.col
  independent_real : LinearIndependent ℝ (basisMatrix.map (Rat.castHom ℝ)).col
  span_eq : K = Submodule.span ℝ (Set.range (basisMatrix.map (Rat.castHom ℝ)).col)
  rationalLift : K →ₗ[ℝ] (Fin m → ℝ)
  geometricLift : K →ₗ[ℝ] (Fin m → ℝ)
  factorization : geometricLift = A.toLinearMap.comp rationalLift
  rational_horizontal : ∀ x i, rationalLift x (Fin.castLE ha i) = x.val i
  geometric_horizontal : ∀ x i, geometricLift x (Fin.castLE ha i) = x.val i
  norm_scaled : ∀ x,
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * geometricLift x j)‖ ≤ bound * ‖x‖
  liftDenominator : ℕ
  liftDenominator_pos : 0 < liftDenominator
  liftDenominator_le : (liftDenominator : ℝ) ≤ bound
  rational_on_basis : ∀ j, ∃ x : K,
    x.val = (basisMatrix.map (Rat.castHom ℝ)).col j ∧ rationalLift x ∈ realDenominatorGrid liftDenominator
  derivativeDenominator : ℕ
  derivativeDenominator_pos : 0 < derivativeDenominator
  derivativeDenominator_le : (derivativeDenominator : ℝ) ≤ bound
  slow : σ → Fin m → ℝ
  rational : σ → Fin m → ℝ
  horizontal : σ → K
  derivative_eq : ∀ i, Y (Pi.basisFun ℝ σ i) = slow i + A (rational i) + geometricLift (horizontal i)
  derivative_grid : ∀ i, rational i ∈ realDenominatorGrid derivativeDenominator
  slow_bound : ∀ i,
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * slow i j)‖ ≤ bound / T i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BoxNiltestDetection
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

def BoxNiltestDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {σ : Type v} [Fintype σ] [DecidableEq σ] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (p : ℝ),
    0 ≤ p → (Fintype.card σ : ℝ) ≤ p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
    ∀ (T : D.Niltest w), T.ComplexityLE p →
    ∀ (a : σ → ℤ) (lengths : σ → ℕ) [∀ i, NeZero (lengths i)] (f : (σ → ℤ) → ℂ),
    (∀ x ∈ translatedIntegerBox a lengths, ‖f x‖ ≤ 1) →
    Real.exp (-p) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f T.eval‖ →
    Real.exp (-F p) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a lengths) f

end Erdos3

end

end OAI
end


