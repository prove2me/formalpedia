-- Prove2me | Definitions.Def_OAIE3v2B044
-- name    : OAIE3v2B044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:12:52.650866+00:00
-- url     : https://prove2.me/theorems/0f0980dd-2f6b-4790-88b8-be0a844b2b07
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 45 of 311
-- statement:
--   Definitions bundle 45 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B006`, `OAIE3v2B007`, `OAIE3v2B008`, `OAIE3v2B009`, `OAIE3v2B010` of this split.
--
--   Modules: `Dynamics/CubeModeUniformBudget.lean`, `Dynamics/LayerRemovalBudgets.lean`, `Dynamics/ModeThresholdLogBudget.lean`, `Dynamics/MultiaffineBiasBudget.lean`, `Estimates/BooleanCubeModeWitness.lean`, `Estimates/CanonicalCoefficientCoverLift.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/MixedBooleanSiteValues.lean`, `Estimates/ModeRemovalThresholds.lean`, `Estimates/PartialComplexScaledQuadrature.lean`, `Estimates/PhysicalAmbientVolumeRatio.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Estimates/WeightedPatchReparam.lean`, `FixedDensity/Energy.lean`, `Fourier/CommonCoveredSiteCharacter.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/StandardJetFourier.lean`, `Geometry/AllocatedSpatialProxyCap.lean`, `Geometry/BoxChartCutoff.lean`, `Geometry/CoefficientJetCoordinates.lean`, `Lattices/AffineCubePositiveComparison.lean`, `Lattices/AffineResidualRecovery.lean`, `Lattices/CRTIntegerRepresentative.lean`, `Lattices/IntegerAffineResidues.lean`, `Lattices/IntegerBoxCoordinateEquiv.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/PrincipalResidueMixture.lean`, `Lattices/RectangularLatticeCells.lean`, `Lattices/RetainedAffineCommonCover.lean`, `Lattices/SelectedResidueApproximation.lean`, `Lattices/StandardLatticeCoordinates.lean`, `Linear/BooleanJetMatrixFactor.lean`, `Linear/CircleFejerKernel.lean`, `Linear/MatrixModuleAction.lean`, `Linear/ModeRankLogBudget.lean`, `Linear/WeightedPatchKernel.lean`, `Polynomial/BoundedRealPolynomialBasis.lean`, `Polynomial/FixedKernelPolynomialCover.lean`, `Polynomial/ModeLogPolynomials.lean`, `Probability/AllocatedReferenceJetMass.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B008
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RectangularLatticeCells
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def rectangularLatticeSample (a S x : J → ℝ) : J → ℝ :=
  rectangularLatticePoint a S (rectangularLatticeRound a S x)

def rectangularLatticeCell (a S : J → ℝ) (k : J → ℤ) : Set (J → ℝ) :=
  Set.univ.pi fun j => latticeSamplingCell (a j) (S j) (k j)

theorem rectangularLatticeCell_measurable (a S : J → ℝ) (k : J → ℤ) :
    MeasurableSet (rectangularLatticeCell a S k) :=
  MeasurableSet.univ_pi fun j => latticeSamplingCell_measurable (a j) (S j) (k j)

omit [Fintype J] in
theorem rectangularLatticeCell_iff (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (x : J → ℝ) (k : J → ℤ) :
    x ∈ rectangularLatticeCell a S k ↔ rectangularLatticeRound a S x = k := by
  simp only [rectangularLatticeCell, Set.mem_univ_pi, rectangularLatticeRound,
    funext_iff, latticeSamplingCell_iff (hS _)]

theorem rectangularLatticeCell_volume (a S : J → ℝ) (hS : ∀ j, 0 < S j) (k : J → ℤ) :
    volume.real (rectangularLatticeCell a S k) = (∏ j, S j)⁻¹ := by
  rw [measureReal_def, rectangularLatticeCell, volume_pi_pi, ENNReal.toReal_prod]
  change (∏ j, volume.real (latticeSamplingCell (a j) (S j) (k j))) = _
  simp only [latticeSamplingCell_volume (hS _), one_div, Finset.prod_inv_distrib]

theorem rectangularLatticeCell_volume_ne_top (a S : J → ℝ) (k : J → ℤ) :
    volume (rectangularLatticeCell a S k) ≠ ⊤ := by
  rw [rectangularLatticeCell, volume_pi_pi]
  apply ENNReal.prod_ne_top
  intro j _
  simp only [latticeSamplingCell, Real.volume_Ico, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]

theorem rectangularLatticeSample_error (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {δ : ℝ} (hδ : 0 ≤ δ) (hmesh : ∀ j, 1 / S j ≤ δ) (x : J → ℝ) :
    ‖rectangularLatticeSample a S x - x‖ ≤ δ := by
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro j
  exact (latticeSample_error (hS j) (x j)).trans (hmesh j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def trimmedIntegerBox (N R : I → ℕ) : Finset (I → ℤ) :=
  (integerBox (fun i => N i - 2 * R i)).image (fun x => (fun i => (R i : ℤ)) + x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MultiaffineBiasBudget
namespace OAI

section

namespace Erdos3

theorem multiaffineBiasBudget_eq_power (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    multiaffineBiasBudget n ζ =
      ((denseProductDensityConstant n : ℝ)*(2*3^n)^denseProductExponent n) /
        ζ^(2^n*(denseProductExponent n+1)) := by
  unfold multiaffineBiasBudget denseProductDensityBudget
  rw [div_pow, div_div, mul_add, mul_one, pow_add, pow_mul]
  field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_sum {α R B : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (b : Finset B) (f : B → Finset α → R) :
    booleanCoefficient (fun t => ∑ i ∈ b, f i t) s =
      ∑ i ∈ b, booleanCoefficient (f i) s := by
  simp only [booleanCoefficient, Finset.mul_sum]
  exact Finset.sum_comm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRealPolynomialBasis
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable instance boundedIntegerExponentFintype (K : Type*) [Fintype K] (h : ℕ) :
    Fintype (BoundedIntegerExponent K h) := by
  classical
  let f : BoundedIntegerExponent K h → List.Vector (Option K) h :=
    fun e => paddedExponentWord e.val h e.property
  apply Fintype.ofInjective f
  intro e d hed
  apply Subtype.ext
  apply Finsupp.ext
  intro k
  have hc := congrArg (fun v : List.Vector (Option K) h =>
    (v.val : Multiset (Option K)).count (some k)) hed
  simpa only [f, paddedExponentWord_count] using hc

theorem boundedIntegerPolynomial_expansion {K : Type*} [Fintype K]
    (p : MvPolynomial K ℤ) (h : ℕ) (hp : p.totalDegree ≤ h) :
    (∑ e : BoundedIntegerExponent K h,
      MvPolynomial.C (p.coeff e.val) * MvPolynomial.monomial e.val 1) = p := by
  classical
  simp only [MvPolynomial.C_mul_monomial, mul_one]
  ext m
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m.sum (fun _ n => n) ≤ h
  · let e : BoundedIntegerExponent K h := ⟨m, hm⟩
    rw [Finset.sum_eq_single e]
    · simp [e, MvPolynomial.coeff_monomial]
    · intro d _ hde
      have hdm : d.val ≠ m := fun heq => hde (Subtype.ext heq)
      simp [MvPolynomial.coeff_monomial, hdm]
    · simp
  · have hzero : p.coeff m = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      intro hmem
      exact hm ((MvPolynomial.le_totalDegree hmem).trans hp)
    rw [hzero]
    apply Finset.sum_eq_zero
    intro e _
    have hem : e.val ≠ m := fun heq => hm (heq ▸ e.property)
    simp [MvPolynomial.coeff_monomial, hem]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineResidues
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def integerJetMatrix {α K O J : Type*} [DecidableEq α]
    (basis : J → MvPolynomial K ℤ) (vertices : Finset α → K → ℤ)
    (rows : O → Finset α) : Matrix O J ℤ :=
  fun o j => booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (basis j)) (rows o)

theorem integerJetMatrix_apply_coefficients {α K O J : Type*} [DecidableEq α] [Fintype J]
    (basis : J → MvPolynomial K ℤ) (vertices : Finset α → K → ℤ)
    (rows : O → Finset α) (c : J → ℤ) (o : O) :
    (integerJetMatrix basis vertices rows *ᵥ c) o =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
        (∑ j, MvPolynomial.C (c j) * basis j)) (rows o) := by
  simp only [map_sum, map_mul, MvPolynomial.eval_C,
    booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, integerJetMatrix basis vertices rows o j * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerBooleanInterpolant_jet {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (vertices : Finset α → K → ℤ)
    (hq : ∀ r t, MvPolynomial.eval (vertices t) (q r) = if r ∈ t then a else 0)
    (row : Finset α) :
    booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
      (integerBooleanInterpolant q a h s)) row = if row = s then a ^ h else 0 := by
  simp_rw [integerBooleanInterpolant_eval q a h s hs vertices hq]
  rw [booleanCoefficient_const_mul, booleanCoefficient_monomial]
  split_ifs <;> simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerAffineNumerator_eval {α K : Type*} [Fintype K]
    (root n : K → ℤ) (difference : α → K → ℤ) (t : Finset α) :
    MvPolynomial.eval (integerAffineCube root difference t) (integerAffineNumerator root n) =
      ∑ r ∈ t, ∑ k, n k * difference r k := by
  simp only [integerAffineNumerator, map_sum, map_mul, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X, integerAffineCube, add_sub_cancel_left,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem integerAffineNumerator_boolean {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (difference : α → K → ℤ) (n : α → K → ℤ) (a : ℤ)
    (hdual : ∀ r s, (∑ k, n r k * difference s k) = if r = s then a else 0)
    (r : α) (t : Finset α) :
    MvPolynomial.eval (integerAffineCube root difference t) (integerAffineNumerator root (n r)) =
      if r ∈ t then a else 0 := by
  rw [integerAffineNumerator_eval]
  simp only [hdual, Finset.sum_ite_eq]

theorem integerAffine_interpolation {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (difference : α → K → ℤ) (n : α → K → ℤ) (a : ℤ)
    (hdual : ∀ r s, (∑ k, n r k * difference s k) = if r = s then a else 0)
    (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    ∃ p : MvPolynomial K ℤ, p.totalDegree ≤ h ∧ ∀ row : Finset α,
      booleanCoefficient (fun t => MvPolynomial.eval (integerAffineCube root difference t) p) row =
        if row = s then a ^ h else 0 := by
  let q := fun r => integerAffineNumerator root (n r)
  refine ⟨integerBooleanInterpolant q a h s,
    integerBooleanInterpolant_degree q a h s hs (fun r _ => integerAffineNumerator_degree root (n r)), ?_⟩
  exact integerBooleanInterpolant_jet q a h s hs (integerAffineCube root difference)
    (integerAffineNumerator_boolean root difference n a hdual)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem exists_integer_kernel_dual {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
    (D : Matrix α K ℤ) (a : ℤ) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range) :
    ∃ n : α → K → ℤ, ∀ r s, (∑ k, n r k * D s k) = if r = s then a else 0 := by
  have hex (r : α) : ∃ n : K → ℤ, D *ᵥ n = a • Pi.single r 1 :=
    hperiod ((integerScalarLattice_mem a _).mpr ⟨Pi.single r 1, rfl⟩)
  choose n hn using hex
  refine ⟨n, fun r s => ?_⟩
  calc
    _ = (D *ᵥ n r) s := by simp [Matrix.mulVec, dotProduct, mul_comm]
    _ = (a • (Pi.single r 1 : α → ℤ)) s := congrFun (hn r) s
    _ = _ := by
      by_cases hrs : r = s
      · subst s; simp
      · simp [hrs, Ne.symm hrs]

theorem integerKernel_interpolation {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
    (D : Matrix α K ℤ) (a : ℤ) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (root : K → ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    ∃ p : MvPolynomial K ℤ, p.totalDegree ≤ h ∧ ∀ row : Finset α,
      booleanCoefficient (fun t => MvPolynomial.eval (integerAffineCube root D t) p) row =
        if row = s then a ^ h else 0 := by
  obtain ⟨n, hn⟩ := exists_integer_kernel_dual D a hperiod
  exact integerAffine_interpolation root D n a hn h s hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def boundedDegreeIntegerJetMatrix {α K O : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α) :
    Matrix O (BoundedIntegerExponent K h) ℤ :=
  integerJetMatrix (fun e => MvPolynomial.monomial e.val 1) (integerAffineCube root D) rows

theorem boundedDegreeIntegerJetMatrix_period {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (h : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    integerScalarLattice O (a ^ h) ≤ (boundedDegreeIntegerJetMatrix root D h rows).mulVecLin.range := by
  classical
  have hex (o : O) := integerKernel_interpolation D a hperiod root h (rows o) (hdegree o)
  choose p hp hjet using hex
  let E := boundedDegreeIntegerJetMatrix root D h rows
  have hunit (o : O) : a ^ h • Pi.single o 1 ∈ E.mulVecLin.range := by
    let c : BoundedIntegerExponent K h → ℤ := fun e => (p o).coeff e.val
    refine ⟨c, ?_⟩
    ext r
    change (integerJetMatrix (fun e : BoundedIntegerExponent K h => MvPolynomial.monomial e.val 1)
      (integerAffineCube root D) rows *ᵥ c) r = _
    rw [integerJetMatrix_apply_coefficients]
    change booleanCoefficient (fun t => MvPolynomial.eval (integerAffineCube root D t)
      (∑ e : BoundedIntegerExponent K h, MvPolynomial.C ((p o).coeff e.val) *
        MvPolynomial.monomial e.val 1)) (rows r) = _
    rw [boundedIntegerPolynomial_expansion (p o) h (hp o), hjet o]
    by_cases hro : r = o
    · subst r; simp
    · simp [hinj.eq_iff, hro]
  rintro y ⟨z, rfl⟩
  change a ^ h • z ∈ E.mulVecLin.range
  have hs : (∑ o, z o • (a ^ h • Pi.single o 1)) ∈ E.mulVecLin.range :=
    E.mulVecLin.range.sum_mem (fun o _ => E.mulVecLin.range.smul_mem (z o) (hunit o))
  convert hs using 1
  ext r
  simp [Pi.single_apply, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def finiteRectangularHistogram (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (a S x : J → ℝ) : ℝ :=
  ∑ k ∈ s, (rectangularLatticeCell a S k).indicator (fun _ => w k) x

theorem rectangularLatticeCell_indicator_integrable (a S : J → ℝ) (k : J → ℤ) (v : ℝ) :
    Integrable ((rectangularLatticeCell a S k).indicator (fun _ => v)) :=
  (integrableOn_const (rectangularLatticeCell_volume_ne_top a S k)).integrable_indicator
    (rectangularLatticeCell_measurable a S k)

theorem finiteRectangularHistogram_integrable (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (a S : J → ℝ) : Integrable (finiteRectangularHistogram s w a S) := by
  apply integrable_finsetSum
  intro k _
  exact rectangularLatticeCell_indicator_integrable a S k (w k)

theorem finiteRectangularHistogram_integral (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (∫ x, finiteRectangularHistogram s w a S x) = (∑ k ∈ s, w k) / (∏ j, S j) := by
  unfold finiteRectangularHistogram
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (rectangularLatticeCell_measurable a S _),
      rectangularLatticeCell_volume a S hS, smul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  · intro k _
    exact rectangularLatticeCell_indicator_integrable a S k (w k)

omit [Fintype J] in
theorem finiteRectangularHistogram_eq_round (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (hw : ∀ k, k ∉ s → w k = 0) (a S : J → ℝ) (hS : ∀ j, 0 < S j) (x : J → ℝ) :
    finiteRectangularHistogram s w a S x = w (rectangularLatticeRound a S x) := by
  classical
  unfold finiteRectangularHistogram
  rw [Finset.sum_eq_single (rectangularLatticeRound a S x)]
  · exact Set.indicator_of_mem ((rectangularLatticeCell_iff a S hS x _).mpr rfl) _
  · intro k _ hne
    apply Set.indicator_of_notMem
    intro hk
    exact hne ((rectangularLatticeCell_iff a S hS x k).mp hk).symm
  · intro hn
    rw [hw _ hn]
    simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxChartCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem lipschitz_coordinateBoxCutoff {ι : Type*} [Fintype ι] (χ : ℝ → ℝ) (A r : ℝ≥0)
    (hr : 0 < r) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hLip : LipschitzWith A χ) :
    LipschitzWith (Fintype.card ι * A / r) (coordinateBoxCutoff (ι := ι) χ r) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have hr' : (0 : ℝ) < r := hr
  have hcoord (i) : |v i - w i| ≤ dist v w := by
    simpa only [Real.dist_eq] using dist_le_pi_dist v w i
  have hd (i) : |χ (v i / r) - χ (w i / r)| ≤ ((A : ℝ) / r) * dist v w := by
    have h := hLip.dist_le_mul (v i / r) (w i / r)
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hr'] at h
    apply h.trans
    calc
      (A : ℝ) * (|v i - w i| / r) = ((A : ℝ) / r) * |v i - w i| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcoord i) (by positivity)
  have hprod := abs_finset_prod_sub_prod_le Finset.univ (fun i => χ (v i / r))
    (fun i => χ (w i / r)) (B := 1) (δ := ((A : ℝ) / r) * dist v w) le_rfl (by positivity)
    (fun i _ => by rw [abs_of_nonneg (hχ _).1]; exact (hχ _).2)
    (fun i _ => by rw [abs_of_nonneg (hχ _).1]; exact (hχ _).2) (fun i _ => hd i)
  rw [Real.dist_eq]
  apply hprod.trans_eq
  simp only [Finset.card_univ, one_pow, mul_one, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LayerRemovalBudgets
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteLayerBiasBudget (m : ℕ) (ζ : ℝ) : ℝ :=
  1 + ∑ i : Fin m, multiaffineBiasBudget i.val ζ

theorem finiteLayerBiasBudget_one_le (m : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    1 ≤ finiteLayerBiasBudget m ζ := by
  unfold finiteLayerBiasBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (multiaffineBiasBudget_pos i.val hζ).le))

theorem multiaffineBiasBudget_le_finite {m : ℕ} (i : Fin m) {ζ : ℝ} (hζ : 0 < ζ) :
    multiaffineBiasBudget i.val ζ ≤ finiteLayerBiasBudget m ζ := by
  apply le_trans (Finset.single_le_sum (fun j _ => (multiaffineBiasBudget_pos j.val hζ).le)
    (Finset.mem_univ i))
  exact le_add_of_nonneg_left zero_le_one

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residueProfile_point {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) (x : K × I → ℤ) :
    rectangularLatticePoint (residueProfileCenter residue modulus) (residueProfileWidth modulus V) x =
      fun z => (residueLatticeArray residue modulus x z : ℝ) / V z := by
  funext z
  have hm : (0 : ℝ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  simp only [rectangularLatticePoint, residueProfileCenter, residueProfileWidth,
    residueLatticeArray, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  field_simp [hm.ne', (hV z).ne']
  ring

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeArray_injective {K I : Type*}
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j) :
    Function.Injective (residueLatticeArray residue modulus) := by
  intro x y he
  funext z
  have hm : (modulus z.2 : ℤ) ≠ 0 := by exact_mod_cast (hmodulus z.2).ne'
  exact mul_left_cancel₀ hm (add_left_cancel (congrFun he z))

theorem residueLatticeArray_range {K I : Type*}
    (residue : K × I → ℤ) (modulus : I → ℕ) (y : K × I → ℤ) :
    y ∈ Set.range (residueLatticeArray residue modulus) ↔
      ∀ z, (modulus z.2 : ℤ) ∣ y z - residue z := by
  constructor
  · rintro ⟨x, rfl⟩ z
    exact ⟨x z, by simp only [residueLatticeArray, add_sub_cancel_left]⟩
  · intro h
    classical
    refine ⟨fun z => (h z).choose, ?_⟩
    funext z
    have hz := (h z).choose_spec
    change residue z + (modulus z.2 : ℤ) * (h z).choose = y z
    omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CircleFejerKernel
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real
open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

def fejerFrequencies (N : ℕ) : Finset ℤ := by
  classical
  exact (Finset.univ : Finset (Fin N × Fin N)).image fejerPairFrequency

end
end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {I : Type*}

def lieTreeMarkedCount (marked : I → Bool) (a : FreeMagma I) : ℕ :=
  lieTreeWeight (fun i => if marked i then 1 else 0) a

@[simp] theorem lieTreeMarkedCount_leaf (marked : I → Bool) (i : I) :
    lieTreeMarkedCount marked (.of i) = if marked i then 1 else 0 := rfl

@[simp] theorem lieTreeMarkedCount_mul (marked : I → Bool) (a b : FreeMagma I) :
    lieTreeMarkedCount marked (a * b) =
      lieTreeMarkedCount marked a + lieTreeMarkedCount marked b := rfl

end Erdos3

end

section

namespace Erdos3

variable {I σ : Type*}

noncomputable def lieTreeMultidegree (g : I → σ →₀ ℕ) : FreeMagma I → σ →₀ ℕ
  | .of i => g i
  | .mul a b => lieTreeMultidegree g a + lieTreeMultidegree g b

@[simp] theorem lieTreeMultidegree_leaf (g : I → σ →₀ ℕ) (i : I) :
    lieTreeMultidegree g (.of i) = g i := rfl

@[simp] theorem lieTreeMultidegree_mul (g : I → σ →₀ ℕ) (a b : FreeMagma I) :
    lieTreeMultidegree g (a * b) = lieTreeMultidegree g a + lieTreeMultidegree g b := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModeRemovalThresholds
namespace OAI

section

namespace Erdos3

noncomputable def modeRemovalTranslationConstant (d : ℕ) : ℝ :=
  4 * (3 : ℝ) ^ d * ((d : ℝ) * probabilityProfileLipschitz)

noncomputable def modeRemovalMeshConstant (d : ℕ) : ℝ :=
  (4 : ℝ) ^ d * ((d : ℝ) * probabilityProfileLipschitz)

theorem modeRemovalTranslationConstant_nonneg (d : ℕ) : 0 ≤ modeRemovalTranslationConstant d := by
  unfold modeRemovalTranslationConstant
  positivity

theorem modeRemovalMeshConstant_nonneg (d : ℕ) : 0 ≤ modeRemovalMeshConstant d := by
  unfold modeRemovalMeshConstant
  positivity

noncomputable def modeRemovalRadius (d : ℕ) (ε : ℝ) : ℝ :=
  ε / (2 * (modeRemovalTranslationConstant d + 1))

theorem modeRemovalRadius_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < modeRemovalRadius d ε := by
  have hc := modeRemovalTranslationConstant_nonneg d
  unfold modeRemovalRadius
  positivity

theorem modeRemovalError_bound (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    modeRemovalTranslationConstant d * modeRemovalRadius d ε + modeRemovalBeta ε ≤ ε := by
  have hc := modeRemovalTranslationConstant_nonneg d
  have hr := (modeRemovalRadius_pos d hε).le
  have hd : modeRemovalTranslationConstant d + 1 ≠ 0 := by positivity
  have he : (modeRemovalTranslationConstant d + 1) * modeRemovalRadius d ε = ε / 2 := by
    unfold modeRemovalRadius
    field_simp
  have hb : modeRemovalBeta ε ≤ ε / 2 := min_le_right _ _
  nlinarith

noncomputable def modeRemovalMesh (d : ℕ) : ℝ := 1 / (2 * (modeRemovalMeshConstant d + 1))

theorem modeRemovalMesh_pos (d : ℕ) : 0 < modeRemovalMesh d := by
  have hc := modeRemovalMeshConstant_nonneg d
  unfold modeRemovalMesh
  positivity

theorem modeRemovalMesh_le_one (d : ℕ) : modeRemovalMesh d ≤ 1 := by
  have hc := modeRemovalMeshConstant_nonneg d
  apply (div_le_iff₀ (by positivity : 0 < 2 * (modeRemovalMeshConstant d + 1))).mpr
  linarith

theorem modeRemovalMesh_small (d : ℕ) :
    modeRemovalMeshConstant d * modeRemovalMesh d ≤ 1 / 2 := by
  have hc := modeRemovalMeshConstant_nonneg d
  have hd : modeRemovalMeshConstant d + 1 ≠ 0 := by positivity
  have he : (modeRemovalMeshConstant d + 1) * modeRemovalMesh d = 1 / 2 := by
    unfold modeRemovalMesh
    field_simp
  nlinarith [modeRemovalMesh_pos d]

theorem modeRemovalMesh_of_width (d : ℕ) {V : ℝ} (hV : 0 < V)
    (hwidth : 1 / modeRemovalMesh d ≤ V) : 1 ≤ V ∧ 1 / V ≤ modeRemovalMesh d := by
  have hm := (div_le_iff₀ (modeRemovalMesh_pos d)).mp hwidth
  have hmul := mul_le_mul_of_nonneg_left (modeRemovalMesh_le_one d) hV.le
  constructor
  · nlinarith
  · apply (div_le_iff₀ hV).mpr
    nlinarith

end Erdos3

end

section

namespace Erdos3

noncomputable def modeRemovalShrink (m d : ℕ) (D ρ ε : ℝ) : ℝ :=
  1 + (m : ℝ) * D / (modeRemovalRadius d ε * ρ)

theorem modeRemovalShrink_one_le (m d : ℕ) {D ρ ε : ℝ}
    (hD : 0 ≤ D) (hρ : 0 < ρ) (hε : 0 < ε) : 1 ≤ modeRemovalShrink m d D ρ ε := by
  have hr := modeRemovalRadius_pos d hε
  unfold modeRemovalShrink
  exact le_add_of_nonneg_right (by positivity)

theorem modeRemovalShrink_move (m d : ℕ) {D ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) :
    (m : ℝ) * D ≤ modeRemovalRadius d ε * ρ * modeRemovalShrink m d D ρ ε := by
  have hr := modeRemovalRadius_pos d hε
  have hd : modeRemovalRadius d ε * ρ ≠ 0 := ne_of_gt (mul_pos hr hρ)
  unfold modeRemovalShrink
  rw [mul_add, mul_one, mul_div_cancel₀ _ hd]
  linarith [mul_pos hr hρ]

noncomputable def modeRemovalSideThreshold (m d : ℕ) (D S ρ ε : ℝ) : ℝ :=
  S * modeRemovalShrink m d D ρ ε * (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) +
    1 / (ρ * modeRemovalMesh d) + 1

noncomputable def modeRemovalRankThreshold (m n d : ℕ) (C D S ρ ε : ℝ) : ℝ :=
  layerRemovalRankBudget m n C D (finiteLayerBiasBudget m (modeRemovalBias m ε))
    (2 * modeRemovalShrink m d D ρ ε) S

theorem modeRemovalSideThreshold_bounds (m d : ℕ) {D S ρ ε : ℝ}
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε) :
    0 < modeRemovalSideThreshold m d D S ρ ε ∧
    S * modeRemovalShrink m d D ρ ε * (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) ≤
      modeRemovalSideThreshold m d D S ρ ε ∧
    1 / modeRemovalMesh d ≤ ρ * modeRemovalSideThreshold m d D S ρ ε := by
  have hT := modeRemovalShrink_one_le m d hD hρ hε
  have hB := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hδ := modeRemovalMesh_pos d
  have ha : 0 ≤ S * modeRemovalShrink m d D ρ ε *
      (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) := by positivity
  have hb : 0 < 1 / (ρ * modeRemovalMesh d) := by positivity
  have he : ρ * (1 / (ρ * modeRemovalMesh d)) = 1 / modeRemovalMesh d := by
    field_simp
  unfold modeRemovalSideThreshold
  refine ⟨by positivity, by linarith, ?_⟩
  nlinarith [mul_nonneg hρ.le ha]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget
namespace OAI

section

namespace Erdos3

noncomputable def modeProfileBound : ℕ := ⌈(probabilityProfileLipschitz : ℝ)⌉₊

noncomputable def modeProfileLog (P : ℝ) : ℝ := 5 * P + (modeProfileBound : ℝ) + 4

theorem modeProfileLog_nonneg {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeProfileLog P := by
  unfold modeProfileLog
  positivity

theorem modeRemovalConstants_le_exp (d : ℕ) {P : ℝ} (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) :
    modeRemovalTranslationConstant d ≤ Real.exp (modeProfileLog P) ∧
      modeRemovalMeshConstant d ≤ Real.exp (modeProfileLog P) := by
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hn : (d : ℝ) ≤ Real.exp P := hd.trans (by linarith [Real.add_one_le_exp P])
  have hL : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (modeProfileBound : ℝ) := by
    have hc : (probabilityProfileLipschitz : ℝ) ≤ modeProfileBound := Nat.le_ceil _
    exact hc.trans (by linarith [Real.add_one_le_exp (modeProfileBound : ℝ)])
  constructor
  · unfold modeRemovalTranslationConstant
    calc
      _ ≤ Real.exp 4 * (Real.exp 3) ^ d * (Real.exp P * Real.exp (modeProfileBound : ℝ)) := by gcongr
      _ = Real.exp (4 + 3 * (d : ℝ) + P + (modeProfileBound : ℝ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold modeProfileLog; nlinarith)
  · unfold modeRemovalMeshConstant
    calc
      _ ≤ (Real.exp 4) ^ d * (Real.exp P * Real.exp (modeProfileBound : ℝ)) := by gcongr
      _ = Real.exp (4 * (d : ℝ) + P + (modeProfileBound : ℝ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold modeProfileLog; linarith)

theorem modeRemovalMesh_inv_le_exp (d : ℕ) {P : ℝ} (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) :
    1 / modeRemovalMesh d ≤ Real.exp (modeProfileLog P + 3) := by
  have hc0 := modeRemovalMeshConstant_nonneg d
  have hc : modeRemovalMeshConstant d + 1 ≤ Real.exp (modeProfileLog P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (modeProfileLog_nonneg hP)
      (modeRemovalConstants_le_exp d hP hd).2
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  simp only [modeRemovalMesh, one_div, inv_inv]
  calc
    _ ≤ Real.exp 2 * Real.exp (modeProfileLog P + 1) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem modeRemovalRadius_inv_le_exp (d : ℕ) {P ε : ℝ}
    (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    1 / modeRemovalRadius d ε ≤ Real.exp (modeProfileLog P + P + 3) := by
  have hc0 := modeRemovalTranslationConstant_nonneg d
  have hc : modeRemovalTranslationConstant d + 1 ≤ Real.exp (modeProfileLog P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (modeProfileLog_nonneg hP)
      (modeRemovalConstants_le_exp d hP hd).1
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have he : 1 / modeRemovalRadius d ε = 2 * (modeRemovalTranslationConstant d + 1) * (1 / ε) := by
    rw [modeRemovalRadius, one_div, inv_div]
    simp only [div_eq_mul_inv, one_mul]
  rw [he]
  calc
    _ ≤ (Real.exp 2 * Real.exp (modeProfileLog P + 1)) * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def multiaffineInverseConstant (n : ℕ) : ℕ :=
  denseProductDensityConstant n * (2 * 3 ^ n) ^ denseProductExponent n

def multiaffineInverseExponent (n : ℕ) : ℕ := 2 ^ n * (denseProductExponent n + 1)

def finiteLayerInverseConstant (m : ℕ) : ℕ := m + 1 + ∑ i : Fin m, multiaffineInverseConstant i.val

def finiteLayerInverseExponent (m : ℕ) : ℕ := ∑ i : Fin m, multiaffineInverseExponent i.val

def finiteLayerInverseLog (m : ℕ) (Z : ℝ) : ℝ :=
  (finiteLayerInverseConstant m : ℝ) + (finiteLayerInverseExponent m : ℝ) * Z

theorem multiaffineBiasBudget_eq_inverse_power (n : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    multiaffineBiasBudget n ζ =
      (multiaffineInverseConstant n : ℝ) * (1 / ζ) ^ multiaffineInverseExponent n := by
  rw [multiaffineBiasBudget_eq_power n hζ]
  simp only [multiaffineInverseConstant, multiaffineInverseExponent,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, one_mul, inv_pow]

theorem multiaffineBiasBudget_le_exp (n : ℕ) {ζ Z : ℝ} (hζ : 0 < ζ)
    (hZ : 1 / ζ ≤ Real.exp Z) :
    multiaffineBiasBudget n ζ ≤ Real.exp
      ((multiaffineInverseConstant n : ℝ) + (multiaffineInverseExponent n : ℝ) * Z) := by
  have hc : (multiaffineInverseConstant n : ℝ) ≤ Real.exp (multiaffineInverseConstant n : ℝ) := by
    linarith [Real.add_one_le_exp (multiaffineInverseConstant n : ℝ)]
  rw [multiaffineBiasBudget_eq_inverse_power n hζ]
  calc
    _ ≤ Real.exp (multiaffineInverseConstant n : ℝ) *
        (Real.exp Z) ^ multiaffineInverseExponent n := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

theorem finiteLayerInverseLog_nonneg (m : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ finiteLayerInverseLog m Z := by unfold finiteLayerInverseLog; positivity

theorem finiteLayerBiasBudget_le_exp (m : ℕ) {ζ Z : ℝ} (hζ : 0 < ζ) (hZ : 0 ≤ Z)
    (hInv : 1 / ζ ≤ Real.exp Z) : finiteLayerBiasBudget m ζ ≤ Real.exp (finiteLayerInverseLog m Z) := by
  have hsum := sum_le_exp_card_add_sum
    (fun i : Fin m => multiaffineBiasBudget i.val ζ)
    (fun i : Fin m => (multiaffineInverseConstant i.val : ℝ) + (multiaffineInverseExponent i.val : ℝ) * Z)
    (fun _ => by positivity) (fun i => multiaffineBiasBudget_le_exp i.val hζ hInv)
  have hs0 : 0 ≤ (Fintype.card (Fin m) : ℝ) +
      ∑ i : Fin m, ((multiaffineInverseConstant i.val : ℝ) + (multiaffineInverseExponent i.val : ℝ) * Z) := by
    positivity
  have h := one_add_le_exp_succ hs0 hsum
  change 1 + ∑ i : Fin m, multiaffineBiasBudget i.val ζ ≤ _
  convert h using 1
  congr 1
  simp only [finiteLayerInverseLog, finiteLayerInverseConstant, finiteLayerInverseExponent,
    Nat.cast_add, Nat.cast_one, Nat.cast_sum, Fintype.card_fin, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  ring

theorem modeRemovalBeta_inv_le_exp {ε P : ℝ} (hP : 0 ≤ P) (hεInv : 1 / ε ≤ Real.exp P) :
    1 / modeRemovalBeta ε ≤ Real.exp (P + 2) := by
  have hEP : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hmin : (modeRemovalBeta ε)⁻¹ ≤ 2 * Real.exp P := by
    apply inv_min_le_of_inv_le
    · norm_num
      linarith
    · rw [inv_div]
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hεInv (by norm_num : (0 : ℝ) ≤ 2)
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 2 * Real.exp P := by simpa only [one_div] using hmin
    _ ≤ Real.exp 2 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem modeRemovalBias_inv_le_exp (m : ℕ) {ε P : ℝ}
    (hε : 0 < ε) (hP : 0 ≤ P) (hεInv : 1 / ε ≤ Real.exp P) :
    1 / modeRemovalBias m ε ≤ Real.exp (((2 ^ m : ℕ) : ℝ) * (P + 2)) := by
  have h := pow_le_pow_left₀ (div_nonneg zero_le_one (modeRemovalBeta_pos hε).le)
    (modeRemovalBeta_inv_le_exp hP hεInv) (2 ^ m)
  simpa only [modeRemovalBias, div_pow, one_pow, ← Real.exp_nat_mul] using h

end Erdos3

end

section

namespace Erdos3

noncomputable def modeBiasLog (m : ℕ) (P : ℝ) : ℝ :=
  finiteLayerInverseLog m (((2 ^ m : ℕ) : ℝ) * (P + 2))

noncomputable def modeShrinkLog (m : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) + modeProfileLog P + 3 * P + 4

noncomputable def modeSideLog (m : ℕ) (P : ℝ) : ℝ :=
  (P + modeShrinkLog m P + modeBiasLog m P + 1) + (P + modeProfileLog P + 3) + 2

theorem modeBiasLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeBiasLog m P :=
  finiteLayerInverseLog_nonneg m (by positivity)

theorem modeShrinkLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeShrinkLog m P := by
  have he := modeProfileLog_nonneg hP
  unfold modeShrinkLog
  positivity

theorem modeSideLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeSideLog m P := by
  have hb := modeBiasLog_nonneg m hP
  have ht := modeShrinkLog_nonneg m hP
  have he := modeProfileLog_nonneg hP
  unfold modeSideLog
  positivity

theorem chosenBiasBudget_le_exp (m : ℕ) {P ε : ℝ}
    (hP : 0 ≤ P) (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    finiteLayerBiasBudget m (modeRemovalBias m ε) ≤ Real.exp (modeBiasLog m P) :=
  finiteLayerBiasBudget_le_exp m (modeRemovalBias_pos m hε) (by positivity)
    (modeRemovalBias_inv_le_exp m hε hP hεInv)

theorem modeRemovalShrink_le_exp (m d : ℕ) {P D ρ ε : ℝ}
    (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hD : 0 ≤ D) (hDP : D ≤ Real.exp P)
    (hρ : 0 < ρ) (hρInv : 1 / ρ ≤ Real.exp P) (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    modeRemovalShrink m d D ρ ε ≤ Real.exp (modeShrinkLog m P) := by
  have hm : (m : ℝ) ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
  have hr := modeRemovalRadius_pos d hε
  have hrInv := modeRemovalRadius_inv_le_exp d hP hd hε hεInv
  have hE := modeProfileLog_nonneg hP
  have hprod : (m : ℝ) * D / (modeRemovalRadius d ε * ρ) ≤
      Real.exp ((m : ℝ) + modeProfileLog P + 3 * P + 3) := by
    calc
      _ = (m : ℝ) * D * (1 / modeRemovalRadius d ε) * (1 / ρ) := by
        simp only [div_eq_mul_inv, mul_inv, one_mul]
        ring
      _ ≤ Real.exp (m : ℝ) * Real.exp P * Real.exp (modeProfileLog P + P + 3) * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h := one_add_le_exp_succ (by positivity) hprod
  have he : ((m : ℝ) + modeProfileLog P + 3 * P + 3) + 1 = modeShrinkLog m P := by
    unfold modeShrinkLog
    ring
  simpa only [modeRemovalShrink, he] using h

theorem modeRemovalSideThreshold_le_exp (m d : ℕ) {P D S ρ ε : ℝ}
    (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hD : 0 ≤ D) (hDP : D ≤ Real.exp P)
    (_hS : 0 ≤ S) (hSP : S ≤ Real.exp P) (hρ : 0 < ρ) (hρInv : 1 / ρ ≤ Real.exp P)
    (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    modeRemovalSideThreshold m d D S ρ ε ≤ Real.exp (modeSideLog m P) := by
  have ht := modeRemovalShrink_le_exp m d hP hd hD hDP hρ hρInv hε hεInv
  have hT := modeRemovalShrink_one_le m d hD hρ hε
  have hb := chosenBiasBudget_le_exp m hP hε hεInv
  have hB := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hBlog := modeBiasLog_nonneg m hP
  have hTlog := modeShrinkLog_nonneg m hP
  have hE := modeProfileLog_nonneg hP
  have hb1 : finiteLayerBiasBudget m (modeRemovalBias m ε) + 1 ≤ Real.exp (modeBiasLog m P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ hBlog hb
  have ha : S * modeRemovalShrink m d D ρ ε * (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) ≤
      Real.exp (P + modeShrinkLog m P + modeBiasLog m P + 1) := by
    calc
      _ ≤ Real.exp P * Real.exp (modeShrinkLog m P) * Real.exp (modeBiasLog m P + 1) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hδ := modeRemovalMesh_pos d
  have hδInv := modeRemovalMesh_inv_le_exp d hP hd
  have hc : 1 / (ρ * modeRemovalMesh d) ≤ Real.exp (P + modeProfileLog P + 3) := by
    calc
      _ = (1 / ρ) * (1 / modeRemovalMesh d) := by ring
      _ ≤ Real.exp P * Real.exp (modeProfileLog P + 3) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum := add_le_exp_add_one (by positivity) (by positivity) ha hc
  have hout := one_add_le_exp_succ (by positivity) hsum
  convert hout using 1
  · unfold modeRemovalSideThreshold
    ring
  · congr 1
    unfold modeSideLog
    ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ModeRankLogBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def modeRankLog (m : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) + 1 + ∑ i : Fin m,
    ((((i.val + 1).factorial : ℝ) + P + (i.val + 1 : ℕ) * P) +
      P ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P) +
      ((i.val + 1 : ℕ) * P + (i.val + 1 : ℕ) * (modeShrinkLog m P + 2) + modeBiasLog m P) + 2)

theorem modeRankLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeRankLog m P := by
  have hb := modeBiasLog_nonneg m hP
  have ht := modeShrinkLog_nonneg m hP
  unfold modeRankLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ModeLogPolynomials
namespace OAI

section

namespace Erdos3

open Polynomial
open scoped BigOperators

noncomputable def modeProfileLogPolynomial : Polynomial ℕ := 5 * X + C modeProfileBound + 4

noncomputable def modeBiasLogPolynomial (m : ℕ) : Polynomial ℕ :=
  C (finiteLayerInverseConstant m) + C (finiteLayerInverseExponent m) * (C (2 ^ m) * (X + 2))

noncomputable def modeShrinkLogPolynomial (m : ℕ) : Polynomial ℕ :=
  C m + modeProfileLogPolynomial + 3 * X + 4

noncomputable def modeSideLogPolynomial (m : ℕ) : Polynomial ℕ :=
  (X + modeShrinkLogPolynomial m + modeBiasLogPolynomial m + 1) + (X + modeProfileLogPolynomial + 3) + 2

noncomputable def modeRankLogPolynomial (m : ℕ) : Polynomial ℕ :=
  C m + 1 + ∑ i : Fin m,
    ((C (i.val + 1).factorial + X + C (i.val + 1) * X) +
      X ^ (i.val + 1) * (modeBiasLogPolynomial m + C (i.val + 1) * X) +
      (C (i.val + 1) * X + C (i.val + 1) * (modeShrinkLogPolynomial m + 2) + modeBiasLogPolynomial m) + 2)

theorem modeProfileLogPolynomial_eval (P : ℝ) :
    modeProfileLogPolynomial.eval₂ (Nat.castRingHom ℝ) P = modeProfileLog P := by
  simp [modeProfileLogPolynomial, modeProfileLog]

theorem modeBiasLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeBiasLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeBiasLog m P := by
  simp [modeBiasLogPolynomial, modeBiasLog, finiteLayerInverseLog, Polynomial.eval₂_pow]

theorem modeShrinkLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeShrinkLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeShrinkLog m P := by
  simp [modeShrinkLogPolynomial, modeShrinkLog, modeProfileLogPolynomial_eval]

theorem modeSideLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeSideLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeSideLog m P := by
  simp [modeSideLogPolynomial, modeSideLog, modeProfileLogPolynomial_eval,
    modeBiasLogPolynomial_eval, modeShrinkLogPolynomial_eval]

theorem modeRankLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeRankLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeRankLog m P := by
  simp [modeRankLogPolynomial, modeRankLog, Polynomial.eval₂_finsetSum,
    modeBiasLogPolynomial_eval, modeShrinkLogPolynomial_eval]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CubeModeUniformBudget
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Polynomial

theorem cubeModePolynomialBudget_le_exp_input (q : ℕ) {P L : ℝ}
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hLP : L ≤ Real.exp P) :
    cubeModePolynomialBudget q L ≤ Real.exp ((cubeInputLogPolynomial q).eval₂ (Nat.castRingHom ℝ) P) := by
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have h3L : 3 * L ≤ Real.exp (P + 3) := by
    calc
      _ ≤ Real.exp 3 * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hbase : 1 + 3 * L ≤ Real.exp (P + 4) := by
    convert one_add_le_exp_succ (by positivity) h3L using 1
    congr 1
    ring
  have hf : (q.factorial : ℝ) ≤ Real.exp (q.factorial : ℝ) := by
    linarith [Real.add_one_le_exp (q.factorial : ℝ)]
  have ha : 2 + (q : ℝ) * (q + 1) ≤ Real.exp (2 + (q : ℝ) * (q + 1)) := by
    linarith [Real.add_one_le_exp (2 + (q : ℝ) * (q + 1))]
  unfold cubeModePolynomialBudget
  calc
    _ ≤ Real.exp (q.factorial : ℝ) * Real.exp (2 + (q : ℝ) * (q + 1)) *
        (Real.exp (P + 4)) ^ (q + 2) := by gcongr
    _ = Real.exp ((q.factorial : ℝ) + (2 + (q : ℝ) * (q + 1)) + (q + 2 : ℕ) * (P + 4)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      simp [cubeInputLogPolynomial]
      linarith

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixModuleAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem matrixModuleAction_apply {I J W : Type*} [Fintype J]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) (x : J → W) (i : I) :
    matrixModuleAction A x i = ∑ j, A i j • x j := rfl

theorem matrixModuleAction_mul {I J K W : Type*} [Fintype J] [Fintype K]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) (B : Matrix J K ℝ) (x : K → W) :
    matrixModuleAction A (matrixModuleAction B x) = matrixModuleAction (A * B) x := by
  funext i
  simp only [matrixModuleAction_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def latticeLiftSection (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) :
    orthogonalLatticeImage Λ Wᗮ →ₗ[ℤ] Λ :=
  basisSurjectionSection (orthogonalLatticeProjection Λ Wᗮ)
    (orthogonalLatticeProjection_surjective Λ Wᗮ) bP

variable [Fintype I] [Fintype J]

noncomputable def latticeIntegerLift (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) : (J → ℤ) →ₗ[ℤ] Λ :=
  (latticeLiftSection Λ W bP).comp bP.equivFun.symm.toLinearMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

def arrayCoordinateTorus {I J : Type*} (U : Submodule ℝ (J → ℝ)) :
    SubspaceArrayTorus I U →+ (I → SubspaceArrayTorus Unit U) :=
  AddMonoidHom.pi (fun i => QuotientAddGroup.map (subspaceArrayIntegerLattice I U)
    (subspaceArrayIntegerLattice Unit U) (arrayCoordinateLinear U i).toAddMonoidHom
    (fun _x hx _ a => hx i a))

theorem arrayCoordinateTorus_mk {I J : Type*} (U : Submodule ℝ (J → ℝ)) (x : I → U) (i : I) :
    arrayCoordinateTorus U (QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) x) i =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U) (fun _ => x i) := rfl

theorem arrayCoordinateTorus_bijective {I J : Type*} (U : Submodule ℝ (J → ℝ)) :
    Function.Bijective (arrayCoordinateTorus (I := I) U) := by
  constructor
  · intro x y h
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) y
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    intro i a
    exact (QuotientAddGroup.eq_iff_sub_mem.mp (congrFun h i)) () a
  · intro y
    choose v hv using fun i => QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice Unit U) (y i)
    refine ⟨QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) (fun i => v i ()), ?_⟩
    funext i
    rw [arrayCoordinateTorus_mk]
    have he : (fun _ : Unit => v i ()) = v i := funext (fun u => by cases u; rfl)
    rw [he, hv i]

noncomputable def arrayCoordinateEquiv {I J : Type*} (U : Submodule ℝ (J → ℝ)) :
    SubspaceArrayTorus I U ≃+ (I → SubspaceArrayTorus Unit U) :=
  AddEquiv.ofBijective (arrayCoordinateTorus U) (arrayCoordinateTorus_bijective U)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerMatrix_preserves_array_lattice {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (x : I → U)
    (hx : x ∈ subspaceArrayIntegerLattice I U) :
    matrixModuleAction (fun s i => (E s i : ℝ)) x ∈ subspaceArrayIntegerLattice S U := by
  classical
  change ∀ i a, ∃ n : ℤ, (x i).val a = n at hx
  choose z hz using hx
  intro s a
  refine ⟨∑ i, E s i * z i a, ?_⟩
  change (∑ i, (E s i : ℝ) • x i).val a = _
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, hz, Int.cast_sum, Int.cast_mul]

noncomputable def integerMatrixTorusMap {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) :
    SubspaceArrayTorus I U →+ SubspaceArrayTorus S U :=
  QuotientAddGroup.map (subspaceArrayIntegerLattice I U) (subspaceArrayIntegerLattice S U)
    (matrixModuleAction (fun s i => (E s i : ℝ))).toAddMonoidHom
    (fun x hx => integerMatrix_preserves_array_lattice U E x hx)

theorem integerMatrixTorusMap_mk {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (x : I → U) :
    integerMatrixTorusMap U E (QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) x) =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice S U)
        (matrixModuleAction (fun s i => (E s i : ℝ)) x) := rfl

end Erdos3

end

section

namespace Erdos3

theorem subspaceAmbientTorus_continuous {J : Type*} [Fintype J] (U : Submodule ℝ (J → ℝ)) :
    Continuous (subspaceAmbientTorus U) := by
  apply continuous_pi
  intro a
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice Unit U)).continuous_iff.mpr
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp
    (unitSubspaceCoordinate U a).continuous_of_finiteDimensional

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem booleanJetExtractionMatrix_mulVec {α O : Type*} [Fintype α] [DecidableEq α]
    (rows : O → Finset α) (f : Finset α → ℤ) (o : O) :
    (booleanJetExtractionMatrix rows *ᵥ f) o = booleanCoefficient f (rows o) := by
  classical
  change (∑ t, (if t ⊆ rows o then (-1 : ℤ) ^ (rows o \ t).card else 0) * f t) = _
  simp only [ite_mul, zero_mul, ← Finset.sum_filter]
  have hsets : Finset.univ.filter (fun t : Finset α => t ⊆ rows o) = (rows o).powerset := by
    ext t
    simp
  rw [hsets]
  rfl

def boundedCoefficientIntegerExponentEquiv (K : Type*) (h : ℕ) :
    VectorPolynomial.BoundedCoefficientExponent K h ≃ BoundedIntegerExponent K h where
  toFun e := ⟨e.val, e.property⟩
  invFun e := ⟨e.val, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def boundedCoefficientJetMatrix {α K O : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α) :
    Matrix O (VectorPolynomial.BoundedCoefficientExponent K h) ℤ :=
  fun o e => boundedDegreeIntegerJetMatrix root D h rows o
    (boundedCoefficientIntegerExponentEquiv K h e)

theorem boundedCoefficientJetMatrix_period {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (h : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    integerScalarLattice O (a ^ h) ≤ (boundedCoefficientJetMatrix root D h rows).mulVecLin.range := by
  intro y hy
  obtain ⟨x, hx⟩ := boundedDegreeIntegerJetMatrix_period root D a hperiod h rows hinj hdegree hy
  let e := boundedCoefficientIntegerExponentEquiv K h
  refine ⟨fun d => x (e d), ?_⟩
  ext o
  change (∑ d, boundedCoefficientJetMatrix root D h rows o d * x (e d)) = y o
  calc
    _ = ∑ d, boundedDegreeIntegerJetMatrix root D h rows o d * x d :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = y o := congrFun hx o

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

def coefficientLayerArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    CoefficientArray (K := K) U →ₗ[ℝ] (BoundedCoefficientExponent K (j.val + 1) → U j) where
  toFun x d := x ⟨j, d⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientLayerArray_preserves_lattice {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientLayerArray U j x ∈ subspaceArrayIntegerLattice
      (BoundedCoefficientExponent K (j.val + 1)) (U j) := fun d a => hx ⟨j, d⟩ a

def coefficientLayerTorus {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    CoefficientTorus (K := K) U →+
      SubspaceArrayTorus (BoundedCoefficientExponent K (j.val + 1)) (U j) :=
  QuotientAddGroup.map (coefficientIntegerLattice U)
    (subspaceArrayIntegerLattice (BoundedCoefficientExponent K (j.val + 1)) (U j))
    (coefficientLayerArray U j).toAddMonoidHom (coefficientLayerArray_preserves_lattice U j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

abbrev SiteTorus (S : Type*) {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) := ∀ j, SubspaceArrayTorus S (U j)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerMatrixTorusMap_comp {I S T J : Type*}
    [Fintype I] [Fintype S] (U : Submodule ℝ (J → ℝ))
    (A : Matrix T S ℤ) (B : Matrix S I ℤ) (x : SubspaceArrayTorus I U) :
    integerMatrixTorusMap U A (integerMatrixTorusMap U B x) =
      integerMatrixTorusMap U (A * B) x := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
  have hcast : Matrix.of (fun t s => (A t s : ℝ)) *
      Matrix.of (fun s i => (B s i : ℝ)) =
      Matrix.of (fun t i => ((A * B) t i : ℝ)) := by
    ext t i
    simp [Matrix.mul_apply]
  exact congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice T U))
    ((matrixModuleAction_mul (Matrix.of (fun t s => (A t s : ℝ)))
      (Matrix.of (fun s i => (B s i : ℝ))) v).trans
      (congrArg (fun M => matrixModuleAction M v) hcast))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

abbrev BooleanJetTorus {m : ℕ} (O : Fin m → Type*) {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) := ∀ j, SubspaceArrayTorus (O j) (U j)

noncomputable def siteBooleanJetTorusMap {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {O J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (rows : ∀ j, O j → Finset α) : SiteTorus (Finset α) U →+ BooleanJetTorus O U where
  toFun x j := integerMatrixTorusMap (U j) (booleanJetExtractionMatrix (rows j)) (x j)
  map_zero' := funext (fun j => map_zero (integerMatrixTorusMap (U j) _))
  map_add' x y := funext (fun j => map_add (integerMatrixTorusMap (U j) _) (x j) (y j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev EuclideanJetLayers (O : Fin m → Type*) :=
  ∀ j : Fin m, O j → euclideanSubspace (U j) ⧸
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J]

noncomputable def standardLatticeIntegerLift (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) :
    (J → ℤ) →ₗ[ℤ] standardEuclideanLattice D :=
  latticeIntegerLift (standardEuclideanLattice D) W
    (integerBasisOfReal (projectedIntegerLattice W) bP hP)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCoefficientCoverLift
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def normalizedLatticeRepresentative (x : W × (Fin n → ℤ)) : W :=
  x.1 - W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val

noncomputable def normalizedCoverLift (d : ℕ) (x : W × (Fin n → ℤ)) :
    W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  QuotientAddGroup.mk ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

theorem booleanJetExtraction_mul_reconstruction {α : Type*} [Fintype α] [DecidableEq α] :
    booleanJetExtractionMatrix (id : Finset α → Finset α) * booleanReconstructionMatrix α = 1 := by
  ext s r
  change (booleanJetExtractionMatrix id *ᵥ (fun t => if r ⊆ t then (1 : ℤ) else 0)) s = _
  rw [booleanJetExtractionMatrix_mulVec, booleanCoefficient_monomial]
  rfl

theorem booleanReconstruction_mul_extraction {α : Type*} [Fintype α] [DecidableEq α] :
    booleanReconstructionMatrix α * booleanJetExtractionMatrix (id : Finset α → Finset α) = 1 :=
  mul_eq_one_comm.mp booleanJetExtraction_mul_reconstruction

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

abbrev PrincipalIntegerTuples {D : Type*} (B : D → Type*) (h : D → ℕ) (α : Type*)
    (L : PrincipalTupleIndex B h → ℕ) := ∀ j, IntegerScalarCubeBox α (L j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

noncomputable def insertSubstitution (I : SlotInterleaving D E) (k : Fin (D + E))
    (i : Fin E) : (σ ⊕ Fin D) ⊕ Fin i.val → MvPolynomial (σ ⊕ Fin k.val) ℝ :=
  Sum.elim
    (Sum.elim (fun a => X (Sum.inl a))
      (fun j => if h : (I.left j).val < k.val then X (Sum.inr ⟨_, h⟩) else 0))
    (fun j => PolynomialSlots.placementSubstitution I.right k i (Sum.inr j))

end WeightedParameterSlots

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FixedKernelPolynomialCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

noncomputable def boundedExponentMap {K I : Type*} (e : K → I) (h : ℕ)
    (d : BoundedCoefficientExponent K h) : BoundedCoefficientExponent I h :=
  ⟨d.val.mapDomain e, by rw [Finsupp.degree_mapDomain]; exact d.property⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover
namespace OAI

section

namespace Erdos3

noncomputable def modeResidueSideThreshold (m d : ℕ) (D S ρ ε : ℝ) : ℝ :=
  modeRemovalSideThreshold m d D S ρ ε + S / (ρ * modeRemovalMesh d)

theorem modeResidueSideThreshold_bounds (m d : ℕ) {D S ρ ε : ℝ}
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε) :
    modeRemovalSideThreshold m d D S ρ ε ≤ modeResidueSideThreshold m d D S ρ ε ∧
      S / modeRemovalMesh d ≤ ρ * modeResidueSideThreshold m d D S ρ ε := by
  have hδ := modeRemovalMesh_pos d
  have hb := (modeRemovalSideThreshold_bounds m d hD hS hρ hε).1
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · have hle : S / (ρ * modeRemovalMesh d) ≤ modeResidueSideThreshold m d D S ρ ε :=
      le_add_of_nonneg_left hb.le
    have he : ρ * (S / (ρ * modeRemovalMesh d)) = S / modeRemovalMesh d := by
      field_simp
    rw [← he]
    exact mul_le_mul_of_nonneg_left hle hρ.le

theorem modeResidueWidth_mesh (m d : ℕ) {D S ρ ε H V : ℝ} {M : ℕ}
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hM : 0 < M) (hMS : (M : ℝ) ≤ S)
    (hH : modeResidueSideThreshold m d D S ρ ε ≤ H)
    (hV : 0 < V) (hwidth : ρ * H ≤ V) :
    1 ≤ V / M ∧ 1 / (V / M) ≤ modeRemovalMesh d := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hδ := modeRemovalMesh_pos d
  have hu : (M : ℝ) / modeRemovalMesh d ≤ V :=
    (div_le_div_of_nonneg_right hMS hδ.le).trans
      (((modeResidueSideThreshold_bounds m d hD hS hρ hε).2.trans
        (mul_le_mul_of_nonneg_left hH hρ.le)).trans hwidth)
  apply modeRemovalMesh_of_width d (div_pos hV hm)
  apply (le_div_iff₀ hm).mpr
  calc
    (1 / modeRemovalMesh d) * M = (M : ℝ) / modeRemovalMesh d := by ring
    _ ≤ V := hu

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubePositiveComparison
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

variable {K : Type*} [Fintype K] {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
  (U : ∀ j, Submodule ℝ (J j → ℝ))
  (R : CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U)
  (hR : ∀ x ∈ coefficientIntegerLattice U, R x ∈ coefficientIntegerLattice U)
  [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem coefficientResidual_section_integrable
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (f : CoefficientTorus (K := K) U → W) (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (x : CoefficientTorus (K := K) U) :
    Integrable (fun y => f (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) μ := by
  have hc := linearQuotientEndomorphism_continuous (coefficientIntegerLattice U) R hR
    R.continuous_of_finiteDimensional
  exact Integrable.of_bound (hf.comp (continuous_const.add hc)).aestronglyMeasurable B
    (ae_of_all μ (fun _ => hB _))

theorem coefficientResidualAverage_continuous
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (f : CoefficientTorus (K := K) U → W) (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    Continuous (linearQuotientAverage (coefficientIntegerLattice U) R hR μ f) := by
  apply continuous_of_dominated
    (fun x => (coefficientResidual_section_integrable U R hR μ f hf hB x).aestronglyMeasurable)
    (fun _ => ae_of_all μ (fun _ => hB _)) (integrable_const B)
  exact ae_of_all μ (fun _ => hf.comp (continuous_id.add continuous_const))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientJetCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem arrayCoordinateTorus_integerMatrix {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (A : Matrix S I ℤ) (x : SubspaceArrayTorus I U) (s : S) :
    arrayCoordinateTorus U (integerMatrixTorusMap U A x) s =
      ∑ i, A s i • arrayCoordinateTorus U x i := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
  simp only [integerMatrixTorusMap_mk, arrayCoordinateTorus_mk]
  let a : S → I → ℤ := A
  let q := QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U)
  change q (fun _ => matrixModuleAction (fun s i => (a s i : ℝ)) v s) =
    ∑ i, a s i • q (fun _ => v i)
  have he : (fun _ : Unit => matrixModuleAction (fun s i => (a s i : ℝ)) v s) =
      ∑ i, a s i • (fun _ : Unit => v i) := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply]
    change (∑ i, (a s i : ℝ) • v i) = ∑ i, a s i • v i
    exact Finset.sum_congr rfl (fun i _ => Int.cast_smul_eq_zsmul ℝ (a s i) (v i))
  rw [he, map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_zsmul q _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCoordinateEquiv
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

def coordinateReindexedSides (e : X ≃ Y) (N : X → ℕ) : Y → ℕ :=
  fun y => N (e.symm y)

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem coordinateReindexedSides_mem_integerBox (e : X ≃ Y) (N : X → ℕ) (y : Y → ℤ) :
    y ∈ integerBox (coordinateReindexedSides e N) ↔
      (fun x => y (e x)) ∈ integerBox N := by
  simp only [mem_integerBox, coordinateReindexedSides]
  constructor
  · intro hy x
    simpa only [e.symm_apply_apply] using hy (e x)
  · intro hy j
    simpa only [e.apply_symm_apply] using hy (e.symm j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalAmbientVolumeRatio
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

def centeredPhysicalCubeMap {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (z : Option K × X → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun d => physicalCubeCoefficient root D *ᵥ (fun k => z (k, d))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix

theorem physicalCubeRootDifferences_standard {X : Type*} {q : ℕ}
    (z : Option (Fin q) × X → ℤ) :
    physicalCubeRootDifferences (fun _ : Fin q => 0) (1 : Matrix (Fin q) (Fin q) ℤ) 0 z =
      standardPhysicalCubeOutput z := by
  funext x i
  rcases i with i | i
  · cases i
    rw [physicalCubeRootDifferences_root]
    simp [jointIntegerPhysicalSite, integerPhysicalSite, standardPhysicalCubeOutput]
  · rw [physicalCubeRootDifferences_direction]
    simp [Matrix.one_apply, standardPhysicalCubeOutput]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

def standardPhysicalSite {q : ℕ} : Finset (Fin q) → Fin q → ℤ :=
  integerAffineCube (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

@[simp]
theorem mean_empty {α : Type*} [Fintype α] [IsEmpty α] (f : α → ℝ) :
    mean f = 0 := by
  simp [mean]

@[simp]
theorem mean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    mean (fun _ : α => c) = c := by
  exact Fintype.expect_const c

@[simp]
theorem mean_zero {α : Type*} [Fintype α] :
    mean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [mean]

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

noncomputable def narrowTrimmedSpatialWidths {G J X : Type*}
    (W τ ξ : ℝ) (N : X → ℕ) : Option (G ⊕ J) × X → ℝ :=
  fun z => match z.1 with
    | some (.inr _) => ξ * trimmedSpatialWidths W τ N z
    | _ => trimmedSpatialWidths W τ N z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.StandardJetFourier
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical Matrix

theorem standardPhysicalSite_apply {q : ℕ} (s : Finset (Fin q)) (i : Fin q) :
    standardPhysicalSite s i = if i ∈ s then 1 else 0 := by
  simp [standardPhysicalSite, integerAffineCube, Matrix.one_apply]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedPatchKernel
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace PatchKernel

variable {d : ℕ}

def weight (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : PatchKernel d where
  value x := Φ.value x * f x
  nonneg x := mul_nonneg (Φ.nonneg x) (hI x).1
  le_one x := (mul_le_of_le_one_left (hI x).1 (Φ.le_one x)).trans (hI x).2
  support x hx := Φ.support x (mul_ne_zero_iff.mp hx).1
  lip := Φ.lip + L
  lipschitz := lipschitz_mul_unit_interval Φ.lipschitz hf (fun x => ⟨Φ.nonneg x, Φ.le_one x⟩) hI

@[simp] theorem weight_lip (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (Φ.weight f L hf hI).lip = Φ.lip + L := rfl

@[simp] theorem weight_value (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (x : Fin d → ℝ) :
    (Φ.weight f L hf hI).value x = Φ.value x * f x := rfl

def weightAlong {m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (g : (Fin d → ℝ) → Fin m → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g) : PatchKernel d :=
  Φ.weight (fun x => Ψ.value (g x)) (Ψ.lip * K) (Ψ.lipschitz.comp hg)
    (fun x => ⟨Ψ.nonneg (g x), Ψ.le_one (g x)⟩)

@[simp] theorem weightAlong_lip {m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (g : (Fin d → ℝ) → Fin m → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g) :
    (Φ.weightAlong Ψ g K hg).lip = Φ.lip + Ψ.lip * K := rfl

@[simp] theorem weightAlong_value {m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (g : (Fin d → ℝ) → Fin m → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g)
    (x : Fin d → ℝ) : (Φ.weightAlong Ψ g K hg).value x = Φ.value x * Ψ.value (g x) := rfl

end PatchKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidualRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem recoveredSmallLift_lipschitz {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) : LipschitzWith K (recoveredSmallLift M a c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro i
  simp only [recoveredSmallLift, Real.dist_eq]
  rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |(M i j : ℝ) * (a j - x j) - (M i j : ℝ) * (a j - y j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |(M i j : ℝ)| * dist x y := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [sub_sub_sub_cancel_left, abs_sub_comm, Real.dist_eq] using dist_le_pi_dist x y j
    _ = (∑ j, |(M i j : ℝ)|) * dist x y := (Finset.sum_mul _ _ _).symm
    _ ≤ K * dist x y := mul_le_mul_of_nonneg_right (hM i) dist_nonneg

noncomputable def recoveredCellKernel {d m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) : PatchKernel d :=
  Φ.weightAlong Ψ (recoveredSmallLift M a c) K (recoveredSmallLift_lipschitz M a c K hM)

@[simp] theorem recoveredCellKernel_lip {d m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) :
    (recoveredCellKernel Φ Ψ M a c K hM).lip = Φ.lip + Ψ.lip * K := rfl

@[simp] theorem recoveredCellKernel_value {d m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (e : Fin d → ℝ) :
    (recoveredCellKernel Φ Ψ M a c K hM).value e = Φ.value e * Ψ.value (recoveredSmallLift M a c e) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTIntegerRepresentative
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open _root_.MvPolynomial

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

omit [NeZero (∏ j, N j)] in
theorem crtRepresentativePolynomial_degree :
    crtRepresentativePolynomial N hN ∈ weightedSupportLE (fun _ => 1) 1 := by
  apply Submodule.sum_mem
  intro j _
  exact (weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedReferenceJetMass
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

noncomputable def coarseReferenceMassConstant (q : ℕ) (X : Type*) [Fintype X]
    (W L : ℝ) : ℝ :=
  4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
    (((1 + W) / L) ^ q) ^ Fintype.card X

end Erdos3.BooleanCubeKernel

end

end OAI
end


