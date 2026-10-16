-- Prove2me | Definitions.Def_OAIErdos3B1372
-- name    : OAIErdos3B1372
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T23:13:05.8813+00:00
-- url     : https://prove2.me/theorems/6155cff0-347f-45f7-807f-e292deb786f7
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1373 of 1375
-- statement:
--   Definitions bundle 1373 of 1375 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1371`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1373 available.
--
--   Modules: `OAI.Erdos3.FiniteProbabilityWeights.piRestriction_mass_pos`, `OAI.Erdos3.FiniteProbabilityWeights.pi_condition`, `OAI.Erdos3.FiniteProbabilityWeights.toPMF_bind_apply`, `OAI.Erdos3.FiniteProbabilityWeights.toPMF_bind_toReal`, `OAI.Erdos3.FiniteProbabilityWeights.toPMF_map_toReal`, `OAI.Erdos3.FiniteProbabilityWeights.toPMF_pi`, `OAI.Erdos3.FiniteProbabilityWeights.toPMF_toReal`, `OAI.Erdos3.VectorPolynomial.allocatedLayerInteger_moderate_eval`, `OAI.Erdos3.VectorPolynomial.allocatedLayerInteger_moderate_tail_zero`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample_jets`, `OAI.Erdos3.VectorPolynomial.coefficientAxisLaw_probability`, `OAI.Erdos3.VectorPolynomial.coefficientDeckJetMap_coordinate`, `OAI.Erdos3.VectorPolynomial.coefficientDeckJetMap_mem_range_iff`, `OAI.Erdos3.VectorPolynomial.coefficientDeckJetMap_range_eq_of_integer_range_eq`, `OAI.Erdos3.VectorPolynomial.coefficientDeckKernel_jets`, `OAI.Erdos3.VectorPolynomial.coefficientJetAxisMap_measurable`, `OAI.Erdos3.affineProductProfileLip_le_exp`, `OAI.Erdos3.affineProductProfile_integral`, `OAI.Erdos3.allocatedIntegerCoordinate_tail_pure`, `OAI.Erdos3.allocatedIntegerCoordinate_tail_zero`, `OAI.Erdos3.arrayResidueChart_measurePreserving`, `OAI.Erdos3.booleanCoefficient_abs_le`, `OAI.Erdos3.booleanCoefficient_div`, `OAI.Erdos3.booleanCoefficient_map`, `OAI.Erdos3.boundedDegreeIntegerJetMatrix_common_period`, `OAI.Erdos3.boundedDegreeRealJetMatrix_entry_bound`, `OAI.Erdos3.coefficientImageMultiplier_le_index`, `OAI.Erdos3.coefficientImageMultiplier_nonneg`, `OAI.Erdos3.dependentProductPMF_apply`, `OAI.Erdos3.dependentProductPMF_marginal`, `OAI.Erdos3.ennreal_smul_sigmaFinite`, `OAI.Erdos3.finiteFiberAverage_continuous`, `OAI.Erdos3.finiteFiberAverage_eq_of_map_eq`, `OAI.Erdos3.finiteFiberAverage_factor`, `OAI.Erdos3.finiteFiberAverage_integral_of_invariant`, `OAI.Erdos3.finiteFiberAverage_integral_uniform`, `OAI.Erdos3.finiteKernelLiftLaw_basisResidues`, `OAI.Erdos3.finiteKernelLiftLaw_eq`, `OAI.Erdos3.finiteKernelLiftLaw_integral`, `OAI.Erdos3.finiteKernelLiftLaw_relabel`, `OAI.Erdos3.finiteKernelLift_density`, `OAI.Erdos3.finiteKernelLift_restrict`, `OAI.Erdos3.hasBoundedScalarPeriod_index_le`, `OAI.Erdos3.integerAffineCube_residue_eq`, `OAI.Erdos3.integerBooleanCoefficient_congr`, `OAI.Erdos3.integerBooleanCoefficient_residue`, `OAI.Erdos3.integerColumnEquiv_range`, `OAI.Erdos3.integerJetMatrix_residue_eq`, `OAI.Erdos3.integerMappedCubeTuple_residue`, `OAI.Erdos3.integerMappedCubeTuple_residue_both`, `OAI.Erdos3.integerMappedJetMatrix_residue`, `OAI.Erdos3.integerMappedJetMatrix_residue_both`, `OAI.Erdos3.integerMatrixImage_eq_of_residueMatrix`, `OAI.Erdos3.integerMatrixResidue_image_eq`, `OAI.Erdos3.integerMatrixResidue_mem`, `OAI.Erdos3.integerMatrix_fromCols_range`, `OAI.Erdos3.integerMonomialArrayPolynomial_principal_sum`, `OAI.Erdos3.integerPolynomial_eval_congr`, `OAI.Erdos3.integerPolynomial_eval_residue`, `OAI.Erdos3.integerPrincipalPolynomial_eval`, `OAI.Erdos3.integerResidueMatrix_range_eq_of_integer_range_eq`, `OAI.Erdos3.integerRowMassInterpolation_grid`, `OAI.Erdos3.integerRowMassInterpolation_lipschitz`, `OAI.Erdos3.integerRowMassInterpolation_range`, `OAI.Erdos3.integerRowMassTent_grid`, `OAI.Erdos3.integerRowMassTent_integrable`, `OAI.Erdos3.integerRowMassTent_lipschitz`, `OAI.Erdos3.integerRowMassTent_range`, `OAI.Erdos3.integerScalarLattice_pow_le`, `OAI.Erdos3.integer_monomial_eval_cast`, `OAI.Erdos3.integral_comp_inverse_pivot`, `OAI.Erdos3.inverse_map_volume`, `OAI.Erdos3.latticeCover_measurePreserving`, `OAI.Erdos3.latticeDeckInteger_coordinates`, `OAI.Erdos3.latticeDeckInteger_reconstruction`, `OAI.Erdos3.latticeQuotient_compact`, `OAI.Erdos3.latticeSignedCoordinates_reconstruction`, `OAI.Erdos3.latticeSignedCoordinates_symm_apply`, `OAI.Erdos3.mixedArrayIntegerImage_regroup`, `OAI.Erdos3.mixedArrayRegroup_apply`, `OAI.Erdos3.mixedArrayRegroup_volume_count`, `OAI.Erdos3.mixedRealPoint_coordinates`, `OAI.Erdos3.mixedScalarArrayLaw_probability`, `OAI.Erdos3.monomialCoefficientMatrix_residue_eq`, `OAI.Erdos3.normalizedBoundedIntegerJetMatrix_eq`, `OAI.Erdos3.normalizedChartReference_finite`, `OAI.Erdos3.normalizedChartReference_map`, `OAI.Erdos3.normalizedChartRegion_measurable`, `OAI.Erdos3.normalizedCoverLift_reference`, `OAI.Erdos3.normalizedCoverResidues_reference`, `OAI.Erdos3.normalizedDeckPoint_identity`, `OAI.Erdos3.normalizedIntegerColumns_entry`, `OAI.Erdos3.normalizedIntegerColumns_entry_div`, `OAI.Erdos3.normalizedIntegerMonomialJetMatrix_eq`, `OAI.Erdos3.normalizedIntegerPivot_entry`, `OAI.Erdos3.normalizedLatticePoint_linear_lift`, `OAI.Erdos3.orthonormalArrayChart_measurePreserving`, `OAI.Erdos3.orthonormalArrayChart_scaled_reference`, `OAI.Erdos3.orthonormalMixedChart_sum_zsmul`, `OAI.Erdos3.piChart_reference_map`, `OAI.Erdos3.pi_count_measure`, `OAI.Erdos3.pi_smul_finite`, `OAI.Erdos3.pivotCoordinateChange_inverse_map`, `OAI.Erdos3.pivotDensityPullback_integrable`, `OAI.Erdos3.pivotDensityPullback_integral`, `OAI.Erdos3.pivotFullImage_eq_range`, `OAI.Erdos3.pivotOutputDensity_integrable`, `OAI.Erdos3.pivotOutputDensity_integral`, `OAI.Erdos3.pivotOutputDensity_nonneg`, `OAI.Erdos3.pmf_real_mass`, `OAI.Erdos3.principalCoefficientChoice_injective`, `OAI.Erdos3.principalCoefficientMarginal`, `OAI.Erdos3.productBlockExponent_monomial_int`, `OAI.Erdos3.progression_slice_endpoint_geometry`, `OAI.Erdos3.realAffineCube_abs_le`, `OAI.Erdos3.realAffineCube_normalized_integer`, `OAI.Erdos3.realDensityMeasure_indicator_one`, `OAI.Erdos3.real_monomial_eval_abs_le`, `OAI.Erdos3.real_monomial_eval_div_scale`, `OAI.Erdos3.residueLatticeImage_card_mul_index`, `OAI.Erdos3.residueLatticeImage_comap`, `OAI.Erdos3.residueLatticeImage_determines_lattice`, `OAI.Erdos3.residueLatticeImage_index`, `OAI.Erdos3.residueLatticeImage_index_le`, `OAI.Erdos3.restrictedChartDensity_measurable`, `OAI.Erdos3.restrictedComplexChartDensity_apply`, `OAI.Erdos3.restrictedComplexChartDensity_zero`, `OAI.Erdos3.rootDifferenceMatrix_mulVec`, `OAI.Erdos3.rootDifferenceMatrix_period`, `OAI.Erdos3.scalarCubeResiduePi_support`, `OAI.Erdos3.scalarCubeResidueWeights_support`, `OAI.Erdos3.scalarKernelJet_extended_index`, `OAI.Erdos3.scalarKernelJet_extended_period`, `OAI.Erdos3.selectedCoefficientProfile_integral`, `OAI.Erdos3.selectedCoefficientProfile_nonneg`, `OAI.Erdos3.selectedCoefficientProfile_zero_outside`, `OAI.Erdos3.selectedSpatial_fromCols`, `OAI.Erdos3.selectedSpatial_full_image`, `OAI.Erdos3.signedSplitCoordinates_symm_apply`, `OAI.Erdos3.smoothProbabilityProfile_inner_lower`, `OAI.Erdos3.splitFreeProfile_continuous`, `OAI.Erdos3.splitFreeProfile_integrable`, `OAI.Erdos3.splitFreeProfile_integral`, `OAI.Erdos3.splitFreeProfile_nonneg`, `OAI.Erdos3.splitFreeProfile_zero_outside`, `OAI.Erdos3.splitInputProfile_integral`, `OAI.Erdos3.standardEuclideanLinearEquiv_apply`, `OAI.Erdos3.standardEuclideanLinearEquiv_eq_point`, `OAI.Erdos3.standardLatticeCoordinates_reconstruction`, `OAI.Erdos3.uniformPMF_map_equiv`, `OAI.Erdos3.uniformPMF_map_fiber`, `OAI.Erdos3.uniformPMF_map_hom_eq_of_range_eq`, `OAI.Erdos3.uniformPMF_map_hom_image`, `OAI.Erdos3.uniformPMF_toMeasure_pi`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B053

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_comap {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).comap (integerResidueMap I m) = L := by
  apply Submodule.comap_map_eq_self
  rwa [integerResidueMap_ker]

theorem residueLatticeImage_determines_lattice {I : Type*} [Fintype I]
    (L K : Submodule ℤ (I → ℤ)) (m : ℕ)
    (hL : integerScalarLattice I (m : ℤ) ≤ L) (hK : integerScalarLattice I (m : ℤ) ≤ K)
    (h : residueLatticeImage L m = residueLatticeImage K m) : L = K := by
  rw [← residueLatticeImage_comap L m hL, ← residueLatticeImage_comap K m hK, h]

theorem residueLatticeImage_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).toAddSubgroup.index = L.toAddSubgroup.index := by
  have hk : (integerResidueMap I m).toAddMonoidHom.ker ≤ L.toAddSubgroup := by
    change (LinearMap.ker (integerResidueMap I m)).toAddSubgroup ≤ L.toAddSubgroup
    rw [integerResidueMap_ker]
    exact hperiod
  have h := L.toAddSubgroup.index_map_eq (integerResidueMap_surjective I m) hk
  change (L.toAddSubgroup.map (integerResidueMap I m).toAddMonoidHom).index = _
  exact h

theorem residueLatticeImage_card_mul_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = m ^ Fintype.card I := by
  classical
  have h := (residueLatticeImage L m).toAddSubgroup.card_mul_index
  rw [residueLatticeImage_index L m hperiod] at h
  change Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = Nat.card (I → ZMod m) at h
  have heq : Nat.card (I → ZMod m) = m ^ Fintype.card I := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  exact h.trans heq

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem integerMatrixResidue_mem {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) (v : I → ZMod m) :
    v ∈ residueLatticeImage A.mulVecLin.range m ↔
      ∃ x : J → ZMod m, integerResidueMatrix A m *ᵥ x = v := by
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, hy⟩
    exact ⟨integerResidueMap J m x, (integerResidueMap_mulVec A m x).symm.trans hy⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz⟩ := integerResidueMap_surjective J m x
    refine ⟨A *ᵥ z, ⟨z, rfl⟩, ?_⟩
    rw [integerResidueMap_mulVec, hz, hx]

theorem integerMatrixResidue_image_eq {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) :
    residueLatticeImage A.mulVecLin.range m =
      (integerResidueMatrix A m).mulVecLin.range.restrictScalars ℤ := by
  ext v
  exact integerMatrixResidue_mem A m v

theorem integerMatrixImage_eq_of_residueMatrix {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℤ) (m : ℕ)
    (hA : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hB : integerScalarLattice I (m : ℤ) ≤ B.mulVecLin.range)
    (hAB : integerResidueMatrix A m = integerResidueMatrix B m) :
    A.mulVecLin.range = B.mulVecLin.range := by
  apply residueLatticeImage_determines_lattice _ _ m hA hB
  rw [integerMatrixResidue_image_eq, integerMatrixResidue_image_eq, hAB]

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    L.toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hpos := Nat.card_pos (α := residueLatticeImage L m)
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem dependentProductPMF_apply {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (x : ∀ d, X d) : dependentProductPMF p x = ∏ d, p d (x d) := by
  simp only [dependentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

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

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialResidues
namespace OAI

section

namespace Erdos3

theorem integerPolynomial_eval_residue {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) (x : X → ℤ) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod m)) (integerResidueMap X m x) p := by
  have heq : integerResidueMap X m x = (fun i => (x i : ZMod m)) := rfl
  rw [heq]
  simpa only [MvPolynomial.eval₂_id, RingHom.comp_id, Int.coe_castRingHom] using
    MvPolynomial.hom_eval₂ p (RingHom.id ℤ) (Int.castRingHom (ZMod m)) x

theorem integerPolynomial_eval_congr {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) {x y : X → ℤ} (hxy : integerResidueMap X m x = integerResidueMap X m y) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) = ((MvPolynomial.eval y p : ℤ) : ZMod m) := by
  rw [integerPolynomial_eval_residue, integerPolynomial_eval_residue, hxy]

theorem integerBooleanCoefficient_residue {α : Type*} [DecidableEq α]
    (m : ℕ) (f : Finset α → ℤ) (s : Finset α) :
    ((booleanCoefficient f s : ℤ) : ZMod m) =
      booleanCoefficient (fun t => (f t : ZMod m)) s :=
  booleanCoefficient_map (Int.castRingHom (ZMod m)) f s

theorem integerBooleanCoefficient_congr {α : Type*} [DecidableEq α]
    (m : ℕ) (f g : Finset α → ℤ) (s : Finset α)
    (hfg : ∀ t ∈ s.powerset, (f t : ZMod m) = (g t : ZMod m)) :
    ((booleanCoefficient f s : ℤ) : ZMod m) = ((booleanCoefficient g s : ℤ) : ZMod m) := by
  rw [integerBooleanCoefficient_residue, integerBooleanCoefficient_residue]
  unfold booleanCoefficient
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only
  rw [hfg t ht]

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

theorem integerJetMatrix_residue_eq {α K O J : Type*} [DecidableEq α]
    (basis : J → MvPolynomial K ℤ) (vertices vertices' : Finset α → K → ℤ)
    (rows : O → Finset α) (m : ℕ)
    (hvertices : ∀ o t, t ∈ (rows o).powerset →
      integerResidueMap K m (vertices t) = integerResidueMap K m (vertices' t)) :
    integerResidueMatrix (integerJetMatrix basis vertices rows) m =
      integerResidueMatrix (integerJetMatrix basis vertices' rows) m := by
  ext o j
  apply integerBooleanCoefficient_congr
  intro t ht
  exact integerPolynomial_eval_congr (basis j) m (hvertices o t ht)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerScalarLattice_pow_le {O : Type*} [Fintype O]
    (a : ℤ) {h s : ℕ} (hh : h ≤ s) :
    integerScalarLattice O (a ^ s) ≤ integerScalarLattice O (a ^ h) := by
  rintro y ⟨z, rfl⟩
  refine ⟨a ^ (s - h) • z, ?_⟩
  change a ^ h • (a ^ (s - h) • z) = a ^ s • z
  rw [smul_smul, ← pow_add, Nat.add_sub_of_le hh]

theorem boundedDegreeIntegerJetMatrix_common_period {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (s h : ℕ) (hh : h ≤ s) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    integerScalarLattice O (a ^ s) ≤ (boundedDegreeIntegerJetMatrix root D h rows).mulVecLin.range :=
  (integerScalarLattice_pow_le a hh).trans
    (boundedDegreeIntegerJetMatrix_period root D a hperiod h rows hinj hdegree)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerAffineCube_residue_eq {α K : Type*}
    (root root' : K → ℤ) (D D' : Matrix α K ℤ) (m : ℕ)
    (hroot : integerResidueMap K m root = integerResidueMap K m root')
    (hD : integerResidueMatrix D m = integerResidueMatrix D' m) (t : Finset α) :
    integerResidueMap K m (integerAffineCube root D t) =
      integerResidueMap K m (integerAffineCube root' D' t) := by
  funext k
  change ((root k + ∑ r ∈ t, D r k : ℤ) : ZMod m) =
    ((root' k + ∑ r ∈ t, D' r k : ℤ) : ZMod m)
  push_cast
  have hk : (root k : ZMod m) = (root' k : ZMod m) := congrFun hroot k
  rw [hk]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact congrFun (congrFun hD r) k

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

variable [Fintype ι]

theorem inverse_map_volume (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    Measure.map A.symm volume = ENNReal.ofReal ((inverseJacobian A)⁻¹) • volume := by
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    A.symm.toLinearEquiv.isUnit_det'.ne_zero
  simpa only [inverseJacobian, abs_inv, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PivotCoordinateChange
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotCoordinateChange_inverse_map (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) :
    Measure.map (pivotCoordinateChange A B).symm volume =
      ENNReal.ofReal ((inverseJacobian A)⁻¹) • volume := by
  have hs (y : J → ℝ) :
      Measure.map (fun x => A.symm (x - B y)) volume =
        ENNReal.ofReal ((inverseJacobian A)⁻¹) • volume := by
    have ht : Measure.map (fun x : I → ℝ => x - B y) volume = volume := by
      simpa only [sub_eq_add_neg] using (measurePreserving_add_right volume (-B y)).map_eq
    rw [show (fun x => A.symm (x - B y)) = A.symm ∘ (fun x => x - B y) from rfl,
      ← Measure.map_map A.symm.continuous.measurable (by fun_prop), ht]
    exact inverse_map_volume A
  have hp := (MeasurePreserving.id (volume : Measure (J → ℝ))).skew_product
    (g := fun y x => A.symm (x - B y)) (by fun_prop) (Filter.Eventually.of_forall hs)
  change Measure.map (fun p : (J → ℝ) × (I → ℝ) => (p.1, A.symm (p.2 - B p.1)))
    (volume.prod volume) = _
  simpa only [id_eq, Measure.prod_smul_right, Measure.volume_eq_prod] using hp.map_eq

theorem integral_comp_inverse_pivot (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ p, f ((pivotCoordinateChange A B).symm p)) =
      (inverseJacobian A)⁻¹ * ∫ p, f p := by
  have h := (pivotCoordinateChange A B).symm.measurableEmbedding.integral_map
    (μ := volume) f
  rw [pivotCoordinateChange_inverse_map, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (inverseJacobian_pos A).le)] at h
  exact h.symm

theorem pivotDensityPullback_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (pivotDensityPullback A B f) := by
  have hm : Integrable f (Measure.map (pivotCoordinateChange A B).symm volume) := by
    rw [pivotCoordinateChange_inverse_map]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact ((pivotCoordinateChange A B).symm.measurableEmbedding.integrable_map_iff.mp hm).const_mul _

theorem pivotDensityPullback_integral (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ p, pivotDensityPullback A B f p) = ∫ p, f p := by
  unfold pivotDensityPullback
  rw [integral_const_mul, integral_comp_inverse_pivot, ← mul_assoc,
    mul_inv_cancel₀ (inverseJacobian_pos A).ne', one_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.TranslatedMixtureL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem pivotOutputDensity_nonneg (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : ∀ p, 0 ≤ f p) (v : I → ℝ) : 0 ≤ pivotOutputDensity A B f v :=
  integral_nonneg fun _ => mul_nonneg (inverseJacobian_pos A).le (hf _)

theorem pivotOutputDensity_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (pivotOutputDensity A B f) :=
  (pivotDensityPullback_integrable A B hf).integral_prod_right

theorem pivotOutputDensity_integral (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) : (∫ v, pivotOutputDensity A B f v) = ∫ p, f p := by
  unfold pivotOutputDensity
  rw [← integral_prod_symm _ (pivotDensityPullback_integrable A B hf)]
  exact pivotDensityPullback_integral A B f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotNormalizedMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem normalizedIntegerPivot_entry (A : Matrix I I ℤ) (S P : I → ℝ) (i j : I) :
    normalizedIntegerPivot A S P i j = (A i j : ℝ) * S j / P i := by
  simp only [normalizedIntegerPivot, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.map_apply, Int.coe_castRingHom, div_eq_mul_inv]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem splitInputProfile_integral (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ x, splitInputProfile f x) = ∫ p, f p :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).measurableEmbedding f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_abs_le {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) {M : ℝ}
    (hf : ∀ t ∈ s.powerset, |f t| ≤ M) :
    |booleanCoefficient f s| ≤ (2 : ℝ) ^ s.card * M := by
  unfold booleanCoefficient
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ) ^ (s \ t).card * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hf t ht
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realAffineCube_abs_le {α K : Type*} [Fintype α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (t : Finset α) (k : K) :
    |realAffineCube root difference t k| ≤ (Fintype.card α : ℝ) + 1 := by
  unfold realAffineCube
  calc
    _ ≤ |root k| + |∑ r ∈ t, difference r k| := abs_add_le _ _
    _ ≤ 1 + ∑ r ∈ t, |difference r k| :=
      add_le_add (hroot k) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ _r ∈ t, (1 : ℝ) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun r _ => hd r k))
    _ = 1 + t.card := by simp
    _ ≤ (Fintype.card α : ℝ) + 1 := by
      have hc : (t.card : ℝ) ≤ Fintype.card α := by exact_mod_cast Finset.card_le_univ t
      linarith

theorem real_monomial_eval_abs_le {K : Type*} (e : K →₀ ℕ) (x : K → ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hx : ∀ k, |x k| ≤ C) {h : ℕ}
    (he : e.sum (fun _ n => n) ≤ h) :
    |MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ))| ≤ C ^ h := by
  classical
  rw [MvPolynomial.eval_monomial, one_mul]
  change |∏ k ∈ e.support, x k ^ e k| ≤ _
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ k ∈ e.support, C ^ e k := by
      apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
      intro k _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _
    _ = C ^ e.sum (fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ C ^ h := pow_le_pow_right₀ hC he

theorem boundedDegreeRealJetMatrix_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : BoundedIntegerExponent K h) :
    |boundedDegreeRealJetMatrix root difference h rows o e| ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
  have hb := booleanCoefficient_abs_le
    (fun t => MvPolynomial.eval (realAffineCube root difference t)
      (MvPolynomial.monomial e.val (1 : ℝ))) (rows o)
    (fun t _ => real_monomial_eval_abs_le e.val _ (le_add_of_nonneg_left (Nat.cast_nonneg _))
      (realAffineCube_abs_le root difference hroot hd t) e.property)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_mass {X : Type*} (p : PMF X) : (∑' x, (p x).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (p.apply_ne_top), p.tsum_coe, ENNReal.toReal_one]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Function _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem restrictedChartDensity_measurable (q : X → Y) {S : Set X}
    (he : MeasurableEmbedding (fun x : S => q x.val)) (c : ℝ)
    (f : X → ℝ) (hf : Measurable f) :
    Measurable (restrictedChartDensity q S c f) :=
  embeddingDensity_measurable _ he c _ (hf.comp measurable_subtype_coe)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

theorem restrictedComplexChartDensity_apply (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) (hinj : Set.InjOn q S) {x : X} (hx : x ∈ S) :
    restrictedComplexChartDensity q S c f (q x) = (c : ℂ) * f x := by
  have he : Function.Injective (fun x : S => q x.val) := fun a b h => Subtype.ext (hinj a.property b.property h)
  exact congrArg (fun z : ℂ => (c : ℂ) * z) (he.extend_apply (fun x => f x.val) (fun _ => 0) ⟨x, hx⟩)

theorem restrictedComplexChartDensity_zero (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) {y : Y} (hy : y ∉ q '' S) :
    restrictedComplexChartDensity q S c f y = 0 := by
  have hy' : y ∉ Set.range (fun x : S => q x.val) := by
    rintro ⟨x, rfl⟩
    exact hy ⟨x.val, x.property, rfl⟩
  simp only [restrictedComplexChartDensity, Function.extend_apply' _ _ _ hy', mul_zero]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

variable {σ R W Z : Type*} [CommRing R] [AddCommGroup W] [Module R W]
  [AddCommGroup Z] [Module R Z]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {I R S W : Type*} [CommRing R] [CommRing S] [AddCommGroup W] [Module R W]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

theorem dependentProductPMF_marginal {I J : Type*} [Fintype I] [Fintype J]
    {X : I → Type*} [∀ i, Countable (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSingletonClass (X i)]
    (p : ∀ i, PMF (X i)) (e : J → I) (he : Function.Injective e) :
    (dependentProductPMF p).map (fun (x : ∀ i, X i) (j : J) => x (e j)) =
      dependentProductPMF (fun j => p (e j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun (x : ∀ i, X i) (j : J) => x (e j)) _ (by fun_prop)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  have hind : iIndepFun (fun i (x : ∀ i, X i) => x i)
      (Measure.pi (fun i => (p i).toMeasure)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hsel := iIndepFun.precomp he hind
  have hm := hsel.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  apply hm.trans
  congr 1
  funext j
  exact (measurePreserving_eval (fun i => (p i).toMeasure) (e j)).map_eq

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped TensorProduct Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

theorem principalCoefficientChoice_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (principalCoefficientChoice (G := G) (B := B) h d) := by
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b =>
      exact False.elim (canonicalPrincipalExponent_ne_zero h d hd b
        (congrArg Subtype.val hxy).symm)
  | some b =>
    cases y with
    | none =>
      exact False.elim (canonicalPrincipalExponent_ne_zero h d hd b
        (congrArg Subtype.val hxy))
    | some b' =>
      exact congrArg some (principalCoefficientSlot_injective h d hd hxy)

theorem principalCoefficientMarginal {D G : Type*} [Fintype D] [Fintype G]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (hd : 0 < h d)
    (p : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → PMF ℤ) :
    (independentProductPMF p).map (fun a r => a (principalCoefficientChoice h d r)) =
      independentProductPMF (fun r => p (principalCoefficientChoice h d r)) :=
  independentProductPMF_marginal p _ (principalCoefficientChoice_injective h d hd)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RootDifferenceMatrix
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rootDifferenceMatrix_mulVec {I J R : Type*} [Fintype J] [CommRing R]
    (root : J → R) (D : Matrix I J R) (x : R) (v : J → R) :
    rootDifferenceMatrix root D *ᵥ Sum.elim (fun _ : Unit => x) v =
      Sum.elim (fun _ : Unit => x + ∑ j, root j * v j) (D *ᵥ v) := by
  funext i
  cases i with
  | inl i =>
    cases i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rootDifferenceMatrix, Matrix.fromBlocks]
  | inr i => simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rootDifferenceMatrix, Matrix.fromBlocks]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem selectedSpatial_fromCols {I J R : Type*} [Fintype I] [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J) :
    Matrix.fromCols (selectedSpatialPivot root D s) (selectedSpatialFreeColumns root D s) =
      (rootDifferenceMatrix root D).submatrix id (selectedSpatialColumnEquiv s) := by
  ext i j
  cases j with
  | inl j => cases j <;> cases i <;> rfl
  | inr j => cases i <;> rfl

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeProfile_continuous {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (splitFreeProfile f g) := by
  unfold splitFreeProfile
  fun_prop

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeProfile_nonneg {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ n, 0 ≤ g n) (p) :
    0 ≤ splitFreeProfile f g p := mul_nonneg (hf _) (hg _)

theorem splitFreeProfile_zero_outside {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} {R S : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (hg : ∀ n, S < ‖n‖ → g n = 0)
    (p : (J ⊕ N → ℝ) × (I → ℝ)) (hp : max R S < ‖p‖) :
    splitFreeProfile f g p = 0 := by
  let y : J → ℝ := fun j => p.1 (.inl j)
  let n : N → ℝ := fun n => p.1 (.inr n)
  by_cases hy : R < ‖(y, p.2)‖
  · exact mul_eq_zero_of_left (hf _ hy) _
  · have hn : S < ‖n‖ := by
      by_contra! hn
      have hy' : ‖(y, p.2)‖ ≤ R := le_of_not_gt hy
      have hnorm : ‖p‖ ≤ max R S := by
        rw [Prod.norm_def]
        apply max_le
        · rw [← splitCoordinates_norm p.1, Prod.norm_def]
          exact max_le ((norm_fst_le (y, p.2)).trans (hy'.trans (le_max_left _ _)))
            (hn.trans (le_max_right _ _))
        · exact (norm_snd_le (y, p.2)).trans (hy'.trans (le_max_left _ _))
      exact (not_le_of_gt hp) hnorm
    exact mul_eq_zero_of_right _ (hg _ hn)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

theorem normalizedIntegerColumns_entry (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (i : I) (j : J) : normalizedIntegerColumns B T P i j = (P i)⁻¹ * B i j * T j := by
  simp [normalizedIntegerColumns, Matrix.diagonal_mul, Matrix.mul_diagonal]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

theorem normalizedIntegerColumns_entry_div {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) (i : I) (j : J) :
    normalizedIntegerColumns A T P i j = (A i j : ℝ) * T j / P i := by
  rw [normalizedIntegerColumns_entry]
  simp only [div_eq_mul_inv]
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedCoefficientProfile_nonneg {I J : Type*} [Fintype I]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ p, 0 ≤ selectedCoefficientProfile s f p := fun p => hf (selectedCoefficientEquiv s ℝ p)

theorem selectedCoefficientProfile_zero_outside {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ x, R < ‖x‖ → f x = 0) :
    ∀ p, R < ‖p‖ → selectedCoefficientProfile s f p = 0 := by
  intro p hp
  exact hf _ (by rwa [selectedCoefficientEquiv_norm])

theorem selectedCoefficientProfile_integral {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) :
    (∫ p, selectedCoefficientProfile s f p) = ∫ x, f x := by
  let e := selectedFreeFirstEquiv s
  have hsum := (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : UnselectedColumn s ⊕ I => ℝ)).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : UnselectedColumn s ⊕ I => ℝ)).symm.measurableEmbedding
    (fun z => f (z ∘ e.symm))
  have hpi := (volume_measurePreserving_piCongrLeft (fun _ : J => ℝ) e).integral_comp
    (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e).measurableEmbedding f
  apply hsum.trans
  simpa only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
    Equiv.coe_fn_symm_mk, eq_rec_constant, Function.comp_def] using hpi

end Erdos3

end

section

namespace Erdos3

variable {I J R : Type*} [Fintype I] (s : I ↪ J)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem smoothProbabilityProfile_inner_lower (x : ℝ) (hx : |x| ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ smoothProbabilityProfile x := by
  have hx' : probabilityProfileBump x = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simpa [probabilityProfileBump, Real.dist_eq] using hx)
  have hi := probabilityProfileBump.integral_le_measure_closedBall volume
  norm_num [probabilityProfileBump] at hi
  change (∫ y, probabilityProfileBump y) ≤ 3 / 2 at hi
  change (1 / 2 : ℝ) ≤ probabilityProfileBump x / ∫ y, probabilityProfileBump y
  rw [hx']
  apply (le_div_iff₀ probabilityProfileBump.integral_pos).mpr
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]

theorem piRestriction_mass_pos (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) (hG : ∀ j, 0 < (p j).mass (G j)) :
    0 < (pi p).mass (piRestrictionSet G) := by
  rw [piRestriction_mass]
  exact Finset.prod_pos (fun j _ => hG j)

theorem pi_condition (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) (hG : ∀ j, 0 < (p j).mass (G j)) :
    pi (fun j => (p j).condition (G j) (hG j)) =
      (pi p).condition (piRestrictionSet G) (piRestriction_mass_pos p G hG) := by
  classical
  apply ext_weight
  funext x
  change (∏ j, (if x j ∈ G j then (p j).weight (x j) else 0) / (p j).mass (G j)) =
    (if x ∈ piRestrictionSet G then ∏ j, (p j).weight (x j) else 0) /
      (pi p).mass (piRestrictionSet G)
  rw [piRestriction_mass, Finset.prod_div_distrib]
  congr 1
  by_cases hx : ∀ j, x j ∈ G j
  · simp only [hx, ite_true, (mem_piRestrictionSet G x).mpr hx]
  · rw [if_neg ((mem_piRestrictionSet G x).not.mpr hx)]
    obtain ⟨j, hj⟩ := not_forall.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

theorem scalarCubeResidueWeights_support (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I+1)*M ≤ L)
    (x : IntegerScalarCubeBox I L)
    (hx : (scalarCubeResidueWeights I L M hL m r hm hmM hsize).weight x ≠ 0) :
    ∀ i, ((x i : ℤ) : ZMod (m i)) = r i := by
  classical
  apply (mem_scalarCubeResidueSet L m r x).mp
  by_contra hnot
  apply hx
  simp only [scalarCubeResidueWeights, FiniteProbabilityWeights.condition, hnot, ite_false, zero_div]

theorem scalarCubeResiduePi_support {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I+1)*M j ≤ L j)
    (x : ∀ j, IntegerScalarCubeBox I (L j))
    (hx : (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).weight x ≠ 0) :
    ∀ j i, ((x j i : ℤ) : ZMod (m j i)) = r j i := by
  intro j
  apply scalarCubeResidueWeights_support I (L j) (M j) (hL j) (m j) (r j) (hm j) (hmM j) (hsize j) (x j)
  intro hz
  apply hx
  exact Finset.prod_eq_zero (Finset.mem_univ j) hz

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI

namespace Erdos3

theorem hasBoundedScalarPeriod_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (B : ℕ) (h : HasBoundedScalarPeriod L B) :
    L.toAddSubgroup.index ≤ B ^ Fintype.card I := by
  obtain ⟨a, ha, haB, hperiod⟩ := h
  let : NeZero a := ⟨ha.ne'⟩
  exact (residueLatticeImage_index_le L a hperiod).trans (Nat.pow_le_pow_left haB _)

end Erdos3

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RootDifferencePeriod
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rootDifferenceMatrix_period {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) (a : ℤ)
    (hperiod : integerScalarLattice I a ≤ D.mulVecLin.range) :
    integerScalarLattice (Unit ⊕ I) a ≤ (rootDifferenceMatrix root D).mulVecLin.range := by
  rintro y ⟨z, rfl⟩
  have hz : a • (fun i => z (Sum.inr i)) ∈ integerScalarLattice I a :=
    ⟨fun i => z (Sum.inr i), rfl⟩
  obtain ⟨v, hv⟩ := hperiod hz
  refine ⟨Sum.elim (fun _ : Unit => a * z (Sum.inl ()) - ∑ j, root j * v j) v, ?_⟩
  change rootDifferenceMatrix root D *ᵥ _ = a • z
  rw [rootDifferenceMatrix_mulVec]
  funext i
  cases i with
  | inl i => cases i; simp
  | inr i => exact congrFun hv i

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport
namespace OAI

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitFreeProfile_integrable {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0) :
    Integrable (splitFreeProfile f g) := by
  apply (splitFreeProfile_continuous hf hg).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (J ⊕ N → ℝ) × (I → ℝ)) (max R S))
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hp (splitFreeProfile_zero_outside hfs hgs p h)

theorem splitFreeProfile_integral {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0) :
    (∫ p, splitFreeProfile f g p) = (∫ p, f p) * ∫ n, g n := by
  have hfi : Integrable f := by
    apply hf.integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : (J → ℝ) × (I → ℝ)) R)
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra! h
    exact hp (hfs p h)
  have hi := splitFreeProfile_integrable hf hg hfs hgs
  rw [Measure.volume_eq_prod, integral_prod _ hi]
  have heq (y : J ⊕ N → ℝ) :
      (∫ x : I → ℝ, splitFreeProfile f g (y, x)) =
        splitInputProfile (fun p : (J → ℝ) × (N → ℝ) => (∫ x, f (p.1, x)) * g p.2) y := by
    unfold splitFreeProfile splitInputProfile
    exact integral_mul_const (g (fun n => y (.inr n)))
      (fun x => f ((fun j => y (.inl j)), x))
  simp_rw [heq]
  rw [splitInputProfile_integral, Measure.volume_eq_prod,
    integral_prod_mul (fun y : J → ℝ => ∫ x, f (y, x)) g, ← integral_prod f hfi]
  rfl

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

namespace Erdos3

open scoped NNReal

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI

namespace Erdos3

open scoped BigOperators Matrix Classical

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix

theorem integerMatrix_fromCols_range {I J N : Type*} [Fintype J] [Fintype N]
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    (Matrix.fromCols B C).mulVecLin.range = B.mulVecLin.range ⊔ C.mulVecLin.range := by
  ext v
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨B *ᵥ (fun j => x (.inl j)), ⟨_, rfl⟩,
      C *ᵥ (fun n => x (.inr n)), ⟨_, rfl⟩, ?_⟩
    exact (Matrix.fromCols_mulVec B C x).symm.trans hx
  · rintro ⟨b, ⟨x, rfl⟩, c, ⟨y, rfl⟩, h⟩
    refine ⟨Sum.elim x y, ?_⟩
    change Matrix.fromCols B C *ᵥ Sum.elim x y = v
    rw [Matrix.fromCols_mulVec_sumElim]
    exact h

theorem pivotFullImage_eq_range {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) :
    pivotFullImage A B = (Matrix.fromCols A B).mulVecLin.range :=
  (integerMatrix_fromCols_range A B).symm

end Erdos3

namespace Erdos3

open scoped Matrix Classical

end Erdos3

namespace Erdos3

open scoped Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

end Erdos3

namespace Erdos3

open scoped NNReal Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarSpatialScaleBounds
namespace OAI

namespace Erdos3

theorem integerColumnEquiv_range {I J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix I J ℤ) (e : K ≃ J) : (A.submatrix id e).mulVecLin.range = A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  change Submodule.span ℤ (Set.range (fun k => fun i => A i (e k))) =
    Submodule.span ℤ (Set.range (fun j => fun i => A i j))
  congr 1
  ext v
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨e k, hk⟩
  · rintro ⟨j, hj⟩
    exact ⟨e.symm j, by simpa only [e.apply_symm_apply] using hj⟩

theorem selectedSpatial_full_image {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) :
    pivotFullImage (selectedSpatialPivot root D s) (selectedSpatialFreeColumns root D s) =
      (rootDifferenceMatrix root D).mulVecLin.range := by
  rw [pivotFullImage_eq_range, selectedSpatial_fromCols]
  exact integerColumnEquiv_range _ _

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerNormalizedJetColumns
namespace OAI

namespace Erdos3

open scoped BigOperators

theorem real_monomial_eval_div_scale {K : Type*} (e : K →₀ ℕ) (x T : K → ℝ) :
    MvPolynomial.eval (fun k => x k / T k) (MvPolynomial.monomial e (1 : ℝ)) =
      MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ)) / monomialScale T e := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, monomialScale, Finsupp.prod,
    div_pow, Finset.prod_div_distrib]

theorem integer_monomial_eval_cast {K : Type*} (e : K →₀ ℕ) (x : K → ℤ) :
    (MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℤ)) : ℝ) =
      MvPolynomial.eval (fun k => (x k : ℝ)) (MvPolynomial.monomial e (1 : ℝ)) := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, Int.cast_prod, Int.cast_pow]

theorem normalizedIntegerMonomialJetMatrix_eq {α K O J : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℤ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows)
      (fun j => H / monomialScale T (e j)) (fun _ => H) =
    realJetMatrix (fun j => MvPolynomial.monomial (e j) 1)
      (fun t k => (vertices t k : ℝ) / T k) rows := by
  ext o j
  rw [normalizedIntegerColumns_entry_div]
  change ((booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
    (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o) : ℤ) : ℝ) *
      (H / monomialScale T (e j)) / H =
    booleanCoefficient (fun t => MvPolynomial.eval (fun k => (vertices t k : ℝ) / T k)
      (MvPolynomial.monomial (e j) (1 : ℝ))) (rows o)
  have hcast := booleanCoefficient_map (Int.castRingHom ℝ)
    (fun t => MvPolynomial.eval (vertices t) (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o)
  change ((booleanCoefficient _ (rows o) : ℤ) : ℝ) =
    booleanCoefficient (fun t => (MvPolynomial.eval (vertices t)
      (MvPolynomial.monomial (e j) (1 : ℤ)) : ℝ)) (rows o) at hcast
  rw [hcast]
  simp only [real_monomial_eval_div_scale, integer_monomial_eval_cast]
  rw [booleanCoefficient_div]
  simp [div_eq_mul_inv, hH, mul_assoc, mul_comm]

theorem realAffineCube_normalized_integer {α K : Type*}
    (root : K → ℤ) (difference : α → K → ℤ) (T : K → ℝ) (t : Finset α) (k : K) :
    realAffineCube (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) t k =
        (integerAffineCube root difference t k : ℝ) / T k := by
  simp only [realAffineCube, integerAffineCube, Int.cast_add, Int.cast_sum,
    add_div, Finset.sum_div]

theorem normalizedBoundedIntegerJetMatrix_eq {α K O : Type*}
    [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (boundedDegreeIntegerJetMatrix root difference h rows)
      (fun e => H / monomialScale T e.val) (fun _ => H) =
    boundedDegreeRealJetMatrix (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) h rows := by
  have hv : (fun t k => (integerAffineCube root difference t k : ℝ) / T k) =
      realAffineCube (fun k => (root k : ℝ) / T k)
        (fun r k => (difference r k : ℝ) / T k) := by
    funext t k
    exact (realAffineCube_normalized_integer root difference T t k).symm
  have he := normalizedIntegerMonomialJetMatrix_eq
    (fun e : BoundedIntegerExponent K h => e.val) (integerAffineCube root difference) rows T hH
  rw [hv] at he
  exact he

end Erdos3

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

theorem scalarKernelJet_extended_period {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [Fintype N]
    {L B : ℕ} {κ : ℝ} (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (h : ℕ) (rows : O → Finset I)
    (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) (C : Matrix O N ℤ) :
    HasBoundedScalarPeriod (Matrix.fromCols (scalarKernelIntegerJet x h rows) C).mulVecLin.range (B ^ h) := by
  obtain ⟨a, ha, haB, hp⟩ := hx.2
  refine ⟨a ^ h, pow_pos ha h, Nat.pow_le_pow_left haB h, ?_⟩
  rw [integerMatrix_fromCols_range, Nat.cast_pow]
  exact (boundedDegreeIntegerJetMatrix_period _ _ (a : ℤ) hp h rows hr hrows).trans le_sup_left

theorem scalarKernelJet_extended_index {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [Fintype N]
    {L B : ℕ} {κ : ℝ} (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (h : ℕ) (rows : O → Finset I)
    (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) (C : Matrix O N ℤ) :
    (Matrix.fromCols (scalarKernelIntegerJet x h rows) C).mulVecLin.range.toAddSubgroup.index ≤
      (B ^ h) ^ Fintype.card O :=
  hasBoundedScalarPeriod_index_le _ _ (scalarKernelJet_extended_period selection x hx h rows hr hrows C)

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

theorem coefficientImageMultiplier_nonneg {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) : 0 ≤ coefficientImageMultiplier A v := by
  classical
  unfold coefficientImageMultiplier
  split <;> positivity

theorem coefficientImageMultiplier_le_index {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) :
    coefficientImageMultiplier A v ≤ (A.mulVecLin.range.toAddSubgroup.index : ℝ) := by
  classical
  unfold coefficientImageMultiplier
  split <;> simp

theorem monomialCoefficientMatrix_residue_eq {α K I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (vertices vertices' : Finset α → K → ℤ) (rows : I → Finset α) (m : ℕ)
    (hv : ∀ t, integerResidueMap K m (vertices t) = integerResidueMap K m (vertices' t)) :
    integerResidueMatrix (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices rows) m =
      integerResidueMatrix (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices' rows) m :=
  integerJetMatrix_residue_eq _ _ _ _ _ (fun _ t _ => hv t)

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

open scoped Matrix

variable {I I' J : Type*} [Fintype J]

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_fiber {G H : Type*} [Fintype G] [Nonempty G]
    [DecidableEq H] (f : G → H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
  classical
  rw [pmf_map_toReal_indicator, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem uniformPMF_map_hom_image {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      if y ∈ f.range then (Nat.card f.range : ℝ)⁻¹ else 0 := by
  classical
  rw [uniformPMF_map_fiber]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have he := AddMonoidHom.card_fiber_eq_of_mem_range f hy
      (show (0 : H) ∈ Set.range f from ⟨0, f.map_zero⟩)
    have hk : (Finset.univ.filter (fun x => f x = 0)).card = Fintype.card f.ker := by
      simp [Fintype.card_subtype, AddMonoidHom.mem_ker]
    have hc : Fintype.card f.ker * Fintype.card f.range = Fintype.card G := by
      simpa only [AddSubgroup.index_ker, Nat.card_eq_fintype_card] using f.ker.card_mul_index
    rw [he, hk, ← hc, Nat.cast_mul, Nat.card_eq_fintype_card]
    have hkn : (Fintype.card f.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp only [hy, ite_false]
    have hz : Finset.univ.filter (fun x => f x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, (Finset.mem_filter.mp hx).2⟩
    simp [hz]

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_integral {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : (∫ x, affineProductProfile c w x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun i => affineProbabilityProfile (c i) (w i)) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [affineProbabilityProfile_integral _ (hw _), Finset.prod_const_one]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem affineProductProfileLip_le_exp (I : Type*) [Fintype I]
    {δ : ℝ≥0} {t : ℝ} (hi : (δ : ℝ)⁻¹ ≤ Real.exp t) :
    (affineProductProfileLip I δ : ℝ) ≤ Real.exp (affineProfileLogBound (Fintype.card I) t) := by
  have hn : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (probabilityProfileLipschitz : ℝ) := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  simp only [affineProductProfileLip, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_inv]
  calc
    _ ≤ Real.exp (Fintype.card I : ℝ) * Real.exp (probabilityProfileLipschitz : ℝ) *
        (Real.exp t)^(Fintype.card I + 1) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [affineProfileLogBound, Nat.cast_add, Nat.cast_one]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {O J : D → Type*}
  [∀ d, Fintype (O d)] [∀ d, Fintype (J d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_toReal (p : FiniteProbabilityWeights X) (x : X) :
    (p.toPMF x).toReal = p.weight x := by
  rw [toPMF_apply, ENNReal.toReal_ofReal (p.nonneg x)]

theorem toPMF_bind_apply {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    (p.toPMF.bind q) y = ∑ x, ENNReal.ofReal (p.weight x) * q x y := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply]

theorem toPMF_bind_toReal {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    ((p.toPMF.bind q) y).toReal = p.mean (fun x => (q x y).toReal) := by
  rw [toPMF_bind_apply, ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (p.nonneg _), mean]

theorem toPMF_pi {J : Type*} [Fintype J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    [∀ j, MeasurableSpace (Ω j)] [∀ j, MeasurableSingletonClass (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) :
    (pi p).toPMF = Erdos3.dependentProductPMF (fun j => (p j).toPMF) := by
  ext x
  rw [toPMF_apply, Erdos3.dependentProductPMF_apply]
  change ENNReal.ofReal (∏ j, (p j).weight (x j)) = ∏ j, ENNReal.ofReal ((p j).weight (x j))
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (p j).nonneg (x j))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {O : Type*} [Fintype O]

theorem integerRowMassTent_range {K : ℝ} (hK : 0 ≤ K) (z : O → ℤ) (x : O → ℝ) :
    0 ≤ integerRowMassTent K z x ∧ integerRowMassTent K z x ≤ K ^ Fintype.card O := by
  refine ⟨Finset.prod_nonneg (fun i _ => (integerMassTent_range K hK (z i) (x i)).1), ?_⟩
  simpa only [integerRowMassTent, Finset.prod_const, Finset.card_univ] using
    Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).1)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).2)

theorem integerRowMassTent_grid {K : ℝ} (hK : 0 < K) (z k : O → ℤ) :
    integerRowMassTent K z (fun i => (k i : ℝ) / K) =
      if z = k then K ^ Fintype.card O else 0 := by
  classical
  by_cases he : z = k
  · subst z
    simp [integerRowMassTent, integerMassTent_grid K hK]
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ k i := Function.ne_iff.mp he
    have hz : integerMassTent K (z i) ((k i : ℝ) / K) = 0 := by
      rw [integerMassTent_grid K hK]
      simp [Ne.symm hi]
    simp only [he, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem integerRowMassTent_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (z : O → ℤ) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassTent (K : ℝ) z) := by
  have hf (i : O) : LipschitzWith (2 * K ^ 2) (fun x : O → ℝ => integerMassTent K (z i) (x i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ ≤ (2 * (K : ℝ) ^ 2) * |x i - y i| := integerMassTent_difference K K.coe_nonneg (z i) (x i) (y i)
      _ ≤ _ := by
        simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow, Real.dist_eq] using
          mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (by positivity : 0 ≤ 2 * (K : ℝ) ^ 2)
  exact (bounded_lipschitz_real_prod _ hK hf (fun i x => by
    rw [abs_of_nonneg (integerMassTent_range K K.coe_nonneg (z i) (x i)).1]
    exact (integerMassTent_range K K.coe_nonneg (z i) (x i)).2)).2

theorem integerRowMassTent_integrable {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    Integrable (fun z => integerRowMassTent K z x) p.toMeasure := by
  apply (integrable_const (K ^ Fintype.card O)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integerRowMassTent_range hK z x).1]
    exact (integerRowMassTent_range hK z x).2)

theorem integerRowMassInterpolation_range {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    0 ≤ integerRowMassInterpolation K p x ∧ integerRowMassInterpolation K p x ≤ K ^ Fintype.card O := by
  refine ⟨integral_nonneg (fun z => (integerRowMassTent_range hK z x).1), ?_⟩
  have h := integral_mono (integerRowMassTent_integrable hK p x) (integrable_const (K ^ Fintype.card O))
    (fun z => (integerRowMassTent_range hK z x).2)
  simpa only [integerRowMassInterpolation, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using h

theorem integerRowMassInterpolation_grid {K : ℝ} (hK : 0 < K) (p : PMF (O → ℤ)) (k : O → ℤ) :
    integerRowMassInterpolation K p (fun i => (k i : ℝ) / K) =
      K ^ Fintype.card O * (p k).toReal := by
  classical
  have he : (fun z => integerRowMassTent K z (fun i => (k i : ℝ) / K)) =
      Set.indicator {k} (fun _ => K ^ Fintype.card O) := by
    funext z
    simp only [integerRowMassTent_grid hK, Set.indicator_apply, Set.mem_singleton_iff]
  rw [integerRowMassInterpolation, he, integral_indicator (measurableSet_singleton k), integral_singleton,
    measureReal_def, PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k), smul_eq_mul, mul_comm]

theorem integerRowMassInterpolation_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (p : PMF (O → ℤ)) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassInterpolation (K : ℝ) p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖integerRowMassInterpolation (K : ℝ) p x - integerRowMassInterpolation (K : ℝ) p y‖ ≤ _
  rw [integerRowMassInterpolation, integerRowMassInterpolation,
    ← integral_sub (integerRowMassTent_integrable K.coe_nonneg p x) (integerRowMassTent_integrable K.coe_nonneg p y)]
  have h := norm_integral_le_of_norm_le_const (μ := p.toMeasure)
    (f := fun z => integerRowMassTent (K : ℝ) z x - integerRowMassTent (K : ℝ) z y)
    (C := (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O : ℝ≥0) * dist x y)
    (Filter.Eventually.of_forall (fun z => by
      simpa only [dist_eq_norm] using (integerRowMassTent_lipschitz K hK z).dist_le_mul x y))
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {O : Type*} [Fintype O]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {O : Type*} [Fintype O]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem integerMonomialArrayPolynomial_principal_sum {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hzero : ∀ j, j ≠ j₀ → j ∉ P → a j = 0) :
    integerMonomialArrayPolynomial e a =
      MvPolynomial.C (a j₀) + ∑ j ∈ P, MvPolynomial.monomial (e j) (a j) := by
  classical
  have hsum : (∑ j ∈ insert j₀ P, MvPolynomial.monomial (e j) (a j)) =
      ∑ j, MvPolynomial.monomial (e j) (a j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hne : j ≠ j₀ := fun he => hj (he ▸ Finset.mem_insert_self _ _)
    have hnot : j ∉ P := fun hp => hj (Finset.mem_insert_of_mem hp)
    simp [hzero j hne hnot]
  rw [integerMonomialArrayPolynomial, ← hsum, Finset.sum_insert hj₀, he₀]
  rfl

theorem productBlockExponent_monomial_int {V : Type*} {h : ℕ}
    (principal : Fin h → V) (c : ℤ) :
    MvPolynomial.monomial (productBlockExponent principal) c =
      MvPolynomial.C c * ∏ v, MvPolynomial.X (principal v) := by
  rw [productBlockExponent, MvPolynomial.monomial_sum_index]
  rfl

theorem integerPrincipalPolynomial_eval {D G : Type*} [Fintype D] [Fintype G]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (hd : 0 < h d)
    (a : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → ℤ)
    (hzero : ∀ e, e ≠ constantCoefficientSlot _ _ → e ∉ principalCoefficientSlots h d → a e = 0)
    (x : SamplerTupleIndex G B h → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B d,
        a (principalCoefficientSlot h d b) * ∏ v : Fin (h d), x (.inr ⟨d, b, v⟩) := by
  classical
  rw [integerMonomialArrayPolynomial_principal_sum Subtype.val a
    (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
    (constantCoefficientSlot_not_principal h d hd) rfl hzero]
  simp only [map_add, map_sum, MvPolynomial.eval_C]
  congr 1
  rw [principalCoefficientSlots, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro b _
    change MvPolynomial.eval x
      (MvPolynomial.monomial (productBlockExponent (fun v => .inr ⟨d, b, v⟩)) _) = _
    rw [productBlockExponent_monomial_int]
    simp only [map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  · intro b _ b' _ hb
    exact principalCoefficientSlot_injective h d hd hb

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)


end Erdos3

end

section

namespace Erdos3

variable {J V : Type*}
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem progression_slice_endpoint_geometry {L step H : ℕ} (c : ℤ)
    (hL : 0 < L) (hstep : 0 < step) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ)) :
    let lower := (c : ℝ) / L
    let width := (step : ℝ) * ((H : ℝ) - 1) / L
    0 ≤ lower ∧ δ / 2 ≤ width ∧ |lower| + |width| ≤ 1 ∧
      (step : ℝ) / L ≤ 2 / ((H : ℝ) - 1) := by
  have hbase := hsubset (integerProgressionSupport_point c step H hstep 0 (by omega))
  have hlast := hsubset (integerProgressionSupport_point c step H hstep (H - 1) (by omega))
  have hc : (0 : ℝ) ≤ c := by
    have hh : 0 ≤ c := by simpa using (Finset.mem_Ico.mp hbase).1
    exact_mod_cast hh
  have hh : (c : ℝ) + (step : ℝ) * ((H : ℝ) - 1) < L := by
    have hh := (Finset.mem_Ico.mp hlast).2
    have he : (c : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] using he
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep1 : (1 : ℝ) ≤ step := by exact_mod_cast hstep
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  rw [card_integerProgressionSupport c step H hstep] at hdense
  have hwidth : δ / 2 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := by
    apply (le_div_iff₀ hLp).mpr
    have h1 : (H : ℝ) / 2 ≤ (H : ℝ) - 1 := by linarith
    have h2 : (H : ℝ) - 1 ≤ (step : ℝ) * ((H : ℝ) - 1) := by nlinarith
    nlinarith
  have hw0 : 0 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := (half_pos hδ).le.trans hwidth
  refine ⟨div_nonneg hc hLp.le, hwidth, ?_, ?_⟩
  · rw [abs_of_nonneg (div_nonneg hc hLp.le), abs_of_nonneg hw0, ← add_div]
    exact (div_le_one hLp).mpr hh.le
  · apply (le_div_iff₀ (by linarith : 0 < (H : ℝ) - 1)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLp).mpr
    linarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

theorem integerMappedCubeTuple_residue {Z X K α : Type*}
    (input : K → Option α → Z ⊕ X) (z : Z → ℤ) (x y : X → ℤ) (m : ℕ)
    (hxy : integerResidueMap X m x = integerResidueMap X m y) (t : Finset α) :
    integerResidueMap K m (integerMappedCubeTuple input z x t) =
      integerResidueMap K m (integerMappedCubeTuple input z y t) := by
  apply integerAffineCube_residue_eq
  · funext k
    change ((Sum.elim z x (input k none) : ℤ) : ZMod m) =
      ((Sum.elim z y (input k none) : ℤ) : ZMod m)
    cases input k none with
    | inl j => rfl
    | inr j => exact congrFun hxy j
  · funext i k
    change ((Sum.elim z x (input k (some i)) : ℤ) : ZMod m) =
      ((Sum.elim z y (input k (some i)) : ℤ) : ZMod m)
    cases input k (some i) with
    | inl j => rfl
    | inr j => exact congrFun hxy j

theorem integerMappedJetMatrix_residue {Z X K α I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : I → Finset α) (x y : X → ℤ) (m : ℕ)
    (hxy : integerResidueMap X m x = integerResidueMap X m y) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows x) m =
      integerResidueMatrix (integerMappedJetMatrix e input z rows y) m :=
  monomialCoefficientMatrix_residue_eq e _ _ rows m (integerMappedCubeTuple_residue input z x y m hxy)

end Erdos3

end

section

namespace Erdos3

theorem integerMappedCubeTuple_residue_both {Z X K α : Type*}
    (input : K → Option α → Z ⊕ X) (z w : Z → ℤ) (x y : X → ℤ) (q : ℕ)
    (hzw : integerResidueMap Z q z = integerResidueMap Z q w)
    (hxy : integerResidueMap X q x = integerResidueMap X q y) (t : Finset α) :
    integerResidueMap K q (integerMappedCubeTuple input z x t) =
      integerResidueMap K q (integerMappedCubeTuple input w y t) := by
  apply integerAffineCube_residue_eq
  · funext k
    change ((Sum.elim z x (input k none) : ℤ) : ZMod q) =
      ((Sum.elim w y (input k none) : ℤ) : ZMod q)
    cases input k none with
    | inl j => exact congrFun hzw j
    | inr j => exact congrFun hxy j
  · funext i k
    change ((Sum.elim z x (input k (some i)) : ℤ) : ZMod q) =
      ((Sum.elim w y (input k (some i)) : ℤ) : ZMod q)
    cases input k (some i) with
    | inl j => exact congrFun hzw j
    | inr j => exact congrFun hxy j

theorem integerMappedJetMatrix_residue_both {Z X K α I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (z w : Z → ℤ) (rows : I → Finset α) (x y : X → ℤ) (q : ℕ)
    (hzw : integerResidueMap Z q z = integerResidueMap Z q w)
    (hxy : integerResidueMap X q x = integerResidueMap X q y) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows x) q =
      integerResidueMatrix (integerMappedJetMatrix e input w rows y) q :=
  monomialCoefficientMatrix_residue_eq e _ _ rows q
    (integerMappedCubeTuple_residue_both input z w x y q hzw hxy)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

namespace FiniteProbabilityWeights

theorem toPMF_map_toReal {X Y : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → Y) (y : Y) :
    ((p.toPMF.map f) y).toReal = p.mean (fun x => if f x = y then 1 else 0) := by
  change ((p.toPMF.bind (fun x => PMF.pure (f x))) y).toReal = _
  rw [toPMF_bind_toReal]
  congr 1
  funext x
  by_cases h : f x = y
  · simp [PMF.pure_apply, h]
  · have h' : y ≠ f x := Ne.symm h
    simp [PMF.pure_apply, h, h']

end FiniteProbabilityWeights

section IntegerSourceLaw

variable (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
variable (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
variable (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
variable (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
variable (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal)


end IntegerSourceLaw

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SignedSplitCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {R E F I J : Type*} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] [Fintype I] [Fintype J]

theorem signedSplitCoordinates_symm_apply (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (bK : Basis I R (LinearMap.ker q)) (bI : Basis J R F)
    (z : J → R) (w : I → R) :
    (signedSplitCoordinates q s hs bK bI).symm (z, w) =
      (bK.equivFun.symm w).val - s (bI.equivFun.symm z) := by
  change (bK.equivFun.symm w).val + s (bI.equivFun.symm (-z)) = _
  rw [map_neg, map_neg, sub_eq_add_neg]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

open Submodule _root_.Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem standardEuclideanLinearEquiv_apply (J : Type*) [Fintype J] (z : J → ℤ) (i : J) :
    (standardEuclideanLinearEquiv J z).val i = (z i : ℝ) := by
  have h := latticeBasisEquiv_coordinates (standardEuclideanLattice J)
    (EuclideanSpace.basisFun J ℝ).toBasis rfl z i
  have he : (latticeBasisEquiv (standardEuclideanLattice J)
      (EuclideanSpace.basisFun J ℝ).toBasis rfl z).val =
      (standardEuclideanLinearEquiv J z).val := rfl
  rw [he] at h
  simpa only [Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr] using h

theorem standardEuclideanLinearEquiv_eq_point (J : Type*) [Fintype J] (z : J → ℤ) :
    standardEuclideanLinearEquiv J z = standardEuclideanPoint J z := by
  apply Subtype.ext
  ext i
  exact standardEuclideanLinearEquiv_apply J z i

end Erdos3

end

section

namespace Erdos3

variable (J : Type*) [Fintype J]

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

variable [Fintype I] [Fintype J]

theorem latticeSignedCoordinates_symm_apply (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ))
    (z : J → ℤ) (w : I → ℤ) :
    ((latticeSignedCoordinates Λ W bW bP).symm (z, w)).val =
      (bW.equivFun.symm w).val.val - (latticeIntegerLift Λ W bP z).val := by
  rw [latticeSignedCoordinates, signedSplitCoordinates_symm_apply]
  simp only [Submodule.coe_sub, Basis.map_equivFun, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  rfl

theorem latticeSignedCoordinates_reconstruction (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (x : Λ) :
    x.val + (latticeIntegerLift Λ W bP (latticeSignedCoordinates Λ W bW bP x).1).val =
      (bW.equivFun.symm (latticeSignedCoordinates Λ W bW bP x).2).val.val := by
  have h := latticeSignedCoordinates_symm_apply Λ W bW bP
    (latticeSignedCoordinates Λ W bW bP x).1 (latticeSignedCoordinates Λ W bW bP x).2
  change ((latticeSignedCoordinates Λ W bW bP).symm (latticeSignedCoordinates Λ W bW bP x)).val = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact eq_sub_iff_add_eq.mp h

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductChartReference
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem ennreal_smul_sigmaFinite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (c : ℝ≥0∞) (hc : c ≠ ∞) : SigmaFinite (c • μ) where
  out' := ⟨{
    set := spanningSets μ
    set_mem := fun _ => trivial
    finite := by
      intro i
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top hc.lt_top (measure_spanningSets_lt_top μ i)
    spanning := iUnion_spanningSets μ }⟩

theorem piChart_reference_map {I : Type*} [Fintype I] {X Y : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (ν : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (ν i)]
    (q : ∀ i, X i → Y i) (hq : ∀ i, Measurable (q i)) (S : ∀ i, Set (X i))
    (hmap : ∀ i, ((μ i).restrict (S i)).map (q i) = (ν i).restrict (q i '' S i)) :
    ((Measure.pi μ).restrict (Set.univ.pi S)).map (fun x i => q i (x i)) =
      (Measure.pi ν).restrict ((fun x i => q i (x i)) '' Set.univ.pi S) := by
  let : ∀ i, SigmaFinite (((μ i).restrict (S i)).map (q i)) := by
    intro i
    rw [hmap i]
    infer_instance
  rw [Measure.restrict_pi_pi, Measure.pi_map_pi (fun i => (hq i).aemeasurable)]
  simp_rw [hmap]
  rw [← Measure.restrict_pi_pi]
  congr 1
  exact (Set.piMap_image_univ_pi q S).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

theorem pi_count_measure {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] [∀ i, Countable (X i)] :
    Measure.pi (fun i => (Measure.count : Measure (X i))) =
      (Measure.count : Measure (∀ i, X i)) := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

theorem uniformPMF_toMeasure_pi {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] :
    (PMF.uniformOfFintype (∀ i, X i)).toMeasure =
      Measure.pi (fun i => (PMF.uniformOfFintype (X i)).toMeasure) := by
  apply Measure.ext_of_singleton
  intro x
  rw [(PMF.uniformOfFintype (∀ i, X i)).toMeasure_apply_singleton x (measurableSet_singleton x),
    Measure.pi_singleton]
  have he (i) : (PMF.uniformOfFintype (X i)).toMeasure {x i} =
      (Fintype.card (X i) : ℝ≥0∞)⁻¹ := by
    rw [(PMF.uniformOfFintype (X i)).toMeasure_apply_singleton (x i) (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
  simp only [he, PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  exact ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _))

theorem pi_smul_finite {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (c : I → ℝ≥0∞) (hc : ∀ i, c i ≠ ∞) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  let : ∀ i, SigmaFinite (c i • μ i) := fun i => ennreal_smul_sigmaFinite (μ i) (c i) (hc i)
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem mixedArrayRegroup_apply {I Z J : Type*} (x : (I → J → ℝ) × (Z → J → ℤ)) (j : J) :
    mixedArrayRegroup I Z J x j = (fun i => x.1 i j, fun z => x.2 z j) := rfl

theorem mixedScalarArrayLaw_probability {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    IsProbabilityMeasure (mixedScalarArrayLaw c w p) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  unfold mixedScalarArrayLaw
  infer_instance

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators ENNReal

theorem mixedArrayRegroup_volume_count (I Z O : Type*) [Fintype I] [Fintype Z] [Fintype O] :
    MeasurePreserving (mixedArrayRegroup I Z O) (mixedArrayReference I Z O)
      (Measure.pi (fun _ : O => (volume : Measure (I → ℝ)).prod (Measure.count : Measure (Z → ℤ)))) := by
  simpa only [mixedArrayReference, volume_pi, pi_count_measure] using
    (mixedArrayRegroup_measurePreserving (fun _ : I => fun _ : O => (volume : Measure ℝ))
      (fun _ : Z => fun _ : O => (Measure.count : Measure ℤ)))

variable {E I Z O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [Fintype I] [Fintype Z] (o : OrthonormalBasis I ℝ E)

variable [Fintype O]

theorem orthonormalArrayChart_measurePreserving :
    MeasurePreserving (orthonormalArrayChart (O := O) (Z := Z) o) (mixedArrayReference I Z O)
      (Measure.pi (fun _ : O => (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))) := by
  have h := measurePreserving_pi
    (fun _ : O => (volume : Measure (I → ℝ)).prod (Measure.count : Measure (Z → ℤ)))
    (fun _ : O => (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))
    (fun _ => orthonormalMixedChart_measurePreserving (J := Z) o)
  exact h.comp (mixedArrayRegroup_volume_count I Z O)

theorem orthonormalArrayChart_scaled_reference (c : ℝ≥0∞) (hc : c ≠ ∞) :
    MeasurePreserving (orthonormalArrayChart (O := O) (Z := Z) o)
      (c ^ Fintype.card O • mixedArrayReference I Z O)
      (Measure.pi (fun _ : O => c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))) := by
  refine ⟨(orthonormalArrayChart o).measurable, ?_⟩
  rw [Measure.map_smul,
    (orthonormalArrayChart_measurePreserving o).map_eq,
    pi_smul_finite _ _ (fun _ => hc)]
  simp only [Finset.prod_const, Finset.card_univ]

theorem arrayResidueChart_measurePreserving {R : Type*} [MeasurableSpace R]
    (ν : Measure R) [SigmaFinite ν] (c : ℝ≥0∞) (hc : c ≠ ∞) :
    MeasurePreserving (arrayResidueChart (O := O) (Z := Z) o)
      ((c ^ Fintype.card O • mixedArrayReference I Z O).prod (Measure.pi (fun _ : O => ν)))
      (Measure.pi (fun _ : O => (c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ))).prod ν)) := by
  let : SigmaFinite (c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ))) :=
    ennreal_smul_sigmaFinite _ c hc
  have h₁ := (orthonormalArrayChart_scaled_reference (O := O) (Z := Z) o c hc).prod
    (MeasurePreserving.id (Measure.pi (fun _ : O => ν)))
  have h₂ := (measurePreserving_arrowProdEquivProdArrow (E × (Z → ℤ)) R O
    (fun _ => c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))
    (fun _ => ν)).symm (MeasurableEquiv.arrowProdEquivProdArrow (E × (Z → ℤ)) R O)
  exact h₂.comp h₁

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Matrix NNReal

variable {J R I : Type*} [Fintype J] [Fintype R]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open Module Submodule BohrLattice.MinkowskiSecondBox
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J]

theorem standardLatticeCoordinates_reconstruction (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (β : D → ℤ) :
    (standardEuclideanPoint D β).val +
        (standardLatticeIntegerLift W bP hP
          (fun j => standardLatticeCoordinates W bW bP hP β (Sum.inl j))).val =
      (bW.equivFun.symm (fun i => standardLatticeCoordinates W bW bP hP β (Sum.inr i))).val.val := by
  rw [← standardEuclideanLinearEquiv_eq_point]
  exact latticeSignedCoordinates_reconstruction (standardEuclideanLattice D) W bW
    (integerBasisOfReal (projectedIntegerLattice W) bP hP) (standardEuclideanLinearEquiv D β)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module _root_.Set
open scoped ENNReal

variable {E T I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

end Erdos3

end

section

namespace Erdos3

open Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)

theorem normalizedChartRegion_measurable
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    MeasurableSet (normalizedChartRegion W b hb Ω) := by
  have he := normalizedLatticeQuotient_embedding W b hb hΩm hΩ
  have hr : Set.range (fun x : normalizedLatticePoint W b ⁻¹' Ω =>
      normalizedLatticeQuotient W b hb x.val) = normalizedChartRegion W b hb Ω := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hr]
  exact he.measurableSet_range

variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

theorem normalizedChartReference_map
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    (normalizedChartReference W b Ω).map (normalizedLatticeQuotient W b hb) =
      μ.restrict (normalizedChartRegion W b hb Ω) := by
  have hc : ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice D) W)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos _ volume)).ne'
  rw [normalizedChartReference,
    Measure.map_smul,
    normalizedLatticeQuotient_map_restrict W b hb μ hΩm hΩ, smul_smul,
    ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul]
  rfl

include hb μ in
theorem normalizedChartReference_finite
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    IsFiniteMeasure (normalizedChartReference W b Ω) := by
  have : IsFiniteMeasure ((normalizedChartReference W b Ω).map
      (normalizedLatticeQuotient W b hb)) := by
    rw [normalizedChartReference_map W b hb μ hΩm hΩ]
    infer_instance
  exact Measure.isFiniteMeasure_of_map (normalizedLatticeQuotient_measurable W b hb).aemeasurable

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem orthonormalMixedChart_sum_zsmul (o : OrthonormalBasis I ℝ W)
    {S : Type*} (s : Finset S) (a : S → ℤ)
    (x : S → (I → ℝ) × (Fin n → ℤ)) :
    orthonormalMixedChart o (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • orthonormalMixedChart o (x i) := by
  change orthonormalMixedChartHom W o _ = _
  simp only [map_sum, map_zsmul, orthonormalMixedChartHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerTailZero
namespace OAI

section

namespace Erdos3

section Coordinate

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : L^h < K → (principalSamplingGapRatio (principalProfileSize R P.card)*L)^h ≤ K)
variable (hεL : 8*(probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J)*L)

local notation "laws" => allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL
  e he R σ hR hσ hgap hεL

theorem allocatedIntegerCoordinate_tail_pure (hsmall : K ≤ L^(s+1))
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∉ P) : laws j = PMF.pure 0 := by
  classical
  unfold allocatedIntegerPolynomialCoordinatePMF integerPolynomialCoordinatePMF
  simp only [hj₀, hjP, ↓reduceIte]
  exact integerAxisTailPMF_small T hT hK hL hTL (tailProfileSize_pos hR hσ _) hεL (e j) (he j) hsmall

theorem allocatedIntegerCoordinate_tail_zero (hsmall : K ≤ L^(s+1))
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∉ P) {k : ℤ} (hk : k ∈ (laws j).support) : k = 0 := by
  rw [allocatedIntegerCoordinate_tail_pure P j₀ h K L s hh hK hL T hT hTL e he R σ hR hσ
    hgap hεL hsmall j hj₀ hjP] at hk
  simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk

end Coordinate

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortDependence
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (j : Fin m) (i : Fin (n j))
variable {X α O : Type} [Fintype X] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (p : FiniteProbabilityWeights X)
variable (a : X → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ)
variable (ha : ∀ x, p.weight x ≠ 0 → ∀ d,
  a x d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
variable (vertices : X → Finset α → LayerSamplerVariables G I n B → ℤ)
variable (rows : O → Finset α) (q : ℕ) (hrows : ∀ o, (rows o).card ≤ q)
variable (hx : ∀ x, p.weight x ≠ 0 → ∀ o t, t ∈ (rows o).powerset →
  ∀ v, |(vertices x t v : ℝ)| ≤ layerSamplerBox B U basis S v)

include hR hσ S hσ1 ha hrows hx

variable {T : ℕ} (hT : 0 < T) (hTS : T ≤ S.value)
variable (hshort : integerAxisSideLength (j.val+1) (basisAxisScale (basis j) i) S.value
  (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) < T)

include hT hTS hshort

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)

theorem allocatedLayerInteger_moderate_tail_zero
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (d : Slots) (hd₀ : d ≠ constantCoefficientSlot _ _)
    (hdP : d ∉ layerIntegerPrincipalSlots B j i) : a d = 0 := by
  exact allocatedIntegerCoordinate_tail_zero (layerIntegerPrincipalSlots B j i)
    (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value (layerTailDegree m)
    (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
    (layerSamplerBox B U basis S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (layerSamplerBox_le B U basis S) Subtype.val
    (fun e => e.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j) hmoderate d hd₀ hdP (ha d)

theorem allocatedLayerInteger_moderate_eval
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (x : LayerSamplerVariables G I n B → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B ⟨j, Sum.inr i⟩,
        a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
          ∏ v : Fin (j.val+1), x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) := by
  exact integerPrincipalPolynomial_eval (layerSamplerDegree I n) ⟨j, Sum.inr i⟩
    (Nat.zero_lt_succ _) a
    (allocatedLayerInteger_moderate_tail_zero B U basis hR hσ S j i hmoderate a ha) x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeCoverMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeQuotient_compact : CompactSpace (E ⧸ Λ.toAddSubgroup) := by
  have hc := IsZLattice.isCompact_range_of_periodic Λ
    (QuotientAddGroup.mk' Λ.toAddSubgroup) QuotientAddGroup.continuous_mk (by
      intro x z hz
      have hz0 : QuotientAddGroup.mk' Λ.toAddSubgroup z = 0 :=
        (QuotientAddGroup.eq_zero_iff z).mpr hz
      rw [map_add, hz0, add_zero])
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective _)] at hc
  exact ⟨hc⟩

variable [MeasurableSpace E] [BorelSpace E]

theorem latticeCover_measurePreserving
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (d : ℕ) (hd : 0 < d) :
    MeasurePreserving (quotientIntegerCover Λ.toAddSubgroup d) μ μ := by
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  let : CompactSpace (E ⧸ Λ.toAddSubgroup) := latticeQuotient_compact Λ
  let : BorelSpace (E ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  let : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving
    (quotientIntegerCover_continuous Λ.toAddSubgroup d)
    (quotientIntegerCover_surjective Λ.toAddSubgroup d hd) rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelRestriction
namespace OAI

section

namespace Erdos3

open MeasureTheory Topology
open scoped BigOperators

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) [Fintype C.ker]

theorem finiteFiberAverage_eq_of_map_eq (f : G → ℝ) {x y : G} (hxy : C x = C y) :
    finiteFiberAverage C f x = finiteFiberAverage C f y := by
  classical
  have hk : x - y ∈ C.ker := by
    change C (x - y) = 0
    rw [map_sub, hxy, sub_self]
  unfold finiteFiberAverage
  congr 1
  apply Fintype.sum_equiv (Equiv.addLeft (⟨x - y, hk⟩ : C.ker))
  intro k
  congr 1
  change x + k.val = y + (x - y + k.val)
  abel

theorem finiteFiberAverage_integral_uniform
    [MeasurableSpace C.ker] [MeasurableSingletonClass C.ker] (f : G → ℝ) (x : G) :
    (∫ k : C.ker, f (x + k.val) ∂(PMF.uniformOfFintype C.ker).toMeasure) =
      finiteFiberAverage C f x := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, finiteFiberAverage]

variable [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem finiteFiberAverage_continuous {f : G → ℝ} (hf : Continuous f) :
    Continuous (finiteFiberAverage C f) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro k _
  exact hf.comp (continuous_id.add continuous_const)

theorem finiteFiberAverage_factor [CompactSpace G] [TopologicalSpace H] [T2Space H]
    (hC : Continuous C) (hCs : Function.Surjective C) {f : G → ℝ} (hf : Continuous f) :
    ∃ g : H → ℝ, Continuous g ∧ ∀ x, g (C x) = finiteFiberAverage C f x := by
  let e : ContinuousMap G H := ⟨C, hC⟩
  have hq : IsQuotientMap e := IsQuotientMap.of_surjective_continuous hCs hC
  let a : ContinuousMap G ℝ := ⟨finiteFiberAverage C f, finiteFiberAverage_continuous C hf⟩
  have hfac : Function.FactorsThrough a e :=
    fun _ _ hxy => finiteFiberAverage_eq_of_map_eq C f hxy
  let g := hq.lift a hfac
  refine ⟨g, g.continuous, ?_⟩
  intro x
  exact DFunLike.congr_fun (hq.lift_comp a hfac) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
variable (C : G →+ H) [Fintype C.ker]

theorem finiteFiberAverage_integral_of_invariant
    (μ : Measure G) [IsFiniteMeasure μ]
    (hμ : ∀ k : C.ker, μ.map (fun x => x + k.val) = μ)
    (f : G → ℝ) (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ x, finiteFiberAverage C f x ∂μ) = ∫ x, f x ∂μ := by
  have hi (k : C.ker) : Integrable (fun x => f (x + k.val)) μ :=
    Integrable.of_bound (hf.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      B (ae_of_all μ (fun x => hB _))
  have he (k : C.ker) : (∫ x, f (x + k.val) ∂μ) = ∫ x, f x ∂μ := by
    have hm : Measurable (fun x : G => x + k.val) :=
      (continuous_id.add continuous_const).measurable
    have h := integral_map hm.aemeasurable
      (hf.aestronglyMeasurable (μ := μ.map (fun x => x + k.val)))
    rw [hμ k] at h
    exact h.symm
  unfold finiteFiberAverage
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hi k)]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card C.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

variable [T2Space G] [MeasurableSpace X] [MeasurableAdd₂ G]

omit [IsTopologicalAddGroup G] in
theorem finiteKernelLiftLaw_integral (ρ : Measure X) [IsFiniteMeasure ρ]
    (s : X → G) (hs : Measurable s) (f : G → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ y, f y ∂finiteKernelLiftLaw C ρ s) = ∫ x, finiteFiberAverage C f (s x) ∂ρ := by
  have hL : Measurable (fun p : X × C.ker => s p.1 + p.2.val) :=
    (hs.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd)
  have hi : Integrable (fun p : X × C.ker => f (s p.1 + p.2.val))
      (ρ.prod (PMF.uniformOfFintype C.ker).toMeasure) :=
    Integrable.of_bound (hf.comp hL).aestronglyMeasurable B (ae_of_all _ (fun p => hB _))
  rw [finiteKernelLiftLaw, integral_map hL.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi]
  exact integral_congr_ae (ae_of_all ρ (fun x => finiteFiberAverage_integral_uniform C f (s x)))

theorem finiteKernelLiftLaw_eq [CompactSpace G] [HasOuterApproxClosed G]
    [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (hC : Continuous C) (hCs : Function.Surjective C)
    (μ : Measure G) [IsFiniteMeasure μ]
    (hμ : ∀ k : C.ker, μ.map (fun x => x + k.val) = μ)
    (ρ : Measure X) [IsFiniteMeasure ρ] (s : X → G) (hs : Measurable s)
    (hbase : ρ.map (C ∘ s) = μ.map C) :
    finiteKernelLiftLaw C ρ s = μ := by
  let _ : IsFiniteMeasure (finiteKernelLiftLaw C ρ s) := by
    unfold finiteKernelLiftLaw
    infer_instance
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  obtain ⟨g, hgc, hg⟩ := finiteFiberAverage_factor C hC hCs φ.continuous
  calc
    (∫ y, φ y ∂finiteKernelLiftLaw C ρ s) =
        ∫ x, finiteFiberAverage C φ (s x) ∂ρ :=
      finiteKernelLiftLaw_integral C ρ s hs φ φ.continuous.measurable φ.norm_coe_le_norm
    _ = ∫ x, g (C (s x)) ∂ρ := by simp_rw [hg]
    _ = ∫ y, g y ∂ρ.map (C ∘ s) :=
      (integral_map (hC.measurable.comp hs).aemeasurable hgc.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂μ.map C := by rw [hbase]
    _ = ∫ x, g (C x) ∂μ := integral_map hC.measurable.aemeasurable hgc.aestronglyMeasurable
    _ = ∫ x, finiteFiberAverage C φ x ∂μ := by simp_rw [hg]
    _ = ∫ x, φ x ∂μ :=
      finiteFiberAverage_integral_of_invariant C μ hμ φ φ.continuous φ.norm_coe_le_norm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem uniformPMF_map_equiv {R S : Type*} [Fintype R] [Fintype S]
    [Nonempty R] [Nonempty S] (e : R ≃ S) :
    (PMF.uniformOfFintype R).map e = PMF.uniformOfFintype S := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [pmf_map_injective_at _ e e.injective, PMF.uniformOfFintype_apply,
    PMF.uniformOfFintype_apply, Fintype.card_congr e]

theorem finiteKernelLiftLaw_relabel {G H X R : Type*}
    [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableAdd₂ G] [MeasurableSpace X]
    (C : G →+ H) [Fintype C.ker] [Fintype R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    (e : R ≃ C.ker) (ρ : Measure X) [SFinite ρ]
    (s : X → G) (hs : Measurable s) :
    (ρ.prod (PMF.uniformOfFintype R).toMeasure).map
        (fun p => s p.1 + (e p.2).val) = finiteKernelLiftLaw C ρ s := by
  have he : Measurable e := measurable_of_finite _
  have hm : (PMF.uniformOfFintype R).toMeasure.map e =
      (PMF.uniformOfFintype C.ker).toMeasure := by
    rw [PMF.toMeasure_map e _ he, uniformPMF_map_equiv]
  have hp : ρ.prod (PMF.uniformOfFintype C.ker).toMeasure =
      (ρ.prod (PMF.uniformOfFintype R).toMeasure).map (Prod.map id e) := by
    rw [← hm, ← Measure.map_prod_map _ _ measurable_id he, Measure.map_id]
  rw [finiteKernelLiftLaw, hp, Measure.map_map]
  · rfl
  · exact (hs.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd)
  · exact measurable_id.prodMap he

theorem finiteKernelLiftLaw_basisResidues {E I X : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype I]
    (Γ : AddSubgroup E) (b : Module.Basis I ℤ Γ)
    [TopologicalSpace (E ⧸ Γ)] [T2Space (E ⧸ Γ)]
    [MeasurableSpace (E ⧸ Γ)] [BorelSpace (E ⧸ Γ)] [MeasurableAdd₂ (E ⧸ Γ)]
    [MeasurableSpace X] (d : ℕ) [NeZero d]
    [Fintype (quotientIntegerCover Γ d).ker]
    (ρ : Measure X) [SFinite ρ] (s : X → E ⧸ Γ) (hs : Measurable s) :
    (ρ.prod (PMF.uniformOfFintype (I → ZMod d)).toMeasure).map
        (fun p => s p.1 + (coverKernelBasisEquiv Γ b d (Nat.pos_of_ne_zero (NeZero.ne d)) p.2).val) =
      finiteKernelLiftLaw (quotientIntegerCover Γ d) ρ s :=
  finiteKernelLiftLaw_relabel _ (coverKernelBasisEquiv Γ b d _).toEquiv ρ s hs

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
variable [T2Space G] [CompactSpace G] [HasOuterApproxClosed G]
variable [MeasurableAdd₂ G]
variable [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
variable [MeasurableSpace X] (C : G →+ H) [Fintype C.ker]

theorem finiteKernelLift_density (hC : Continuous C) (hCs : Function.Surjective C)
    (μ : Measure G) [μ.IsAddLeftInvariant] (ν : Measure H)
    (hmp : MeasurePreserving C μ ν)
    (D : H → ℝ) (hD : Measurable D) (hi : Integrable D ν) (h0 : ∀ y, 0 ≤ D y)
    (ρ : Measure X) [IsFiniteMeasure ρ] (s : X → G) (hs : Measurable s)
    (hbase : ρ.map (C ∘ s) = realDensityMeasure ν D) :
    finiteKernelLiftLaw C ρ s = realDensityMeasure μ (fun x => D (C x)) := by
  have hci : Integrable (fun x => D (C x)) μ := hmp.integrable_comp_of_integrable hi
  let _ := realDensityMeasure_finite μ (fun x => D (C x)) hci (fun x => h0 _)
  refine finiteKernelLiftLaw_eq C hC hCs (realDensityMeasure μ (fun x => D (C x)))
    ?_ ρ s hs ?_
  · intro k
    rw [realDensityMeasure_map_add_right]
    congr 1
    funext x
    rw [map_sub, show C k.val = 0 from k.property, sub_zero]
  · rw [measurePreserving_realDensity_map μ ν C hmp D hD hi h0]
    exact hbase

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem realDensityMeasure_indicator_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS : MeasurableSet S) :
    realDensityMeasure μ (S.indicator (fun _ => (1 : ℝ))) = μ.restrict S := by
  have he : (fun x => ENNReal.ofReal (S.indicator (fun _ => (1 : ℝ)) x)) =
      S.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [realDensityMeasure, he]
  exact withDensity_indicator_one hS

theorem finiteKernelLift_restrict {G H X : Type*}
    [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [CompactSpace G] [HasOuterApproxClosed G] [MeasurableAdd₂ G]
    [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace X] (C : G →+ H) [Fintype C.ker]
    (hC : Continuous C) (hCs : Function.Surjective C)
    (μ : Measure G) [μ.IsAddLeftInvariant] (ν : Measure H) [IsFiniteMeasure ν]
    (hmp : MeasurePreserving C μ ν) {S : Set H} (hS : MeasurableSet S)
    (ρ : Measure X) [IsFiniteMeasure ρ] (s : X → G) (hs : Measurable s)
    (hbase : ρ.map (C ∘ s) = ν.restrict S) :
    finiteKernelLiftLaw C ρ s = μ.restrict (C ⁻¹' S) := by
  have hb : ρ.map (C ∘ s) = realDensityMeasure ν (S.indicator (fun _ => (1 : ℝ))) := by
    rw [realDensityMeasure_indicator_one ν hS]
    exact hbase
  have he : (fun x => S.indicator (fun _ => (1 : ℝ)) (C x)) =
      (C ⁻¹' S).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : C x ∈ S <;> simp [hx]
  rw [finiteKernelLift_density C hC hCs μ ν hmp _ (measurable_const.indicator hS)
    ((integrable_const (1 : ℝ)).indicator hS)
    (fun x => by by_cases hx : x ∈ S <;> simp [hx]) ρ s hs hb,
    he, realDensityMeasure_indicator_one μ (hS.preimage hC.measurable)]

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

theorem normalizedCoverLift_reference (d : ℕ) (hd : 0 < d)
    [Fintype (quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d).ker]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    finiteKernelLiftLaw
      (quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d)
      (normalizedChartReference W b Ω) (normalizedCoverLift W b hb d) =
    μ.restrict (quotientIntegerCover
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d ⁻¹'
        normalizedChartRegion W b hb Ω) := by
  let Λ := latticeSection (standardEuclideanLattice D) W
  let : DiscreteTopology Λ.toAddSubgroup := latticeSection_discrete (standardEuclideanLattice D) W
  let : IsClosed (Λ.toAddSubgroup : Set W) := AddSubgroup.isClosed_of_discrete
  let : CompactSpace (W ⧸ Λ.toAddSubgroup) := latticeQuotient_compact Λ
  let : BorelSpace (W ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  let : IsFiniteMeasure (normalizedChartReference W b Ω) :=
    normalizedChartReference_finite W b hb μ hΩm hΩ
  apply finiteKernelLift_restrict _ (quotientIntegerCover_continuous _ d)
    (quotientIntegerCover_surjective _ d hd) μ μ
    (latticeCover_measurePreserving Λ μ d hd)
    (normalizedChartRegion_measurable W b hb hΩm hΩ) _ _
    (normalizedCoverLift_continuous W b hb d).measurable
  have he : (quotientIntegerCover Λ.toAddSubgroup d ∘ normalizedCoverLift W b hb d) =
      normalizedLatticeQuotient W b hb := by
    funext x
    exact normalizedCoverLift_projection W b hb d hd x
  rw [he]
  exact normalizedChartReference_map W b hb μ hΩm hΩ

theorem normalizedCoverResidues_reference
    (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
    (d : ℕ) [NeZero d]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    ((normalizedChartReference W b Ω).prod
      (PMF.uniformOfFintype (R → ZMod d)).toMeasure).map
        (fun p => normalizedCoverLift W b hb d p.1 +
          (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
            bW d (Nat.pos_of_ne_zero (NeZero.ne d)) p.2).val) =
    μ.restrict (quotientIntegerCover
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d ⁻¹'
        normalizedChartRegion W b hb Ω) := by
  let Λ := latticeSection (standardEuclideanLattice D) W
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let : Fintype (quotientIntegerCover Λ.toAddSubgroup d).ker :=
    Fintype.ofEquiv (R → ZMod d) (coverKernelBasisEquiv Λ.toAddSubgroup bW d hd).toEquiv
  let : DiscreteTopology Λ.toAddSubgroup := latticeSection_discrete (standardEuclideanLattice D) W
  let : IsClosed (Λ.toAddSubgroup : Set W) := AddSubgroup.isClosed_of_discrete
  let : BorelSpace (W ⧸ Λ.toAddSubgroup) := QuotientAddGroup.borelSpace
  let : IsFiniteMeasure (normalizedChartReference W b Ω) :=
    normalizedChartReference_finite W b hb μ hΩm hΩ
  rw [finiteKernelLiftLaw_basisResidues Λ.toAddSubgroup bW d _ _
    (normalizedCoverLift_continuous W b hb d).measurable]
  exact normalizedCoverLift_reference W b hb μ d hd hΩm hΩ

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedArrayIntegerImage
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D I J O Z : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

omit [Fintype I] in
theorem mixedArrayIntegerImage_regroup (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Z → J → ℤ)) (r : O) :
    mixedArrayRegroup I Z O (mixedArrayIntegerImage A x) r =
      ∑ j, A r j • mixedArrayRegroup I Z J x j := by
  apply Prod.ext
  · funext i
    simp only [mixedArrayIntegerImage, mixedArrayRegroup_apply, Prod.fst_sum,
      Finset.sum_apply]
    change (∑ j, (A r j : ℝ) * x.1 i j) = ∑ j, A r j • x.1 i j
    exact Finset.sum_congr rfl (fun j _ => Int.cast_smul_eq_zsmul ℝ (A r j) (x.1 i j))
  · funext z
    simp only [mixedArrayIntegerImage, mixedArrayRegroup_apply, Prod.snd_sum,
      Finset.sum_apply]
    change (∑ j, A r j * x.2 z j) = ∑ j, A r j • x.2 z j
    simp only [smul_eq_mul]

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (o : OrthonormalBasis I ℝ W)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedRealCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedRealPoint_coordinates (x : EuclideanSpace ℝ D) :
    mixedRealPoint W b o (mixedRealCoordinates W b o x) = x := by
  change (normalizedOrthogonalChart W b).symm
    ((orthonormalChart o) ((orthonormalChart o).symm ((normalizedOrthogonalChart W b) x).1),
      ((normalizedOrthogonalChart W b) x).2) = x
  simp only [ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformImageLawCongruence
namespace OAI

section

namespace Erdos3

open scoped Classical Matrix

theorem uniformPMF_map_hom_eq_of_range_eq {G G' H : Type*}
    [AddCommGroup G] [AddCommGroup G'] [AddCommGroup H]
    [Fintype G] [Fintype G'] [Fintype H]
    (f : G →+ H) (g : G' →+ H) (h : f.range = g.range) :
    (PMF.uniformOfFintype G).map f = (PMF.uniformOfFintype G').map g := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [uniformPMF_map_hom_image, h]

theorem integerResidueMatrix_range_eq_of_integer_range_eq
    {I J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix I J ℤ) (B : Matrix I K ℤ)
    (h : A.mulVecLin.range = B.mulVecLin.range) (d : ℕ) :
    (integerResidueMatrix A d).mulVecLin.toAddMonoidHom.range =
      (integerResidueMatrix B d).mulVecLin.toAddMonoidHom.range := by
  ext y
  change (∃ x, integerResidueMatrix A d *ᵥ x = y) ↔
    (∃ x, integerResidueMatrix B d *ᵥ x = y)
  rw [← integerMatrixResidue_mem, ← integerMatrixResidue_mem, h]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [Fintype α] [∀ j, Fintype (J j)] [∀ j, Fintype (B j)] in
theorem coefficientDeckJetMap_coordinate (d : ℕ) (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (i : B j) :
    (fun t => coefficientDeckJetMap root D rows d r j t i) =
      integerResidueMatrix (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ
        (fun e => r j e i) := by
  funext t
  change (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e) i =
    ∑ e, ((boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e : ℤ) : ZMod d) * r j e i
  simp only [Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]

theorem coefficientDeckKernel_jets (d : ℕ) (hd : 0 < d)
    (r : CoefficientDeckResidues (K := K) B d) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root D rows (coefficientDeckKernelEquiv U bW d hd r).val j t =
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root D rows d r j t)).val := by
  rw [euclideanCoefficientJetMap_apply]
  simp_rw [coefficientDeckKernelEquiv_coordinate]
  let f := ((quotientIntegerCover
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d).ker.subtype).comp
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd).toAddMonoidHom
  change (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • f (r j e)) =
    f (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e)
  simp only [map_sum, map_zsmul]

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientDeckSample_jets (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root D rows (canonicalCoefficientDeckSample U bW b hb o d hd x r) j t =
      euclideanCoefficientJetMap U root D rows (canonicalCoefficientCoverLift U b hb o d x) j t +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root D rows d r j t)).val := by
  simp only [canonicalCoefficientDeckSample, map_add, Pi.add_apply,
    coefficientDeckKernel_jets]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] in
theorem coefficientDeckJetMap_mem_range_iff (d : ℕ)
    (v : ∀ j, O j → B j → ZMod d) :
    v ∈ (coefficientDeckJetMap root D rows d).range ↔
      ∀ j (i : B j), (fun t => v j t i) ∈
        (integerResidueMatrix (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d).mulVecLin.toAddMonoidHom.range := by
  constructor
  · rintro ⟨a, rfl⟩ j i
    exact ⟨(fun e => a j e i), (coefficientDeckJetMap_coordinate root D rows d a j i).symm⟩
  · intro h
    change ∀ j (i : B j), ∃ a, integerResidueMatrix
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ a = (fun t => v j t i) at h
    choose a ha using h
    refine ⟨(fun j e i => a j i e), ?_⟩
    funext j t i
    exact (congrFun (coefficientDeckJetMap_coordinate root D rows d (fun j e i => a j i e) j i) t).trans
      (congrFun (ha j i) t)

omit [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] in
theorem coefficientDeckJetMap_range_eq_of_integer_range_eq
    (root' : K → ℤ) (D' : Matrix α K ℤ)
    (h : ∀ j, (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range =
      (boundedCoefficientJetMatrix root' D' (j.val + 1) (rows j)).mulVecLin.range)
    (d : ℕ) :
    (coefficientDeckJetMap (B := B) root D rows d).range =
      (coefficientDeckJetMap (B := B) root' D' rows d).range := by
  ext v
  simp only [coefficientDeckJetMap_mem_range_iff]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro i
  rw [integerResidueMatrix_range_eq_of_integer_range_eq _ _ (h j) d]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val+1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val+1) → PMF ℤ)

theorem coefficientAxisLaw_probability [Fintype K]
    (hw : ∀ j i d, 0 < w j i d) (a : LayerSamplerAxis I n) :
    IsProbabilityMeasure (coefficientAxisLaw c w p a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    let : ∀ d, IsProbabilityMeasure (affineCoefficientMeasure (c j i d) (w j i d)) :=
      fun d => affineCoefficientMeasure_probability _ (hw j i d)
    change IsProbabilityMeasure (Measure.pi (fun d => affineCoefficientMeasure (c j i d) (w j i d)))
    infer_instance
  | inr i =>
    change IsProbabilityMeasure (Measure.pi (fun d => (p j i d).toMeasure))
    infer_instance

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

theorem coefficientJetAxisMap_measurable {K : Type*} [Fintype K] {O : Fin m → Type*}
    [∀ j, Fintype (O j)]
    (A : ∀ j, Matrix (O j) (BoundedCoefficientExponent K (j.val+1)) ℤ)
    (a : LayerSamplerAxis I n) : Measurable (coefficientJetAxisMap A a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    exact (matrixSupCLM ((A j).map (Int.cast : ℤ → ℝ))).continuous.measurable
  | inr i =>
    change Measurable (fun c : BoundedCoefficientExponent K (j.val+1) → ℤ => A j *ᵥ c)
    exact measurable_of_countable _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory

variable {m : ℕ} {I O O' : Fin m → Type*} {n : Fin m → ℕ}
variable (e : ∀ j, O' j ≃ O j)

variable [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]

variable (P : LayerSamplerAxis I n → Prop)

variable [∀ j, Fintype (I j)] [DecidablePred P]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem latticeDeckInteger_coordinates (z : Fin n → ℤ) (w : I → ℤ) :
    standardLatticeCoordinates W bW b hb (latticeDeckInteger W bW b hb z w) =
      Sum.elim z w := LinearEquiv.apply_symm_apply _ _

theorem latticeDeckInteger_reconstruction (z : Fin n → ℤ) (w : I → ℤ) :
    (standardEuclideanPoint D (latticeDeckInteger W bW b hb z w)).val +
        (standardLatticeIntegerLift W b hb z).val =
      (bW.equivFun.symm w).val.val := by
  have h := standardLatticeCoordinates_reconstruction W bW b hb
    (latticeDeckInteger W bW b hb z w)
  simpa only [latticeDeckInteger_coordinates, Sum.elim_inl, Sum.elim_inr] using h

theorem normalizedLatticePoint_linear_lift (x : W × (Fin n → ℤ)) :
    normalizedLatticePoint W b x = x.1.val +
      (Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val := by
  rw [normalizedLatticePoint_eq_sheet W b hb, standardLatticeIntegerLift_projection]
  unfold latticeSheetPoint
  rw [latticeBasisEquiv_synthesis]

theorem normalizedDeckPoint_identity (x : W × (Fin n → ℤ)) (w : I → ℤ) :
    (normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val).val =
      normalizedLatticePoint W b x +
        (standardEuclideanPoint D (latticeDeckInteger W bW b hb x.2 w)).val := by
  have hβ := latticeDeckInteger_reconstruction W bW b hb x.2 w
  have hs := W.starProjection_add_starProjection_orthogonal
    (standardLatticeIntegerLift W b hb x.2).val
  change (W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val +
    (Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val = _ at hs
  rw [normalizedLatticePoint_linear_lift W b hb]
  change x.1.val - (W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val +
    (bW.equivFun.symm w).val.val = _
  rw [← hs] at hβ
  rw [← hβ]
  abel

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical
attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [Fintype K]

end Erdos3.VectorPolynomial

end

end OAI

end


