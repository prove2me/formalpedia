-- Prove2me | Definitions.Def_OAIE3v2B082
-- name    : OAIE3v2B082
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:22:13.673526+00:00
-- url     : https://prove2.me/theorems/004b3157-cb08-4d8f-a188-ce70ea287631
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 83 of 311
-- statement:
--   Definitions bundle 83 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B044`, `OAIE3v2B045`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B050`, `OAIE3v2B057`, `OAIE3v2B059`, `OAIE3v2B061`, `OAIE3v2B063` of this split.
--
--   Modules: `Dynamics/AllocatedCandidateNativeMajorBudget.lean`, `Dynamics/AllocatedCandidateStageScalarBudget.lean`, `Dynamics/CandidatePhysicalOrdinaryBudget.lean`, `Dynamics/CanonicalDetectedScaleInputBudget.lean`, `Dynamics/CoefficientAmbientBudget.lean`, `Dynamics/PositiveModerateBudget.lean`, `Estimates/AllocatedAmbientLogBounds.lean`, `Estimates/AllocatedCandidateCommonFastGeometry.lean`, `Estimates/AllocatedCandidateGeneratedFastTerminal.lean`, `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/AllocatedWholeProfileEnvelope.lean`, `Estimates/CoefficientJetScalar.lean`, `Estimates/ContainedProgressionCubeMap.lean`, `Estimates/PositiveRetainedDenominatorLog.lean`, `Estimates/PreparedModularGeneralDetectorNativeBounds.lean`, `Estimates/UnitCoefficientSourceMarginal.lean`, `Fourier/AllocatedMaskedCoefficientFourier.lean`, `Fourier/FixedPrincipalCoefficientSpectrum.lean`, `Fourier/UniformSpectrumLogBounds.lean`, `Geometry/ScalarCubeProductSupport.lean`, `Lattices/AffineCoefficientLaw.lean`, `Lattices/AllocatedAffineScaleEnvelope.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/JointAffineL1Parameter.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/PrincipalResidueMixture.lean`, `Lattices/ResidueSliceNormalizedCell.lean`, `Lattices/StandardLatticeCoordinates.lean`, `Linear/AllocatedCanonicalProjectionBudget.lean`, `Linear/AllocatedFixedKernelReplacement.lean`, `Linear/AllocatedKernelScaleWithCutoff.lean`, `Linear/KernelComparisonScales.lean`, `Linear/KernelProjectionPresentPivotIdeal.lean`, `Linear/KernelScaleIndependence.lean`, `Linear/WeightedDualVector.lean`, `Polynomial/IntegerPolynomialAffineLaw.lean`, `Polynomial/JointPolynomialDilationGrid.lean`, `Polynomial/PolynomialKernelValues.lean`, `Probability/ContainedProgressionCubeLaw.lean`, `Probability/DiagonalImageDensity.lean`, `Probability/RegularizedSigmaDensity.lean`, `Probability/ShiftedProductCoordinateLaw.lean`, `Sampling/CanonicalSamplerTuple.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B044
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B050
import Definitions.Def_OAIE3v2B057
import Definitions.Def_OAIE3v2B059
import Definitions.Def_OAIE3v2B061
import Definitions.Def_OAIE3v2B063

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice
variable {X : Type*} {N : X → ℕ} {q : ℕ}

def meshRounded (S : ResidueBoxSlice N q) (_hq : 0 < q) (M : ℕ)
    (hM : 0 < M) (hlen : ∀ i, 2 * M < S.length i) : ResidueBoxSlice N q where
  start i := S.start i % q + q * (M * (S.start i / q / M + 1))
  length i := M * ((S.start i / q + S.length i) / M) - M * (S.start i / q / M + 1)
  inside i j hj := by
    have h := denseResidueMeshInterval (S.start i / q) (S.length i) M hM (hlen i)
    dsimp only at h
    let offset := M * (S.start i / q / M + 1) - S.start i / q
    have ho : offset + j < S.length i := by dsimp [offset]; omega
    have he := S.inside i (offset + j) ho
    have hmod := Nat.mod_add_div (S.start i) q
    have hstart := h.2.1
    have hoff : offset + S.start i / q = M * (S.start i / q / M + 1) := by
      dsimp [offset]
      omega
    nlinarith

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal Classical

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

noncomputable def fixedSpatialBlockDensityLipschitz
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) : ℝ≥0 :=
  (fixedSpatialBlockDensityCap B *
    boxWindowTranslationBound (fun _ : X => 1) (fun _ => zero_lt_one)) *
    ‖(A.trans (ContinuousLinearEquiv.neg ℝ)).symm.toContinuousLinearMap‖₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

noncomputable def jointBooleanSampler (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) :
    (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ) :=
  sigmaAxisSampler (fun d => booleanSamplerMap (F := Fin (h d)) (c d) (sets d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ R S V : Type*} [Finite σ] [CommRing R] [Field S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

theorem eq_zero_of_eval₂_eq_zero_on_grid
    (length : σ → ℕ) (x : ∀ i, Fin (length i) → S)
    (hinj : ∀ i, Function.Injective (x i))
    {d : ℕ} {p : VectorPolynomial σ R V}
    (hp : DegreeLE (fun _ => 1) d p) (hlen : ∀ i, d < length i)
    (heval : ∀ j : ∀ i, Fin (length i), eval₂ (fun i => x i (j i)) p = 0) :
    p = 0 := by
  classical
  let e := Module.Free.chooseBasis S V
  have hcoord (k : Module.Free.ChooseBasisIndex S V) :
      coordinate (e.coord k).toAddMonoidHom p = 0 := by
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _
      (fun i => Finset.univ.image (x i))
    · intro i
      rw [Finset.card_image_of_injective _ (hinj i), Finset.card_univ,
        Fintype.card_fin]
      exact lt_of_le_of_lt
        ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
          ((degreeLE_one_iff_basis_totalDegree e d p).mp hp k)) (hlen i)
    · intro y hy
      have hy' : ∀ i, ∃ j, x i j = y i := by
        intro i
        simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hy i
      choose j hj using hy'
      have hx : (fun i => x i (j i)) = y := funext hj
      rw [← hx, ← coordinate_eval₂, heval, map_zero]
  apply coefficients.injective
  ext α
  simp only [map_zero, Finsupp.zero_apply]
  apply e.repr.injective
  ext k
  have hk := congrArg (fun polynomial : MvPolynomial σ S => polynomial.coeff α) (hcoord k)
  simpa only [coeff_coordinate, MvPolynomial.coeff_zero, map_zero,
    Finsupp.zero_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply] using hk

theorem eq_of_eval₂_eq_on_grid
    (length : σ → ℕ) (x : ∀ i, Fin (length i) → S)
    (hinj : ∀ i, Function.Injective (x i))
    {d : ℕ} {p q : VectorPolynomial σ R V}
    (hp : DegreeLE (fun _ => 1) d p) (hq : DegreeLE (fun _ => 1) d q)
    (hlen : ∀ i, d < length i)
    (heval : ∀ j : ∀ i, Fin (length i),
      eval₂ (fun i => x i (j i)) p = eval₂ (fun i => x i (j i)) q) :
    p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_eq_zero_on_grid length x hinj
  · intro α hα
    simp only [map_sub, Finsupp.sub_apply, hp α hα, hq α hα, sub_self]
  · exact hlen
  · intro j
    rw [map_sub, heval j, sub_self]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def principalTupleFlatten {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α] :
    (PrincipalTupleIndex B h → Option α → ℝ) ≃L[ℝ] (JointBlockParameter B h α → ℝ) where
  toLinearEquiv :=
    { toFun := fun x z => x ⟨z.1, z.2.1, z.2.2.1⟩ z.2.2.2
      invFun := fun a j r => a ⟨j.1, j.2.1, j.2.2, r⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


namespace Erdos3


noncomputable def scalarKernelIntegerJet {I J O : Type*} [DecidableEq I] [Fintype J]
    {L : ℕ} (x : J → IntegerScalarCubeBox I L) (h : ℕ) (rows : O → Finset I) :
    Matrix O (BoundedIntegerExponent J h) ℤ :=
  boundedDegreeIntegerJetMatrix (fun j => (x j none : ℤ)) (scalarCubeDifferenceMatrix x) h rows

theorem kernelJetCoefficientScale_pos (J : Type*) (h : ℕ) {L H : ℝ}
    (hL : 0 < L) (hH : 0 < H) (e : BoundedIntegerExponent J h) :
    0 < kernelJetCoefficientScale J h L H e :=
  div_pos hH (monomialScale_pos _ (fun _ => hL) e.val)


noncomputable def scalarKernelFixedPivot {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (hL : 0 < L) (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0) :
    (O → ℝ) ≃L[ℝ] (O → ℝ) :=
  normalizedPivotEquiv _ hs (fun i => kernelJetCoefficientScale J degree L 1 (s i))
    (fun _ => 1) (fun i => kernelJetCoefficientScale_pos J degree (by exact_mod_cast hL) zero_lt_one (s i))
    (fun _ => zero_lt_one)

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open scoped Matrix

theorem coefficientWeight_summable {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) : Summable (coefficientWeight f S) := by
  convert rectangularWeight_summable f (fun _ => 0) S hS hsupport using 1
  funext z
  change f (fun j => (z j : ℝ) / S j) = f (rectangularLatticePoint (fun _ => 0) S z)
  congr 1
  funext j
  simp only [rectangularLatticePoint, sub_zero]

noncomputable def coefficientPMF {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S) :
    PMF (J → ℤ) :=
  realWeightPMF (coefficientWeight f S) (fun _ => hf _)
    (coefficientWeight_summable f S hS hsupport) hZ

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointPolynomialDilationGrid
namespace OAI


namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

theorem abs_eval_sub_eval_normalized_mass_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x y : σ → ℝ) {M δ : ℝ} {m : ℕ}
    (hmass : realPolynomialMass (scaleMvPolynomialAxes T P) ≤ M)
    (hδ : 0 ≤ δ) (hx : ∀ i, |x i| ≤ T i) (hy : ∀ i, |y i| ≤ T i)
    (hxy : ∀ i, |x i - y i| ≤ T i * δ) (hdegree : P.totalDegree ≤ m) :
    |eval x P - eval y P| ≤ (m : ℝ) * M * δ := by
  have hunit (v : σ → ℝ) (hv : ∀ i, |v i| ≤ T i) (i : σ) : |v i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i)]
    exact (div_le_one (hT i)).mpr (hv i)
  have hdiff (i : σ) : |x i / T i - y i / T i| ≤ δ := by
    rw [← sub_div, abs_div, abs_of_pos (hT i)]
    exact (div_le_iff₀ (hT i)).mpr (by simpa only [mul_comm] using hxy i)
  have hev (v : σ → ℝ) : eval (fun i => v i / T i) (scaleMvPolynomialAxes T P) = eval v P := by
    rw [scaleMvPolynomialAxes_eval]
    apply congrArg (fun z : σ → ℝ => eval z P)
    funext i
    exact mul_div_cancel₀ (v i) (hT i).ne'
  have h := abs_eval_sub_eval_unit_mass_bound (scaleMvPolynomialAxes T P)
    (fun i => x i / T i) (fun i => y i / T i) hδ (hunit x hx) (hunit y hy) hdiff
    ((scaleMvPolynomialAxes_totalDegree_le T P).trans hdegree)
  rw [hev, hev] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg m)) hδ)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateNativeMajorBudget
namespace OAI

section

namespace Erdos3

theorem allocatedCandidateNativeMajorBudget_bounds {pNative v : ℝ}
    (hpNative : 0 ≤ pNative) (hv : 0 ≤ v) :
    0 ≤ allocatedCandidateNativeMajorBudget pNative v ∧
      pNative ≤ allocatedCandidateNativeMajorBudget pNative v ∧
      productNiltestBudget pNative ≤ allocatedCandidateNativeMajorBudget pNative v ∧
      v ≤ allocatedCandidateNativeMajorBudget pNative v := by
  have hproduct : 0 ≤ productNiltestBudget pNative :=
    (sq_nonneg (pNative + 2)).trans (productNiltestBudget_geometry hpNative)
  unfold allocatedCandidateNativeMajorBudget
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem allocatedCandidateNativeMajorBudget_nonneg {pNative v : ℝ}
    (hpNative : 0 ≤ pNative) (hv : 0 ≤ v) :
    0 ≤ allocatedCandidateNativeMajorBudget pNative v :=
  (allocatedCandidateNativeMajorBudget_bounds hpNative hv).1

theorem exists_allocated_candidate_promoted_native_major_budget (Cnative : ℕ) :
    ∃ Cmajor : ℕ, 2 ≤ Cmajor ∧ ∀ t v pNative : ℝ,
      0 ≤ t → 0 ≤ v → v ≤ t → 0 ≤ pNative →
      pNative ≤ (t + Cnative) ^ Cnative →
      allocatedCandidateNativeMajorBudget (pNative + v + 2) v ≤
        (t + Cmajor) ^ Cmajor := by
  let X : Polynomial ℕ := Polynomial.X
  let N := (X + Polynomial.C Cnative) ^ Cnative + X + 2
  let P := (N + 2) ^ 2 + N + (N + (N ^ 2 + N + 3) ^ 2) + N ^ 2 + 4 + N + X + 2
  obtain ⟨Cmajor, hCmajor, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨Cmajor, hCmajor, ?_⟩
  intro t v pNative ht hv hvt hpNative hNative
  have hpromoted : pNative + v + 2 ≤ (t + Cnative) ^ Cnative + t + 2 := by
    linarith
  apply (allocatedCandidateNativeMajorBudget_mono (by linarith) hpromoted hvt).trans
  simpa [P, N, X, Polynomial.eval₂_pow, allocatedCandidateNativeMajorBudget,
    productNiltestBudget, productObservableLipBudget] using hbudget t ht

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem functional_eq_weighted_inner (p : FiniteProbabilityWeights Ω)
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ)
    (hzero : ∀ x, p.weight x = 0 → f (Pi.single x 1) = 0) (v : Ω → ℂ) :
    f v = p.correlation v (weightedDualVector p f) := by
  rw [functional_eq_sum_coordinates, FiniteProbabilityWeights.correlation]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp [weightedDualVector, hx, hzero x hx]
  · have hxC : (p.weight x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    simp only [weightedDualVector, star_div₀, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_conj]
    field_simp

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

theorem latticeLiftSection_rightInverse (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (x : orthogonalLatticeImage Λ Wᗮ) :
    orthogonalLatticeProjection Λ Wᗮ (latticeLiftSection Λ W bP x) = x :=
  basisSurjectionSection_rightInverse _ _ _ _

variable [Fintype I] [Fintype J]

noncomputable def latticeSignedCoordinates (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) :
    Λ ≃ₗ[ℤ] (J → ℤ) × (I → ℤ) :=
  signedSplitCoordinates (orthogonalLatticeProjection Λ Wᗮ) (latticeLiftSection Λ W bP)
    (latticeLiftSection_rightInverse Λ W bP) (bW.map (orthogonalSectionKernelEquiv Λ W)) bP

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
open scoped Matrix

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J]

noncomputable def standardLatticeCoordinates (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) :
    (D → ℤ) ≃ₗ[ℤ] (J ⊕ I → ℤ) :=
  (standardEuclideanLinearEquiv D).trans
    ((latticeSignedCoordinates (standardEuclideanLattice D) W bW
      (integerBasisOfReal (projectedIntegerLattice W) bP hP)).trans
      (LinearEquiv.sumArrowLequivProdArrow J I ℤ ℤ).symm)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

theorem affineProbabilityProfile_zero (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ)
    (hx : w < |x - c|) : affineProbabilityProfile c w x = 0 := by
  have hnorm : 1 < |(x-c)/w| := by
    rw [abs_div, abs_of_pos hw]
    exact (one_lt_div hw).mpr hx
  rw [affineProbabilityProfile, smoothProbabilityProfile_zero_outside _ hnorm, mul_zero]

theorem affineProbabilityProfile_zero_outside (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ)
    (hx : |c| + w < |x|) : affineProbabilityProfile c w x = 0 := by
  apply affineProbabilityProfile_zero c hw x
  have ht : |x| ≤ |x-c| + |c| := by
    simpa only [sub_add_cancel] using abs_add_le (x-c) c
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_eq {I : Type*} [Fintype I] (c w x : I → ℝ) :
    affineProductProfile c w x = profileWidthFactor w *
      smoothProductProfile I (fun i => (x i - c i) / w i) := by
  simp only [affineProductProfile, affineProbabilityProfile, Finset.prod_mul_distrib,
    profileWidthFactor, smoothProductProfile]

theorem affineProductProfile_zero_outside {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) {R : ℝ} (hR : 0 ≤ R) (hcw : ∀ i, |c i| + w i ≤ R) :
    ∀ x, R < ‖x‖ → affineProductProfile c w x = 0 := by
  classical
  intro x hx
  by_contra hne
  apply (not_le_of_gt hx)
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  rw [Real.norm_eq_abs]
  by_contra! hi
  exact hne (Finset.prod_eq_zero (Finset.mem_univ i)
    (affineProbabilityProfile_zero_outside (c i) (hw i) (x i) ((hcw i).trans_lt hi)))

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

theorem affineProductProfile_sample {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i) (z : I → ℤ) :
    coefficientWeight (affineProductProfile c w) S z = profileWidthFactor w *
      smoothProductProfile I (fun i => ((z i : ℝ) - c i * S i) / (w i * S i)) := by
  rw [coefficientWeight, affineProductProfile_eq]
  congr 1
  congr 1
  funext i
  exact affineProfile_sample_coordinate (c i) (z i) (hw i) (hS i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PositiveModerateBudget
namespace OAI

section

namespace Erdos3

def positiveModerateLengthExponent (n : ℕ) : ℕ :=
  majorArcLengthExponent n + majorArcLengthExponent (n + 1)

def positiveModerateCoverExponent (n j : ℕ) : ℕ :=
  majorArcLengthExponent (n + 1) + majorArcCoverExponent n j +
    majorArcCoverExponent (n + 1) j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

noncomputable def integerMappedJetMatrix {Z X K α I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : I → Finset α) (x : X → ℤ) : Matrix I N ℤ :=
  integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) (integerMappedCubeTuple input z x) rows

end Erdos3

end

section

namespace Erdos3

def principalTupleIntegers {D α : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (y : PrincipalIntegerTuples B h α L) :
    JointBlockParameter B h α → ℤ :=
  fun a => (y ⟨a.1, a.2.1, a.2.2.1⟩ a.2.2.2 : ℤ)

noncomputable def principalTupleNormalized {D α : Type*} {B : D → Type*} {h : D → ℕ}
    (L : PrincipalTupleIndex B h → ℕ) (y : PrincipalIntegerTuples B h α L) :
    JointBlockParameter B h α → ℝ :=
  fun a => (principalTupleIntegers y a : ℝ)/L ⟨a.1, a.2.1, a.2.2.1⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

theorem allocatedWidthFloor_pos {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    {L : ℕ} (hL : 0 < L) (s a : ℕ) : 0 < allocatedWidthFloor R σ L s a := by
  unfold allocatedWidthFloor
  exact div_pos (lt_min (by positivity)
    (lt_min (div_pos (principalProfileSize_pos hR a) (by norm_num)) (tailProfileSize_pos hR hσ a)))
    (pow_pos (Nat.cast_pos.mpr hL) _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedLayerWidthFloor (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  Real.toNNReal (allocatedWidthFloor (R j) (σ j) L (j.val+1)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientAmbientBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def coefficientAmbientInputPolynomial (m : ℕ) : Polynomial ℕ :=
  Polynomial.C (m * (m + 1)) * (Polynomial.X + 1)^m * (Polynomial.X + 1) + Polynomial.X + 1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedAmbientLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedLayerMixedCap (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  (allocatedLayerWidthFloor (G := G) B R σ L j)⁻¹^Fintype.card (I j) *
    (allocatedLayerCommonCap (G := G) B R σ L j)^(n j)

noncomputable def allocatedLayerMixedLip (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  (allocatedLayerWidthFloor (G := G) B R σ L j)⁻¹^Fintype.card (I j) *
      (n j * allocatedLayerCommonLip (G := G) B R σ L j * (allocatedLayerCommonCap (G := G) B R σ L j)^(n j)) +
    (allocatedLayerCommonCap (G := G) B R σ L j)^(n j) *
      affineProductProfileLip (I j) (allocatedLayerWidthFloor (G := G) B R σ L j)

noncomputable def allocatedAmbientFactorCap (R σ : Fin m → ℝ) (L : ℕ) (V : Fin m → ℝ≥0) : ℝ≥0 :=
  1 + ∑ j, V j * allocatedLayerMixedCap (G := G) B R σ L j

noncomputable def allocatedAmbientLayerLip (R σ : Fin m → ℝ) (L : ℕ) (d : Fin m → ℕ)
    (C V : Fin m → ℝ≥0) (j : Fin m) : ℝ≥0 :=
  V j * (allocatedLayerMixedLip (G := G) B R σ L j * (C j * d j)) +
    (V j * allocatedLayerMixedCap (G := G) B R σ L j) * 8

noncomputable def allocatedAmbientFactorLip (R σ : Fin m → ℝ) (L : ℕ) (d : Fin m → ℕ)
    (C V : Fin m → ℝ≥0) : ℝ≥0 :=
  ∑ j, allocatedAmbientLayerLip (G := G) B R σ L d C V j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

noncomputable def coefficientAmbientBudgetExponent (m : ℕ) : ℕ :=
  (exists_natPolynomial_eval_budget (coefficientAmbientInputPolynomial m)).choose

noncomputable def allocatedFourierLogBudget (m : ℕ) (P : ℝ) : ℝ :=
  (P + allocatedAmbientLog m P + coefficientAmbientBudgetExponent m)^coefficientAmbientBudgetExponent m

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitCoefficientSourceMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def unitCoefficientSource (I : Type*) [Fintype I] : Measure (I → ℝ) :=
  realDensityMeasure volume (smoothProductProfile I)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RegularizedSigmaDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def regularizedImageDensity {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (U : Ω → I → ℝ) (δ : ℝ≥0) : (I → ℝ) → ℝ :=
  densityMixture μ (fun a => affineProductProfile (U a) (fun _ => (δ : ℝ)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineL1Parameter
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def affineSelectedJetDensity {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : I → Finset α)
    (c w : J ⊕ N → ℝ) (x : X → ℝ) : (I → ℝ) → ℝ :=
  normalizedJetDensity A F e input z rows
    (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
    (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n))) x

end Erdos3

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

noncomputable def coefficientAxisLaw [Fintype K] :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientAxisRow K a)
  | ⟨j, .inl i⟩ => Measure.pi (fun d => affineCoefficientMeasure (c j i d) (w j i d))
  | ⟨j, .inr i⟩ => Measure.pi (fun d => (p j i d).toMeasure)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialAffineLaw
namespace OAI

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
variable (hgap : L^h < K → (principalSamplingGapRatio γ*L)^h ≤ K)
variable (hεL : 8*(probabilityProfileLipschitz : ℝ) ≤ ε*L)
variable (ha : L^h < K) (henormous : L^(s+1) < K)
variable (hconst : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ*K)
variable (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
variable (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (L : ℝ)^h)

local notation "widths" => coefficientProfileWidth P j₀ ρ γ ε

include hh hL hT hTL he hγ hε hgap hεL ha henormous hconst he₀ hprincipal in
omit [Fintype J] in
theorem integerPolynomialProfile_width_large (j : J) :
    8*(probabilityProfileLipschitz : ℝ) ≤ widths j * ((K : ℝ)/monomialScale T (e j)) := by
  classical
  by_cases hj : j = j₀
  · subst j
    simpa only [coefficientProfileWidth, ↓reduceIte, he₀, monomialScale_zero, div_one] using hconst
  · by_cases hp : j ∈ P
    · simpa only [coefficientProfileWidth, hj, hp, ↓reduceIte, hprincipal j hp] using
        integerAxisPrincipal_width hh hL hγ (hgap ha)
    · simp only [coefficientProfileWidth, hj, hp, ↓reduceIte]
      calc
        _ ≤ (ε/monomialScale T (e j))*(K : ℝ) :=
          integerAxisTail_width T hT hL hTL hε hεL (e j) (he j) henormous
        _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerScalarCube_progression {I : Type*} [Fintype I] [DecidableEq I]
    {L H step : ℕ} (c : ℤ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : Option I → ℤ) (hz : IntegerScalarCube H z) :
    IntegerScalarCube L (fun i => (if i = none then c else 0) + (step : ℤ) * z i) := by
  intro t
  have ht : c + (step : ℤ) * integerScalarCubeValue z t ∈
      integerProgressionSupport c (step : ℤ) H := by
    rw [integerProgressionSupport, mem_translateSupport]
    apply Finset.mem_image.mpr
    refine ⟨integerScalarCubeValue z t, Finset.mem_Ico.mpr (hz t), ?_⟩
    change (step : ℤ) * integerScalarCubeValue z t = _
    ring
  have he : integerScalarCubeValue
      (fun i => (if i = none then c else 0) + (step : ℤ) * z i) t =
      c + (step : ℤ) * integerScalarCubeValue z t := by
    simp only [integerScalarCubeValue, ite_true, Option.some_ne_none, ite_false,
      zero_add, Finset.mul_sum, mul_add]
    ring
  rw [he]
  exact Finset.mem_Ico.mp (hsubset ht)

noncomputable def containedProgressionCubeMap (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) : IntegerScalarCubeBox I L :=
  if hz : IntegerScalarCube H (fun i => (z i : ℤ)) then
    fun i => ⟨(if i = none then c else 0) + (step : ℤ) * (z i : ℤ),
      Finset.mem_Ico.mpr ⟨(integerScalarCube_coordinates
        (integerScalarCube_progression c hsubset _ hz) i).1.le,
        (integerScalarCube_coordinates (integerScalarCube_progression c hsubset _ hz) i).2⟩⟩
  else fun _ => ⟨0, Finset.mem_Ico.mpr (by constructor <;> omega)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedProgressionCubeLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

noncomputable def containedProgressionTupleMap (v : PrincipalIntegerTuples B h α H) :
    PrincipalIntegerTuples B h α L :=
  fun j => containedProgressionCubeMap α (L j) (H j) (step j) (c j) (hL j) (hsubset j) (v j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelProjectionPresentPivotIdeal
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

theorem kernelProjectionPresentPivot_card_le {J : Type*} {r : ℕ}
    (code : Fin r → Option J) : Fintype.card (KernelProjectionPresentPivot code) ≤ r := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    (fun i : KernelProjectionPresentPivot code => i.val) Subtype.val_injective

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

noncomputable def kernelExponentEmbedding (G X : Type*) (h : ℕ) :
    BoundedIntegerExponent G h ↪ BoundedCoefficientExponent (G ⊕ X) h where
  toFun d := ⟨d.val.embDomain Function.Embedding.inl, by
    change (d.val.embDomain Function.Embedding.inl).sum (fun _ n => n) ≤ h
    rw [Finsupp.sum_embDomain]
    exact d.property⟩
  inj' := by
    intro d e hde
    exact Subtype.ext ((Finsupp.embDomain_injective Function.Embedding.inl) (congrArg Subtype.val hde))

abbrev NonkernelCoefficient (G X : Type*) (h : ℕ) :=
  UnselectedColumn (kernelExponentEmbedding G X h)

noncomputable def kernelCoefficientEquiv (G X : Type*) [Fintype G] (h : ℕ) :
    BoundedIntegerExponent G h ⊕ NonkernelCoefficient G X h ≃ BoundedCoefficientExponent (G ⊕ X) h :=
  selectedColumnEquiv (kernelExponentEmbedding G X h)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

theorem allocatedUnitProfileWidth_pos {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (a : ℕ) :
    0 < allocatedUnitProfileWidth R σ a :=
  allocatedWidthFloor_pos hR hσ zero_lt_one 0 a

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

def positiveModerateSpectrumExponent (n j : ℕ) : ℕ :=
  4 * positiveModerateCoverExponent n j * j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

noncomputable def fixedKernelInverseBound {α G O : Type*}
    [Fintype α] [DecidableEq α] [Fintype G] [DecidableEq G] [Fintype O] [DecidableEq O]
    {L : ℕ} (hL : 0 < L) (x : G → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G degree)
    (hA : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0) (κ : ℝ) : Prop :=
  ‖(scalarKernelFixedPivot hL x degree rows s hA).symm.toContinuousLinearMap‖ ≤
    kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card O) degree κ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalDetectedScaleInputBudget
namespace OAI

section

namespace Erdos3

theorem exists_slicedDetection_uniform_budget (s C : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p q a : ℝ} {count : ℕ} (G : Type*) [Fintype G],
      0 ≤ D → 0 ≤ p → 0 ≤ q → 0 ≤ a →
      (count : ℝ) ≤ D → (Fintype.card G : ℝ) ≤ D →
      slicedDetectionGainLog s C count p q a ≤ (D + p + q + a + A) ^ A ∧
      scalarKernelLogarithmicBudget (Fin (s + 1)) G
        (slicedDetectionGainLog s C count p q a + p + 4) ≤ (D + p + q + a + A) ^ A := by
  let X : Polynomial ℕ := Polynomial.X
  let g : Polynomial ℕ := (5 * X + 20) * X + X + 2 + X + 1 +
    Polynomial.C (2 ^ (s + 1)) * (X + Polynomial.C C) ^ C
  let dim : Polynomial ℕ := Polynomial.C (s + 1)
  let k : Polynomial ℕ := 2 * ((4 + 3 * (X * (dim + 1) * dim)) *
    (16 * (10 + dim + X + X * (dim + 1) + (g + X + 4)) ^ 3 + 2)) + 8
  obtain ⟨A, hA, hb⟩ := exists_natPolynomial_eval_budget (g + k)
  refine ⟨A, hA, ?_⟩
  intro D p q a count G _ hD hp hq ha hcount hG
  let R := D + p + q + a
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hDR : D ≤ R := by dsimp only [R]; linarith
  have hpR : p ≤ R := by dsimp only [R]; linarith
  have hqR : q ≤ R := by dsimp only [R]; linarith
  have haR : a ≤ R := by dsimp only [R]; linarith
  have hcR := hcount.trans hDR
  have hGR := hG.trans hDR
  let gainR := (5 * R + 20) * R + R + 2 + R + 1 + (2 ^ (s + 1) : ℕ) * (R + C) ^ C
  let kernelR := 2 * ((4 + 3 * (R * ((s + 1 : ℕ) + 1) * (s + 1 : ℕ))) *
    (16 * (10 + (s + 1 : ℕ) + R + R * ((s + 1 : ℕ) + 1) + (gainR + R + 4)) ^ 3 + 2)) + 8
  have hgainR : slicedDetectionGainLog s C count p q a ≤ gainR := by
    dsimp only [slicedDetectionGainLog, gainR]
    gcongr
  have hgain0 : 0 ≤ gainR := by dsimp only [gainR]; positivity
  have hk0 : 0 ≤ kernelR := by dsimp only [kernelR]; positivity
  have hgainActual := slicedDetectionGainLog_nonneg s C count hp hq ha
  have hkernelR : scalarKernelLogarithmicBudget (Fin (s + 1)) G
      (slicedDetectionGainLog s C count p q a + p + 4) ≤ kernelR := by
    rw [scalarKernelLogarithmicBudget_eq]
    simp only [Fintype.card_fin]
    dsimp only [kernelR]
    push_cast
    gcongr
  have hbound : gainR + kernelR ≤ (R + A) ^ A := by
    simpa [X, g, k, dim, gainR, kernelR, Polynomial.eval₂_pow] using hb R hR
  exact ⟨hgainR.trans ((le_add_of_nonneg_right hk0).trans hbound),
    hkernelR.trans ((le_add_of_nonneg_left hgain0).trans hbound)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelComparisonScales
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def kernelFamilyOutputLog {Q α J : Type*} [Fintype Q] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)] (degree : Q → ℕ) (p : ℝ) : ℝ :=
  1 + ∑ q, kernelRowOutputLog (Fintype.card α) (Fintype.card J) (Fintype.card (O q))
    (Fintype.card (BoundedIntegerExponent J (degree q))) (Fintype.card (N q)) (degree q) p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorNativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def generalDetectorCoefficientCost (m dim : ℕ) : ℕ :=
  ∑ j : Fin m, Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1))

noncomputable def preparedModularGeneralDetectorResources {α : Type*} [Semiring α]
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) (P L : α) :
    PreparedModularCanonicalDetectorResources α :=
  let Q : α := (P + K.Cperiod) ^ K.Cperiod
  let v : α := P + 8
  let w : α := P + 1
  let Dg : α := 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) + K.m + comparisonProfileBound + 8
  let Pproj : α := 4 * (L + 8) ^ 2
  let coverLog : α := (Pproj + (dim + 2 : ℕ) + K.Acover) ^ K.Acover
  let Pmass : α := (Pproj + K.Asample) ^ K.Asample
  let Vlog : α := L ^ 2 * ((layerTailDegree K.m + 1 : ℕ) * L + 1)
  let Nlog : α := (K.m * 2 ^ dim : ℕ) * (P + 8) * (1 + 4 * P)
  let Pbox : α := 2 * P ^ 2 + 8
  let Banalytic : α := Dg + 4 * P + 32
  let baseAmbient : α := Pproj + coverLog + Vlog + Nlog + Q + (layerTailDegree K.m + 1 : ℕ) * L + 3 * P + comparisonProfileBound + (2 ^ dim : ℕ) + 32
  let tq : α := dim + Q + (P + 1) + 1
  let pq : α := K.Cgrid + (dim + 1 : ℕ) * Q + (P + 1) + 4
  let gridlog : α := slicedGridGeometryLog Dg v w tq + pq
  let Fpref : α := (P + K.Cpref) ^ K.Cpref
  let sumlog : α := Pbox + P + Vlog + Nlog + Q + P
  let idealQ : α := dim + P * sumlog + (P + comparisonProfileBound + (P + 1) * sumlog) + sumlog + 1
  let ambient : α := affineAmbientPrimitiveBudget baseAmbient idealQ
  let Psample : α := Pmass + ambient + Pproj + 2 * P +
    generalDetectorCoefficientCost K.m dim + (P + (K.m + dim + 2 : ℕ)) ^ (K.m + dim + 2) + 8
  let Pside : α := Psample + Pproj + Pmass + 2 * L
  let Pnative : α := Dg + gridlog + v + Fpref + 6 * P + Banalytic
  let nativeBudget : α := ((Pnative + K.Cnative) ^ K.Cnative + K.Anorm) ^ K.Anorm
  let E : α := 3 * P + nativeBudget + 30
  let full : α := 4 * (L + 8) ^ 2
  let required : α := (Psample + K.Apert) ^ K.Apert + (Pmass + K.AmassWindow) ^ K.AmassWindow + (Pproj + K.Aproj) ^ K.Aproj + (Pside + K.Aside) ^ K.Aside + (full + E + K.Amarginal) ^ K.Amarginal
  { Q, v, w, Dg, Pproj, coverLog, Pmass, Vlog, Nlog, Pbox, Banalytic, baseAmbient, tq, pq, gridlog, Fpref, sumlog, idealQ, ambient, Psample, Pside, Pnative, nativeBudget, E, full, required }

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
namespace OAI

section

namespace Erdos3

open Module
open scoped Classical TensorProduct

theorem allocatedCandidateCommonFastGeometryLog_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedCandidateCommonFastGeometryLog p ∧
    allocatedCandidateCommonFastSectionInput p ≤ allocatedCandidateCommonFastGeometryLog p := by
  have hq := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  have hbase : 1 ≤ allocatedCandidateCommonFastSectionInput p + 2 := by linarith
  have hpow : allocatedCandidateCommonFastSectionInput p + 2 ≤
      (allocatedCandidateCommonFastSectionInput p + 2) ^ 47 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ (47 : ℕ) by omega)
  dsimp [allocatedCandidateCommonFastGeometryLog]
  constructor <;> linarith

theorem allocatedCandidateCommonFastBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    allocatedCandidateCommonFastGeometryLog p ≤ allocatedCandidateCommonFastBudget s p ∧
    NilpotentLieFiltration.pointwiseFastSectionInput s p ≤ allocatedCandidateCommonFastBudget s p ∧
    p ≤ allocatedCandidateCommonFastBudget s p := by
  have hgeom := allocatedCandidateCommonFastGeometryLog_bounds hp
  have hpoint : 0 ≤ NilpotentLieFiltration.pointwiseFastSectionInput s p := by
    dsimp [NilpotentLieFiltration.pointwiseFastSectionInput]
    positivity
  have hpg := (allocatedCandidateCommonFastSectionInput_bounds hp).2.trans hgeom.2
  dsimp [allocatedCandidateCommonFastBudget]
  constructor
  · linarith only [hpoint]
  constructor
  · linarith only [hgeom.1]
  · linarith only [hpg, hpoint]

theorem allocatedCandidateCommonFastGeneratorHeight_le {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
      Real.exp (allocatedCandidateCommonFastGeometryLog p) := by
  apply (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4)).trans
  exact Real.exp_le_exp.mpr (allocatedCandidateCommonFastGeometryLog_bounds hp).2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumLogBounds
namespace OAI

section

namespace Erdos3

def majorArcBiasLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  (denseProductDensityConstant n * (2 * 3 ^ n) ^ denseProductExponent n : ℕ) +
    ((n + 1) * majorArcBiasExponent n : ℕ) * (1 + 2 * p)

def majorArcLengthLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  majorArcLocalizationLog n p + majorArcBiasLog n p + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveRetainedDenominatorLog
namespace OAI

section

namespace Erdos3

def positiveModerateLengthLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  majorArcLengthLog n p + majorArcLengthLog (n + 1) p + 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedWholeProfileEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

@[instance_reducible]
noncomputable def fullBooleanRowSetFintype (dim degree : ℕ) :
    Fintype {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) degree} :=
  Finset.Subtype.fintype _

attribute [local instance 2000] fullBooleanRowSetFintype

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem exists_allocatedAffineL1Log_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ D P Prho Pk : ℝ,
      0 ≤ D → 0 ≤ P → 0 ≤ Prho → 0 ≤ Pk →
      allocatedAffineL1Log m D P Prho Pk ≤ (D + P + Prho + Pk + A) ^ A := by
  let X : Polynomial ℕ := Polynomial.X
  let poly := allocatedAffineL1Log m X X X X
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D P Prho Pk hD hP hPrho hPk
  let Q := D + P + Prho + Pk
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have hDQ : D ≤ Q := by dsimp [Q]; linarith
  have hPQ : P ≤ Q := by dsimp [Q]; linarith
  have hrQ : Prho ≤ Q := by dsimp [Q]; linarith
  have hkQ : Pk ≤ Q := by dsimp [Q]; linarith
  have hkernel : kernelOutputEnvelope D (4 * (P + 8)) ≤ kernelOutputEnvelope Q (4 * (Q + 8)) := by
    unfold kernelOutputEnvelope kernelGeometryEnvelope kernelInverseEnvelope
    gcongr
  have hden : allocatedDensityEnvelope m D P ≤ allocatedDensityEnvelope m Q Q := by
    unfold allocatedDensityEnvelope
    gcongr
  have hsupp : allocatedSupportEnvelope m D P ≤ allocatedSupportEnvelope m Q Q := by
    unfold allocatedSupportEnvelope
    gcongr
  have hmono : allocatedAffineL1Log m D P Prho Pk ≤ allocatedAffineL1Log m Q Q Q Q := by
    unfold allocatedAffineL1Log allocatedIdealLipEnvelope scalarCubeRiemannLog
    gcongr
  apply hmono.trans
  simpa [poly, X, allocatedAffineL1Log, allocatedDensityEnvelope, allocatedSupportEnvelope,
    allocatedIdealLipEnvelope, scalarCubeRiemannLog, kernelOutputEnvelope,
    kernelGeometryEnvelope, kernelInverseEnvelope, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul]
    using hbound Q hQ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

 theorem exists_allocatedAffineScaleLog_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ D P Prho Pk target F T : ℝ,
      0 ≤ D → 0 ≤ P → 0 ≤ Prho → 0 ≤ Pk → 0 ≤ target → 0 ≤ F → 0 ≤ T →
      allocatedScaleLog (D + P + allocatedAffineLengthLog m D P Prho Pk target F T + 1) ≤
        (D + P + Prho + Pk + target + F + T + A) ^ A := by
  obtain ⟨b, hb, hLb⟩ := exists_allocatedAffineL1Log_bound m
  let X : Polynomial ℕ := Polynomial.X
  let poly := allocatedAffineScalePolynomial m X X ((X + Polynomial.C b) ^ b) X X X
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D P Prho Pk target F T hD hP hr hk ht hF hT
  let Q := D + P + Prho + Pk + target + F + T
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hDQ : D ≤ Q := by dsimp [Q]; linarith
  have hPQ : P ≤ Q := by dsimp [Q]; linarith
  have htQ : target ≤ Q := by dsimp [Q]; linarith
  have hFQ : F ≤ Q := by dsimp [Q]; linarith
  have hTQ : T ≤ Q := by dsimp [Q]; linarith
  have hl0 := allocatedAffineL1Log_nonneg m hD hP hr hk
  have hl : allocatedAffineL1Log m D P Prho Pk ≤ (Q + b) ^ b := by
    apply (hLb D P Prho Pk hD hP hr hk).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [Q]; linarith
  have he : allocatedAffineCoefficientAccuracyLog m D P Prho Pk target ≤
      Q + 1 + coefficientReplacementErrorLog Q ((Q + b) ^ b) := by
    dsimp only [allocatedAffineCoefficientAccuracyLog, coefficientReplacementErrorLog]
    gcongr
  have hE : allocatedAffineReferenceAccuracyLog m D P Prho Pk target ≤
      Q + 1 + affineReferenceCoefficientLog Q ((Q + b) ^ b) + 4 := by
    dsimp only [allocatedAffineReferenceAccuracyLog, affineReferenceCoefficientLog]
    gcongr
  have hi : kernelInverseEnvelope D P ≤ kernelInverseEnvelope Q Q := by
    unfold kernelInverseEnvelope
    gcongr
  have hfront : allocatedFrontEnvelope m D P (allocatedAffineCoefficientAccuracyLog m D P Prho Pk target) ≤
      allocatedFrontEnvelope m Q Q (Q + 1 + coefficientReplacementErrorLog Q ((Q + b) ^ b)) := by
    have hki := kernelInverseEnvelope_nonneg hD hP
    dsimp only [allocatedFrontEnvelope, allocatedKernelEnvelope]
    gcongr
  have hslice : progressionSliceLengthLog D (allocatedAffineReferenceAccuracyLog m D P Prho Pk target) F T ≤
      progressionSliceLengthLog Q (Q + 1 + affineReferenceCoefficientLog Q ((Q + b) ^ b) + 4) Q Q := by
    dsimp only [progressionSliceLengthLog, scalarCubeRiemannLog]
    gcongr
  have hL0 := (allocatedAffineLengthLog_bounds m hD hP hr hk ht hF hT).2.2.1
  have hL : allocatedAffineLengthLog m D P Prho Pk target F T ≤
      (m : ℝ) * allocatedFrontEnvelope m Q Q (Q + 1 + coefficientReplacementErrorLog Q ((Q + b) ^ b)) +
        progressionSliceLengthLog Q (Q + 1 + affineReferenceCoefficientLog Q ((Q + b) ^ b) + 4) Q Q := by
    exact add_le_add (mul_le_mul_of_nonneg_left hfront (Nat.cast_nonneg _)) hslice
  have hmono : allocatedScaleLog (D + P + allocatedAffineLengthLog m D P Prho Pk target F T + 1) ≤
      allocatedAffineScalePolynomial m Q Q ((Q + b) ^ b) Q Q Q := by
    dsimp only [allocatedScaleLog, allocatedAffineScalePolynomial]
    gcongr
  apply hmono.trans
  simpa [poly, X, allocatedAffineScalePolynomial, allocatedFrontEnvelope, allocatedKernelEnvelope,
    kernelInverseEnvelope, kernelGeometryEnvelope, coefficientReplacementErrorLog,
    affineReferenceCoefficientLog, progressionSliceLengthLog, scalarCubeRiemannLog,
    Polynomial.eval₂_pow] using hbound Q hQ

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCanonicalProjectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

noncomputable def allocatedCanonicalProjectionLog (m dim : ℕ) (P coverLog : ℝ) : ℝ :=
  allocatedFourierLogBudget m P + coverLog + canonicalProjectionRowCost m dim

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateStageScalarBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration

theorem allocatedCandidateStage_reset_bounds (s m : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    v ≤ allocatedCandidateStageResetInput s m v ∧
    0 ≤ allocatedCandidateStageResetInput s m v := by
  have h := allocatedCandidateStage_reset_lower s m hv
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hpow : 0 ≤ (v + 2) ^ 4 := by positivity
  exact ⟨by linarith only [h, hpow], by linarith only [h, hpow, hv0]⟩

theorem allocatedCandidateStage_common_bound (s m : ℕ) {v budget : ℝ}
    (hv : 2 ≤ v) (hbudget : budget ≤ v) :
    Real.exp budget * Real.exp ((v + 2) ^ 4) ≤
      Real.exp (allocatedCandidateStageResetInput s m v) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr
    ((add_le_add hbudget le_rfl).trans (allocatedCandidateStage_reset_lower s m hv))

theorem allocatedCandidateStage_mapSlow_bound (s m : ℕ) {v qNative : ℝ}
    (hv : 2 ≤ v) (hqNative : qNative ≤ v) :
    Real.exp ((v + 2) ^ 3 + qNative) ≤
      Real.exp (allocatedCandidateStageResetInput s m v + 2) := by
  have hpow : (v + 2) ^ 3 ≤ (v + 2) ^ 4 :=
    pow_le_pow_right₀ (by linarith only [hv]) (by norm_num)
  have h := allocatedCandidateStage_reset_lower s m hv
  exact Real.exp_le_exp.mpr (by linarith only [hpow, hqNative, h])

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
namespace OAI

section

namespace Erdos3

theorem isDenseCommonStrideBox_classical_iff {V : Type*} [Finite V]
    (t : Fintype V) (d : DecidableEq V) (N : V → ℕ) (cost : ℝ) (points : Finset (V → ℤ)) :
    @IsDenseCommonStrideBox V t d N cost points ↔
      @IsDenseCommonStrideBox V (Fintype.ofFinite V) (Classical.decEq V) N cost points := by
  cases Subsingleton.elim t (Fintype.ofFinite V)
  cases Subsingleton.elim d (Classical.decEq V)
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateGeneratedFastTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

noncomputable def allocatedCandidatePromotedMajorConstant (Csource : ℕ) : ℕ :=
  Classical.choose (exists_allocated_candidate_promoted_native_major_budget Csource)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidatePhysicalOrdinaryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

attribute [local irreducible] certifiedAffineCenterBudget

theorem allocatedCandidateTerminalFullInput_bounds
    (s m Cprimitive : ℕ) {x work cumulative : ℝ}
    (hx : 0 ≤ x) (hw : 0 ≤ work) (hc : 0 ≤ cumulative) :
    let p := allocatedCandidateTerminalFullInput s m Cprimitive x work cumulative
    0 ≤ p ∧ (x + Cprimitive) ^ Cprimitive ≤ p ∧ x ≤ p ∧ work ≤ p ∧
      (s : ℝ) ≤ p ∧ (m : ℝ) ≤ p ∧ certifiedAffineCenterBudget cumulative ≤ p ∧
      work + s * m * certifiedAffineCenterBudget cumulative ≤ p := by
  have hB := (terminal_affine_budget_bounds hc).1
  have hbase : 0 ≤ (x + Cprimitive) ^ Cprimitive := by positivity
  have hprod : 0 ≤ (s : ℝ) * m * certifiedAffineCenterBudget cumulative := by positivity
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  dsimp only [allocatedCandidateTerminalFullInput]
  exact ⟨by linarith only [hbase, hx, hw, hprod, hB, hs, hm],
    by linarith only [hx, hw, hprod, hB, hs, hm],
    by linarith only [hbase, hw, hprod, hB, hs, hm],
    by linarith only [hbase, hx, hprod, hB, hs, hm],
    by linarith only [hbase, hx, hw, hprod, hB, hm],
    by linarith only [hbase, hx, hw, hprod, hB, hs],
    by linarith only [hbase, hx, hw, hprod, hs, hm],
    by linarith only [hbase, hx, hB, hs, hm]⟩

theorem allocatedCandidateTerminalFullInput_denominator_bound
    (s m Cprimitive : ℕ) {x work cumulative : ℝ}
    (hx : 0 ≤ x) (hw : 0 ≤ work) (hc : 0 ≤ cumulative) :
    Real.exp work * (Real.exp ((m : ℝ) * certifiedAffineCenterBudget cumulative)) ^ s ≤
      Real.exp (allocatedCandidateTerminalFullInput s m Cprimitive x work cumulative) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [mul_assoc] using
    (allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hw hc).2.2.2.2.2.2.2

theorem allocatedCandidateTerminalFullInput_mass_bound
    (s m Cprimitive nTags nVars : ℕ) {x work cumulative : ℝ}
    (hx : 0 ≤ x) (hw : 0 ≤ work) (hc : 0 ≤ cumulative)
    (htags : (nTags : ℝ) ≤ x) (hvars : (nVars : ℝ) ≤ x) :
    let p := allocatedCandidateTerminalFullInput s m Cprimitive x work cumulative
    ((nTags : ℝ) + 1) ^ s * Real.exp work *
      (actualCandidateSlowProjectionMassBudget m nVars p
        (((cumulative + ((cumulative + 2) ^ 2 + 2) ^ 63) + 2) ^ 8)) ^ s ≤
          Real.exp ((p + 2) ^ 4) := by
  obtain ⟨hp, _, hxp, hwp, hsp, hmp, hBp, _⟩ :=
    allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hw hc
  exact actualCandidateSlowProjectionMassBudget_terminal_bound s m nTags nVars hp hsp hmp
    (htags.trans hxp) (hvars.trans hxp) hwp ((terminal_affine_budget_bounds hc).2.trans hBp)

end Erdos3.VectorPolynomial

end

end OAI
end


