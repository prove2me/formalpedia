-- Prove2me | Definitions.Def_OAIE3v2B028
-- name    : OAIE3v2B028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:08.105454+00:00
-- url     : https://prove2.me/theorems/3526cd22-d682-4f8b-b120-40d427c758dd
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 29 of 311
-- statement:
--   Definitions bundle 29 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CandidateCommonFastBudgetMonotonicity.lean`, `Dynamics/CandidateFrontSourceLossBudget.lean`, `Dynamics/PointwiseSymbolBudget.lean`, `Dynamics/ScheduledPhysicalEpochStack.lean`, `Estimates/AllocatedCandidateCommonFastGeometry.lean`, `Estimates/AllocatedExternalCandidateGeneratedFreezingSuccessor.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/ConstantObservableMemberNets.lean`, `Estimates/ControlledFixedMarkedNativeFactorization.lean`, `Estimates/ControlledLinearSubspaceLift.lean`, `Estimates/ControlledPrescribedMarkedNativeFactorization.lean`, `Estimates/HomogeneousQuotientSymbolLiftBounds.lean`, `Estimates/PeelingCellCaps.lean`, `Estimates/PeelingCost.lean`, `Estimates/PeelingDecomposition.lean`, `Estimates/PivotStageBoundary.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/ScalarCubeDomain.lean`, `Estimates/Separation.lean`, `Estimates/UnitRangeLocalLipschitz.lean`, `Geometry/CoordinateFiberPatch.lean`, `Geometry/GeometricLocalizationThreshold.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Lattices/UniformExternalMarkedAffineSliceFreezingDictionary.lean`, `Linear/ActualOrdinaryPointwiseSpanning.lean`, `Linear/ControlledMarkedKernelNormalization.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Linear/OrdinarySymbolBasisDimension.lean`, `Linear/RationalTaggedSpanProjection.lean`, `Linear/RealRationalMatrixPiNaturality.lean`, `Polynomial/FrozenPolynomialAffineRange.lean`, `Polynomial/LocalizationPolynomialScales.lean`, `Polynomial/LowestPolynomialLayer.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/PolynomialCoefficientNormalization.lean`, `Polynomial/PolynomialDensityBudget.lean`, `Polynomial/PolynomialPatchProductBudget.lean`, `Polynomial/PolynomialPatchShearOrbit.lean`, `Polynomial/PolynomialShearObservableNet.lean`, `Polynomial/PolynomialValueCoefficient.lean`, `Polynomial/SlowPolynomialSliceLogCost.lean`, `Sampling/PatchKernelGridBudget.lean`, `Sampling/PositiveGridFamily.lean`, `Sampling/RationalPowerGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
namespace OAI

section

namespace Erdos3

def budgetDepthExponent (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => (budgetDepthExponent a d + 2) * a

end Erdos3

end

section

namespace Erdos3

noncomputable def iteratedPowerBudget (a : ℕ) (p : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => (iteratedPowerBudget a p n + 2) ^ a

@[simp] theorem iteratedPowerBudget_zero (a : ℕ) (p : ℝ) : iteratedPowerBudget a p 0 = p := rfl

@[simp] theorem iteratedPowerBudget_succ (a : ℕ) (p : ℝ) (n : ℕ) :
    iteratedPowerBudget a p (n + 1) = (iteratedPowerBudget a p n + 2) ^ a := rfl

theorem iteratedPowerBudget_nonneg (a : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    0 ≤ iteratedPowerBudget a p n := by
  induction n with
  | zero => exact hp
  | succ n ih => exact pow_nonneg (by linarith) _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

def lowestSlotWeight (h : ℕ) : σ ⊕ τ → ℕ := Sum.elim (fun _ => 1) (fun _ => h)

theorem exponent_eq_single_of_lowest_slot {h : ℕ} (hh : 0 < h)
    {α : (σ ⊕ τ) →₀ ℕ}
    (hα : Finsupp.weight (lowestSlotWeight h) α ≤ h)
    {j : τ} (hj : α (Sum.inr j) ≠ 0) : α = Finsupp.single (Sum.inr j) 1 := by
  classical
  have hw := Finsupp.weight_sub_single_add (w := lowestSlotWeight (σ := σ) (τ := τ) h) hj
  have hz : Finsupp.weight (lowestSlotWeight h) (α - Finsupp.single (Sum.inr j) 1) = 0 := by
    change _ + h = _ at hw
    omega
  have hzero : α - Finsupp.single (Sum.inr j) 1 = 0 := by
    ext v
    have hv : lowestSlotWeight (σ := σ) (τ := τ) h v ≠ 0 := by
      cases v <;> simp [lowestSlotWeight, hh.ne']
    have hle := Finsupp.le_weight (lowestSlotWeight h) hv (α - Finsupp.single (Sum.inr j) 1)
    rw [hz] at hle
    exact Nat.eq_zero_of_le_zero hle
  have heq := Finsupp.sub_add_single_one_cancel hj
  rw [hzero, zero_add] at heq
  exact heq.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

noncomputable def prefixSubstitution (I : Fin D → MvPolynomial σ ℝ) (i : Fin E) :
    σ ⊕ Fin (D + i.val) → MvPolynomial (σ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a))
    (Fin.addCases (fun j => aeval (fun a => X (Sum.inl a)) (I j))
      (fun j => X (Sum.inr j)))

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

noncomputable def affineLineParameters (a q : σ → ℝ) : σ → MvPolynomial Unit ℝ :=
  fun i => C (a i) + q i • X ()

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget
namespace OAI

section

namespace Erdos3

theorem pow_mul_exp_le_exp_of_le_budget {q p D B : ℝ} {h m : ℕ}
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp p) (hp : 0 ≤ p)
    (hh : h ≤ m) (hbudget : (m : ℝ) * p + D ≤ B) :
    q ^ h * Real.exp D ≤ Real.exp B := by
  calc
    q ^ h * Real.exp D ≤ (Real.exp p) ^ h * Real.exp D :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq h) (Real.exp_nonneg D)
    _ = Real.exp ((h : ℝ) * p + D) := by rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp B := by
      apply Real.exp_le_exp.mpr
      have hmul : (h : ℝ) * p ≤ (m : ℝ) * p :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hh) hp
      linarith

theorem nat_pow_mul_le_exp_of_le_budget {q l d : ℕ} {p D B : ℝ}
    (hq : (q : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp D)
    (hbudget : (d : ℝ) * p + D ≤ B) :
    ((q ^ d * l : ℕ) : ℝ) ≤ Real.exp B := by
  calc
    ((q ^ d * l : ℕ) : ℝ) = (q : ℝ) ^ d * (l : ℝ) := by norm_cast
    _ ≤ (Real.exp p) ^ d * Real.exp D :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg q) hq d) hl
        (Nat.cast_nonneg l) (pow_nonneg (Real.exp_nonneg p) d)
    _ = Real.exp ((d : ℝ) * p + D) := by rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp B := Real.exp_le_exp.mpr hbudget

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialValueCoefficient
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_eval_abs_le_sum_coeff {ι : Type*}
    (p : MvPolynomial ι ℝ) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |MvPolynomial.eval x p| ≤ ∑ m ∈ p.support, |p.coeff m| := by
  classical
  rw [MvPolynomial.eval_eq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m _
  rw [abs_mul, Finset.abs_prod]
  have hprod : (∏ i ∈ m.support, |x i ^ m i|) ≤ 1 := by
    apply Finset.prod_le_one
    · exact fun _ _ => abs_nonneg _
    · intro i _
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hx i)
  exact mul_le_of_le_one_right (abs_nonneg _) hprod

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeDomain
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

def positiveInequalityDomain {I E : Type*} (d : I → E → ℝ) : Set E :=
  {x | ∀ i, 0 < d i x}

theorem positiveInequalityDomain_isOpen {I E : Type*} [Fintype I] [TopologicalSpace E]
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) : IsOpen (positiveInequalityDomain d) := by
  have heq : positiveInequalityDomain d = ⋂ i, {x | 0 < d i x} := by
    ext x
    simp [positiveInequalityDomain]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hd i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators ContDiff

noncomputable def scalarCubeCenter (α : Type*) : Option α → ℝ
  | none => 1 / 2
  | some _ => 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingDecomposition
namespace OAI


namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

noncomputable def positiveSupport (f : G → ℝ) : Finset G := Finset.univ.filter (fun x => 0 < f x)

end Erdos3.Peeling


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} {d : ℕ}

noncomputable def slotAddShearEquiv [AddCommGroup R] (i : Fin d)
    (f : (Fin d → R) → R) (hf : ∀ b c, f (Function.update b i c) = f b) :
    (Fin d → R) ≃ (Fin d → R) where
  toFun b := Function.update b i (b i + f b)
  invFun b := Function.update b i (b i - f b)
  left_inv b := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self, hf, add_sub_cancel_right]
    · simp only [Function.update_of_ne h]
  right_inv b := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self, hf, sub_add_cancel]
    · simp only [Function.update_of_ne h]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealRationalMatrixPiNaturality
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem rationalMatrix_piScalarRight_baseChange
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℚ) (x : ℝ ⊗[ℚ] (J → ℚ)) :
    TensorProduct.piScalarRight ℚ ℝ ℝ I (A.mulVecLin.baseChange ℝ x) =
      (Matrix.mulVecLin (fun i j => (A i j : ℝ)))
        (TensorProduct.piScalarRight ℚ ℝ ℝ J x) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Rat.smul_def]
    funext i
    change ((∑ j, A i j * v j : ℚ) : ℝ) * a =
      ∑ j, (A i j : ℝ) * ((v j : ℝ) * a)
    simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

theorem rationalMatrix_real_ker_eq_range
    (A : Matrix I K ℚ) (D : Matrix J I ℚ)
    (h : LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin) :
    LinearMap.ker (Matrix.mulVecLin (fun j i => (D j i : ℝ))) =
      LinearMap.range (Matrix.mulVecLin (fun i k => (A i k : ℝ))) := by
  classical
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  have hex : Function.Exact (A.mulVecLin.baseChange ℝ) (D.mulVecLin.baseChange ℝ) :=
    Module.Flat.lTensor_exact ℝ (LinearMap.exact_iff.mpr h)
  ext x
  change Matrix.mulVecLin (fun j i => (D j i : ℝ)) x = 0 ↔
    ∃ y, Matrix.mulVecLin (fun i k => (A i k : ℝ)) y = x
  constructor
  · intro hx
    have hx' : D.mulVecLin.baseChange ℝ
        ((TensorProduct.piScalarRight ℚ ℝ ℝ I).symm x) = 0 := by
      apply (TensorProduct.piScalarRight ℚ ℝ ℝ J).injective
      rw [rationalMatrix_piScalarRight_baseChange, map_zero,
        LinearEquiv.apply_symm_apply]
      exact hx
    obtain ⟨z, hz⟩ := (hex _).mp hx'
    refine ⟨TensorProduct.piScalarRight ℚ ℝ ℝ K z, ?_⟩
    rw [← rationalMatrix_piScalarRight_baseChange, hz,
      LinearEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    have hz := hex.apply_apply_eq_zero
      ((TensorProduct.piScalarRight ℚ ℝ ℝ K).symm y)
    have he := congrArg (TensorProduct.piScalarRight ℚ ℝ ℝ J) hz
    simpa only [rationalMatrix_piScalarRight_baseChange,
      LinearEquiv.apply_symm_apply, map_zero] using he

theorem rationalMatrix_real_ker_eq_span
    (A : Matrix I K ℚ) (D : Matrix J I ℚ)
    (h : LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin) :
    LinearMap.ker (Matrix.mulVecLin (fun j i => (D j i : ℝ))) =
      Submodule.span ℝ (Set.range (fun k i => (A i k : ℝ))) := by
  rw [rationalMatrix_real_ker_eq_range A D h]
  exact Matrix.range_mulVecLin (fun i k => (A i k : ℝ) : Matrix I K ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitRangeLocalLipschitz
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitzWith_of_unit_range_near_nonzero {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (C L : ℝ≥0) (hzero : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1)
    (hnear : ∀ x y, f x ≠ 0 → (C : ℝ) * dist x y < 1 →
      |f x - f y| ≤ (L : ℝ) * dist x y) :
    LipschitzWith (max C L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  by_cases hclose : (C : ℝ) * dist x y < 1
  · have hxy : |f x - f y| ≤ (L : ℝ) * dist x y := by
      by_cases hx : f x = 0
      · by_cases hy : f y = 0
        · rw [hx, hy, sub_self, abs_zero]
          positivity
        · have h := hnear y x hy (by simpa only [dist_comm] using hclose)
          simpa only [abs_sub_comm, dist_comm] using h
      · exact hnear x y hx hclose
    exact hxy.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right C L) dist_nonneg)
  · have hxy : |f x - f y| ≤ 1 := abs_le.mpr ⟨by linarith [hzero x, hone y], by linarith [hone x, hzero y]⟩
    exact hxy.trans ((le_of_not_gt hclose).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left C L) dist_nonneg))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialSubstitutionPoint
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (x : σ → R) : σ → R :=
  fun i => aeval x (F (X i))

theorem polynomialSubstitutionPoint_aeval
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (x : σ → R) (P : MvPolynomial σ R) :
    aeval (polynomialSubstitutionPoint F x) P = aeval x (F P) := by
  conv_rhs => rw [MvPolynomial.aeval_unique F, MvPolynomial.comp_aeval_apply]
  rfl

theorem polynomial_map_aeval {S : Type*} [CommRing S] (f : R →+* S)
    (x : σ → R) (P : MvPolynomial σ R) :
    aeval (fun i => f (x i)) (MvPolynomial.map f P) = f (aeval x P) := by
  simpa only [MvPolynomial.aeval_eq_eval, Function.comp_def] using
    (MvPolynomial.map_eval f x P).symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem integerTupleRatCast_injective :
    Function.Injective (fun b : σ → ℤ => fun i => (b i : ℚ)) := by
  intro b c h
  funext i
  have hi : (b i : ℚ) = (c i : ℚ) := congrFun h i
  exact_mod_cast hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalizationPolynomialScales
namespace OAI

section

namespace Erdos3

noncomputable def localizationRadius (U ε : ℝ) : ℝ := ε / (8 * U ^ 2)
noncomputable def localizationMesh (U ε : ℝ) : ℝ := ε ^ 2 / (128 * U ^ 5)
noncomputable def localizationLengthBudget (U ε W : ℝ) : ℝ := 256 * U ^ 6 * W / ε ^ 2

theorem localizationRadius_pos {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    0 < localizationRadius U ε := by unfold localizationRadius; positivity

theorem localizationMesh_pos {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    0 < localizationMesh U ε := by unfold localizationMesh; positivity

theorem localizationMesh_le_one {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    localizationMesh U ε ≤ 1 := by
  have hp : 1 ≤ U ^ 5 := one_le_pow₀ hU
  unfold localizationMesh
  apply (div_le_one (by positivity)).mpr
  nlinarith

theorem localizationMesh_length {U ε W : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    localizationMesh U ε * localizationLengthBudget U ε W = 2 * U * W := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationMesh localizationLengthBudget
  field_simp
  ring

theorem localizationMesh_margin {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    U * localizationMesh U ε < localizationRadius U ε := by
  have hU0 : 0 < U := by linarith
  have hp : 1 ≤ U ^ 2 := one_le_pow₀ hU
  have he : U * localizationMesh U ε = localizationRadius U ε * (ε / (16 * U ^ 2)) := by
    unfold localizationRadius localizationMesh
    field_simp
    ring
  rw [he]
  apply mul_lt_of_lt_one_right (localizationRadius_pos hU hε)
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem localizationLengthBudget_ge_square {U ε W : ℝ}
    (hU : 1 ≤ U) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W) :
    U ^ 2 ≤ localizationLengthBudget U ε W := by
  have hp : U ^ 2 ≤ U ^ 6 := pow_le_pow_right₀ hU (by decide : 2 ≤ 6)
  have he : ε ^ 2 ≤ 1 := by nlinarith
  have hU6 : 0 ≤ U ^ 6 := by positivity
  have hprod : U ^ 6 ≤ U ^ 6 * W := le_mul_of_one_le_right hU6 hW
  unfold localizationLengthBudget
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  have hsmall := mul_le_of_le_one_right (sq_nonneg U) he
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricLocalizationThreshold
namespace OAI

section

namespace Erdos3

noncomputable def localizationThreshold (U ζ : ℝ) (i : ℕ) : ℝ := ζ / (2 * U ^ 2) ^ i

theorem localizationThreshold_pos {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ) (i : ℕ) :
    0 < localizationThreshold U ζ i := by unfold localizationThreshold; positivity

theorem localizationThreshold_zero (U ζ : ℝ) : localizationThreshold U ζ 0 = ζ := by
  simp only [localizationThreshold, pow_zero, div_one]

theorem localizationThreshold_antitone {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 ≤ ζ)
    {i j : ℕ} (hij : i ≤ j) : localizationThreshold U ζ j ≤ localizationThreshold U ζ i := by
  have hC : 1 ≤ 2 * U ^ 2 := by nlinarith [one_le_pow₀ hU (n := 2)]
  apply div_le_div_of_nonneg_left hζ (by positivity)
  exact pow_le_pow_right₀ hC hij

theorem localizationThreshold_le_one {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (i : ℕ) :
    localizationThreshold U ζ i ≤ 1 := by
  have h := localizationThreshold_antitone hU hζ.le (Nat.zero_le i)
  rw [localizationThreshold_zero] at h
  exact h.trans hζ1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalPowerGrid
namespace OAI

section

namespace Erdos3

theorem rational_power_clear_denominator (a : ℤ) (d s k : ℕ) (hd : 0 < d) (hk : k ≤ s) :
    (d : ℝ) ^ s * ((a : ℝ) / d) ^ k = (a : ℝ) ^ k * (d : ℝ) ^ (s - k) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpow : (d : ℝ) ^ s = (d : ℝ) ^ (s - k) * (d : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hpow, div_pow]
  field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PointwiseSymbolBudget
namespace OAI

section

namespace Erdos3

theorem shift_le_power_succ {p : ℝ} (hp : 0 ≤ p) (C : ℕ) :
    p + C ≤ (p + 2) ^ (C + 1) := by
  induction C with
  | zero => simp only [Nat.cast_zero, add_zero, zero_add, pow_one]; linarith
  | succ C ih =>
    have hpow : 1 ≤ (p + 2) ^ (C + 1) := one_le_pow₀ (by linarith)
    calc
      p + (C + 1 : ℕ) ≤ (p + 2) ^ (C + 1) + 1 := by push_cast; linarith
      _ ≤ (p + 2) ^ (C + 1) * (p + 2) := by nlinarith
      _ = (p + 2) ^ (C + 1 + 1) := (pow_succ _ _).symm

theorem shifted_self_power_le_base_power {p : ℝ} (hp : 0 ≤ p) (C : ℕ) :
    (p + C) ^ C ≤ (p + 2) ^ ((C + 1) * C) := by
  calc
    _ ≤ ((p + 2) ^ (C + 1)) ^ C := pow_le_pow_left₀ (by positivity) (shift_le_power_succ hp C) C
    _ = _ := (pow_mul _ _ _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrdinarySymbolBasisDimension
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

def pointwiseFastSectionInput (s : ℕ) (p : ℝ) : ℝ :=
  2 * (p + (s + 3)) ^ (s + 3) + ((p + (s + 3)) ^ (s + 3)) ^ 2 + p

theorem pointwiseFastSectionInput_ge (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ pointwiseFastSectionInput s p := by
  unfold pointwiseFastSectionInput
  exact le_add_of_nonneg_left (by positivity)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledLinearSubspaceLift
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

variable {η ι δ : Type*} [Fintype ι]

noncomputable def jointMatrixImages (Q : η → Matrix ι ι ℚ) (x : η → ι → ℝ) : (Σ _ : η, ι) → ℝ :=
  fun bi => ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ x bi.1) bi.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateFiberPatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteBoxPointsEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (S : I → Finset ℤ) : (∀ i, S i) ≃ Fintype.piFinset S where
  toFun x := ⟨fun i => (x i).val, Fintype.mem_piFinset.mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, Fintype.mem_piFinset.mp x.property i⟩
  left_inv x := by funext i; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem finiteBoxPoints_expect {I : Type*} [Fintype I] [DecidableEq I]
    (S : I → Finset ℤ) (f : (I → ℤ) → ℝ) :
    (𝔼 x : Fintype.piFinset S, f x.val) = 𝔼 x : (∀ i, S i), f (fun i => (x i).val) :=
  (Fintype.expect_equiv (finiteBoxPointsEquiv S)
    (fun x => f (fun i => (x i).val)) (fun x => f x.val) (fun _ => rfl)).symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def coordinateFiberParameters (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ)
    (i : I) : MvPolynomial {i // keep i} ℝ :=
  if hi : keep i then X ⟨i, hi⟩ else C (fixed ⟨i, hi⟩ : ℝ)

theorem finiteBoxPoints_expect_finset (S : I → Finset ℤ) (f : (I → ℤ) → ℝ) :
    (𝔼 x ∈ Fintype.piFinset S, f x) = 𝔼 x : (∀ i, S i), f (fun i => (x i).val) := by
  simpa only [Finset.expect_eq_sum_div_card, Finset.card_univ, Finset.sum_coe_sort,
    Fintype.card_coe] using finiteBoxPoints_expect S f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coefficientResidueSet (L m : ℕ) (r : ZMod m) : Finset ℤ :=
  (Finset.Ico 0 (L : ℤ)).filter (fun z => (z : ZMod m) = r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {K : Type*} (oldKeep keep : K → Prop)

def axisInclusion (hsub : ∀ i, keep i → oldKeep i) (i : {i // keep i}) :
    {i // oldKeep i} :=
  ⟨i.val, hsub i.val i.property⟩

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlowPolynomialSliceLogCost
namespace OAI

section

namespace Erdos3

def slowPolynomialSliceSlope (d n : ℕ) (M : ℝ) : ℝ :=
  (d + 1 : ℝ) * (n + 1 : ℝ) ^ d * M * n * d

theorem slowPolynomialSliceSlope_nonneg (d n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ slowPolynomialSliceSlope d n M := by
  unfold slowPolynomialSliceSlope
  positivity

theorem slowPolynomialSliceSlope_le_exp (d n : ℕ) {M p : ℝ}
    (_hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hM : 0 ≤ M)
    (hMexp : M ≤ Real.exp p) :
    slowPolynomialSliceSlope d n M ≤
      Real.exp (((d : ℝ) + 2) * p + 3 * d + 1) := by
  have hd1 : (d : ℝ) + 1 ≤ Real.exp ((d : ℝ) + 1) := by
    linarith [Real.add_one_le_exp ((d : ℝ) + 1)]
  have hn1 : (n : ℝ) + 1 ≤ Real.exp (p + 1) := by
    linarith [Real.add_one_le_exp (p + 1)]
  have hnp : (n : ℝ) ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  have hd : (d : ℝ) ≤ Real.exp (d : ℝ) := by
    linarith [Real.add_one_le_exp (d : ℝ)]
  unfold slowPolynomialSliceSlope
  calc
    _ ≤ Real.exp ((d : ℝ) + 1) * (Real.exp (p + 1)) ^ d *
        Real.exp p * Real.exp p * Real.exp (d : ℝ) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualOrdinaryPointwiseSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

noncomputable def ordinaryImagePointwiseBudget (s t : ℕ) (p : ℝ) : ℝ :=
  pointwiseFastSectionInput s p + pointwiseFastSectionInput t p + (p + 2) ^ 5

theorem sectionInput_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ pointwiseFastSectionInput s p := by
  unfold pointwiseFastSectionInput
  positivity

theorem ordinaryImagePointwiseBudget_source (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    pointwiseFastSectionInput s p ≤ ordinaryImagePointwiseBudget s t p := by
  have ht := sectionInput_nonneg t hp
  have hh : 0 ≤ (p + 2) ^ 5 := by positivity
  unfold ordinaryImagePointwiseBudget
  linarith

theorem ordinaryImagePointwiseBudget_target (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    pointwiseFastSectionInput t p ≤ ordinaryImagePointwiseBudget s t p := by
  have hs := sectionInput_nonneg s hp
  have hh : 0 ≤ (p + 2) ^ 5 := by positivity
  unfold ordinaryImagePointwiseBudget
  linarith

theorem ordinaryImagePointwiseBudget_height (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + 2) ^ 5 ≤ ordinaryImagePointwiseBudget s t p := by
  have hs := sectionInput_nonneg s hp
  have ht := sectionInput_nonneg t hp
  unfold ordinaryImagePointwiseBudget
  linarith

theorem ordinaryImagePointwiseBudget_ge (s t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ ordinaryImagePointwiseBudget s t p :=
  (pointwiseFastSectionInput_ge s hp).trans (ordinaryImagePointwiseBudget_source s t hp)

theorem symbolCount_le_sectionInput (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + (s + 3)) ^ (s + 3) ≤ pointwiseFastSectionInput s p := by
  have h : 0 ≤ (p + (s + 3)) ^ (s + 3) := by positivity
  unfold pointwiseFastSectionInput
  nlinarith [sq_nonneg ((p + (s + 3)) ^ (s + 3))]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix

variable {ι η V : Type*} [Fintype ι] [Fintype η]
  [AddCommGroup V] [Module ℚ V]

theorem basis_generator_matrix_range (b : Basis ι ℚ V) (v : η → V)
    (U : Submodule ℚ V) (hspan : Submodule.span ℚ (Set.range v) = U) :
    LinearMap.range (Matrix.mulVecLin (show Matrix ι η ℚ from fun i j => b.repr (v j) i)) =
      U.map b.equivFun.toLinearMap := by
  rw [Matrix.range_mulVecLin, ← hspan, Submodule.map_span, ← Set.range_comp]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateCommonFastBudgetMonotonicity
namespace OAI

section

namespace Erdos3

theorem NilpotentLieFiltration.pointwiseFastSectionInput_mono (s : ℕ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    NilpotentLieFiltration.pointwiseFastSectionInput s p ≤
      NilpotentLieFiltration.pointwiseFastSectionInput s q := by
  have hbase : p + ((s : ℝ) + 3) ≤ q + ((s : ℝ) + 3) := add_le_add hpq le_rfl
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ p + ((s : ℝ) + 3)) hbase (s + 3)
  have hsquare := pow_le_pow_left₀
    (by positivity : 0 ≤ (p + ((s : ℝ) + 3)) ^ (s + 3)) hpow 2
  exact add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hpow (by norm_num)) hsquare) hpq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScheduledPhysicalEpochStack
namespace OAI

section

namespace Erdos3

def physicalEpochBudget (A C : ℕ) (b : ℝ) : ℕ → ℝ
  | 0 => b
  | k + 1 => ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ A

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousQuotientSymbolLiftBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators TensorProduct

theorem linearMap_abs_repr_le {V W ι κ : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [Fintype ι]
    (b : Basis ι ℝ V) (c : Basis κ ℝ W) (S : V →ₗ[ℝ] W)
    {A B : ℝ} (hA : 0 ≤ A)
    (hS : ∀ i j, |c.repr (S (b j)) i| ≤ B)
    (x : V) (hx : ∀ j, |b.repr x j| ≤ A) (i : κ) :
    |c.repr (S x) i| ≤ (Fintype.card ι : ℝ) * B * A := by
  classical
  have he : c.repr (S x) i = ∑ j, b.repr x j * c.repr (S (b j)) i := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  calc
    |∑ j, b.repr x j * c.repr (S (b j)) i| ≤
        ∑ j, |b.repr x j * c.repr (S (b j)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, A * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hx j) (hS i j) (abs_nonneg _) hA
    _ = _ := by simp; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearObservableNet
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

noncomputable def patchTopNetError (d s N : ℕ) (M : ℝ) : ℝ :=
  ((s + 1) * (d + 1) ^ s : ℕ) * (4 * (1 + M) / N) * ((1 + M) ^ (s * d)) ^ s

theorem patchTopNetError_nonneg (d s N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ patchTopNetError d s N M := by unfold patchTopNetError; positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PatchKernelGridBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def patchKernelGridRadius (N : ℕ) : ℝ≥0 := 1 / (2 * N)

theorem patchKernelGridRadius_pos {N : ℕ} (hN : 0 < N) : 0 < patchKernelGridRadius N := by
  have : (0 : ℝ≥0) < N := by exact_mod_cast hN
  unfold patchKernelGridRadius
  positivity

theorem patchKernelGridRadius_small {N : ℕ} (hN : 8 ≤ N) :
    2 * (patchKernelGridRadius N : ℝ) ≤ 1 / 8 := by
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  simp only [patchKernelGridRadius, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  field_simp
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_combination_term {I : Type*} [Fintype I] [Nonempty I]
    (c a : I → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hsum : δ ≤ ∑ i, c i * a i) :
    ∃ i, δ / Fintype.card I ≤ a i := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hmean : δ / Fintype.card I ≤ 𝔼 i, c i * a i := by
    rw [Fintype.expect_eq_sum_div_card]
    exact div_le_div_of_nonneg_right hsum hn.le
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have ha : 0 ≤ a i := by
    by_contra! hneg
    have hmul := mul_nonpos_of_nonneg_of_nonpos (hc i).1 hneg.le
    linarith [div_pos hδ hn]
  exact ⟨i, hi.trans (mul_le_of_le_one_left ha (hc i).2)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledMarkedKernelNormalization
namespace OAI

section

namespace Erdos3

theorem kernel_coordinate_factor_le_exp (k H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hk : (k : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (k : ℝ) * H ≤ Real.exp ((p + 2) ^ 2) := by
  have hkexp : (k : ℝ) ≤ Real.exp p :=
    hk.trans (by linarith [Real.add_one_le_exp p])
  calc
    _ ≤ Real.exp p * Real.exp p :=
      mul_le_mul hkexp hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (p + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingCost
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

noncomputable def coefficientCost (B : Finset G) (cs : List (Finset G)) : ℝ :=
  (cs.map (fun C => (C.card : ℝ) / B.card)).sum

end Erdos3.Peeling

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingCellCaps
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def translatedCellFamily (Shape : Finset G → Prop) (A : Finset G) : Prop :=
  ∃ C, Shape C ∧ ∃ z : G, A = C.image (fun t => z + t)

end Erdos3.Peeling

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositiveGridFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev PositiveGridVertex {j : ℕ} (a : Fin j → ℕ) := ∀ i, Fin (a i)

abbrev PositiveGridShifts {j : ℕ} (a : Fin j → ℕ) (G : Type*) := ∀ i, Fin (a i) → G

def positiveGridVolume {j : ℕ} (a : Fin j → ℕ) : ℕ := ∏ i, a i

noncomputable def positiveGridProduct {j : ℕ} (a : Fin j → ℕ) {G : Type*} [AddCommMonoid G]
    (f : PositiveGridVertex a → G → ℝ) (t : PositiveGridShifts a G) : ℝ :=
  ∏ b, f b (∑ i, t i (b i))

noncomputable def positiveGridMean {j : ℕ} (a : Fin j → ℕ) {G : Type*}
    [AddCommMonoid G] [Fintype G] (f : PositiveGridVertex a → G → ℝ) : ℝ :=
  𝔼 t, positiveGridProduct a f t

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotStageBoundary
namespace OAI

section

namespace Erdos3

def PivotCompatible {I R : Type*} [CommRing R] {l : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (a b : R) : Prop :=
  IsUnit (b - a) ∧
    (∀ i ∈ S, IsUnit (a - slopes i) ∧ IsUnit (b - slopes i)) ∧
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsUnit (slopes i - slopes j)) ∧
    (∀ j, IsUnit (a - v j) ∧ IsUnit (b - v j) ∧
      ∀ i ∈ S, IsUnit (slopes i - v j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowestPolynomialLayer
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {D : ℕ} {R : Type*} [CommRing R]

theorem det_one_sub_strictLower (M : Matrix (Fin D) (Fin D) R)
    (hM : ∀ i j, i ≤ j → M i j = 0) : (1 - M).det = 1 := by
  have htri : (1 - M).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    simp [Matrix.sub_apply, hM i j hij.le, Matrix.one_apply_ne hij.ne]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  apply Finset.prod_eq_one
  intro i _
  simp [Matrix.sub_apply, hM i i le_rfl]

variable {σ : Type*}

noncomputable def polynomialMatrixAction (M : Matrix (Fin D) (Fin D) R)
    (C₀ : Fin D → MvPolynomial σ R) : Fin D → MvPolynomial σ R :=
  fun i => ∑ j, M i j • C₀ j

theorem polynomialMatrixAction_eval (M : Matrix (Fin D) (Fin D) R)
    (C₀ : Fin D → MvPolynomial σ R) (t : σ → R) :
    (fun i => aeval t (polynomialMatrixAction M C₀ i)) =
      M.mulVec (fun i => aeval t (C₀ i)) := by
  ext i
  simp [polynomialMatrixAction, Matrix.mulVec, dotProduct]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary
namespace OAI

section

namespace Erdos3
open scoped BigOperators

def affineParentIntegerPoint {ι : Type*} (N : ι → ℕ)
    (origin : ι → ℤ) (step : ℕ) (x : ∀ i, Fin (N i)) : ι → ℤ :=
  fun i => origin i + step * (x i).val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration

open Module

def controlledProjectionDimensionInput (s : ℕ) (p : ℝ) : ℝ :=
  2 * ((p + (s + 2)) ^ (s + 2)) ^ 2 + p + 1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

theorem le_controlledProjectionDimensionInput (s : ℕ) (p : ℝ) :
    p ≤ controlledProjectionDimensionInput s p := by
  unfold controlledProjectionDimensionInput
  nlinarith [sq_nonneg ((p + (s + 2)) ^ (s + 2))]

theorem controlledProjectionDimensionInput_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ controlledProjectionDimensionInput s p :=
  hp.trans (le_controlledProjectionDimensionInput s p)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3
open scoped BigOperators TensorProduct Classical

variable {I : Type*} (keep : I → Prop)

noncomputable def frozenShortStarts (fixed : {i // ¬keep i} → ℤ) : I → ℕ :=
  fun i => if hi : keep i then 0 else (fixed ⟨i, hi⟩).toNat

theorem frozenShortStarts_inside {N : I → ℕ} (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < N i.val) :
    ∀ i, ¬keep i → frozenShortStarts keep fixed i < N i := by
  intro i hi
  simp only [frozenShortStarts, dif_neg hi]
  have h := hfixed ⟨i, hi⟩
  apply Int.ofNat_lt.mp
  simpa only [Int.toNat_of_nonneg h.1] using h.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConstantObservableMemberNets
namespace OAI

section

namespace Erdos3
open scoped Classical

theorem constantObservable_memberNets
    {Z Y : Type*} (box : Finset Z) (hbox : box.Nonempty)
    (F : Y → ℂ) {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : Z // x ∈ box},
        ∀ x ∈ box, ∃ i, ∀ y,
          ‖(fun (_ : Z) => F) x y - (fun (_ : Z) => F) (oc i).val y‖ ≤ η := by
  intro η hη hηone
  have hlog : 0 ≤ Real.log (1 / η) :=
    Real.log_nonneg ((le_div_iff₀ hη).mpr (by simpa using hηone))
  have hpower : 0 ≤ (p + Real.log (1 / η) + (e : ℝ)) ^ e :=
    pow_nonneg (add_nonneg (add_nonneg hp hlog) (Nat.cast_nonneg e)) e
  obtain ⟨z, hz⟩ := hbox
  refine ⟨1, (by simpa using Real.one_le_exp_iff.mpr hpower), (fun _ => ⟨z, hz⟩), ?_⟩
  intro x hx
  exact ⟨0, fun y => by simpa using hη.le⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateGeneratedFreezingSuccessor
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem frozenMarkedPhysical_exp_mono {p : ℝ} (hp : 0 ≤ p)
    {a C : ℕ} (ha : 2 ≤ a) (haC : a ≤ C) :
    Real.exp ((p + a) ^ a) ≤ Real.exp ((p + C) ^ C) := by
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (p + C) ^ a := pow_le_pow_left₀ (by positivity : 0 ≤ p + (a : ℝ))
      (add_le_add le_rfl (Nat.cast_le.mpr haC)) a
    _ ≤ _ := pow_le_pow_right₀ (by
      have hC : (2 : ℝ) ≤ C := Nat.cast_le.mpr (ha.trans haC)
      linarith) haC

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledFixedMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

def markedNativeLiftInput (p : ℝ) : ℝ := (p + 2) ^ 11 + p

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

def fullMarkedNativeInput (s a C : ℕ) (p : ℝ) : ℝ :=
  (pointwiseFastSectionInput s p + C) ^ C + (p + 2) ^ a + pointwiseFastSectionInput s p

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.Separation
namespace OAI

section

namespace Erdos3

theorem eq_zero_of_integer_mul_of_abs_lt {x D : ℝ} (hD : 0 < D)
    (hgrid : ∃ z : ℤ, D * x = z) (hsmall : |x| < 1 / D) : x = 0 := by
  obtain ⟨z, hz⟩ := hgrid
  have hzsmall : |(z : ℝ)| < 1 := by
    rw [← hz, abs_mul, abs_of_pos hD]
    have h := (lt_div_iff₀ hD).mp hsmall
    nlinarith
  have hz0 : z = 0 := by
    have h : |z| < (1 : ℤ) := by exact_mod_cast hzsmall
    have hnonneg := abs_nonneg z
    have habs : |z| = 0 := by omega
    exact abs_eq_zero.mp habs
  rw [hz0, Int.cast_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left hD.ne'

theorem separate_kernel {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : V →ₗ[ℝ] (ι → ℝ)) (a b : V) {D : ℝ} (hD : 0 < D)
    (hsum : Q (a + b) = 0)
    (hgrid : ∀ i, ∃ z : ℤ, D * Q b i = z)
    (hsmall : ∀ i, |Q a i| < 1 / D) : Q a = 0 ∧ Q b = 0 := by
  have hcoords : ∀ i, Q a i + Q b i = 0 := by
    intro i
    have h := congrFun hsum i
    simpa only [map_add, Pi.add_apply, Pi.zero_apply] using h
  have hb : Q b = 0 := by
    funext i
    apply eq_zero_of_integer_mul_of_abs_lt hD (hgrid i)
    have hneg : Q b i = -(Q a i) := by linarith [hcoords i]
    simpa only [hneg, abs_neg] using hsmall i
  refine ⟨?_, hb⟩
  funext i
  change Q a i = 0
  have hbi : Q b i = 0 := congrFun hb i
  linarith [hcoords i]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FrozenPolynomialAffineRange
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem polynomialFamily_eval_mem {J τ R : Type*} [Fintype J] [CommRing R]
    (P : J → MvPolynomial τ R) (K : Submodule R (J → R))
    (hP : ∀ α, (fun j => (P j).coeff α) ∈ K) (x : τ → R) :
    (fun j => MvPolynomial.eval x (P j)) ∈ K := by
  classical
  let S : Finset (τ →₀ ℕ) := Finset.univ.biUnion (fun j => (P j).support)
  have he (j : J) : MvPolynomial.eval x (P j) =
      ∑ α ∈ S, (α.prod fun i n => x i ^ n) * (P j).coeff α := by
    conv_lhs => rw [← (P j).support_sum_monomial_coeff, map_sum]
    simp only [eval_monomial, mul_comm]
    apply Finset.sum_subset
    · intro α hα
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hα⟩
    · intro α _ hα
      have hz : (P j).coeff α = 0 := by
        simpa only [mem_support_iff, not_not] using hα
      rw [hz]
      simp
  have he' : (fun j => MvPolynomial.eval x (P j)) =
      ∑ α ∈ S, (α.prod fun i n => x i ^ n) • (fun j => (P j).coeff α) := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he j
  rw [he']
  exact K.sum_mem (fun α _ => K.smul_mem _ (hP α))

end Erdos3

end

end OAI
end


