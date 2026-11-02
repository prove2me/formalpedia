-- Prove2me | Definitions.Def_OAIQ093D002
-- name    : OAIQ093D002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T15:59:42.899138+00:00
-- url     : https://prove2.me/theorems/52aec02b-0cd4-4246-8008-fd8b2c3a9b7e
-- title:
--   Definitions bundle OAIQ093D002 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 279 declarations of OpenAI's Lean: 108 definitions, 4 inductive types or structures, 3 instances and 164 theorems. The definitions and types are `OAI.PolycyclicRecognition.CentralLayer`, `OAI.PolycyclicRecognition.CentralLayersSpace`, `OAI.PolycyclicRecognition.CoarsePair`, `OAI.PolycyclicRecognition.CompactProfileEstimates`, `OAI.PolycyclicRecognition.CompactlyGeneratedLCModel`, `OAI.PolycyclicRecognition.CompletedCohomology`, `OAI.PolycyclicRecognition.ComplexCartan.imaginaryPart`, `OAI.PolycyclicRecognition.ComplexCartan.phase`, `OAI.PolycyclicRecognition.ComplexNormedLieAlgebra`, `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.HasSubexponentialUpperBound`, `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.IsMixedWord`, `OAI.PolycyclicRecognition.LipschitzPairBounds`, `OAI.PolycyclicRecognition.NilpotentExponentialCoordinatesInput`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NilpotentGlobalExponentialChartInput`, `OAI.PolycyclicRecognition.NilpotentLieIntegrationInput`, `OAI.PolycyclicRecognition.NormalizedPair`, `OAI.PolycyclicRecognition.RationalAbelianSpace`, `OAI.PolycyclicRecognition.RealNormedLieAlgebra`, `OAI.PolycyclicRecognition.adjointLinearMap`, `OAI.PolycyclicRecognition.adjointOperator`, `OAI.PolycyclicRecognition.algebraExpUnit`, `OAI.PolycyclicRecognition.basisBracket`, `OAI.PolycyclicRecognition.basisBracketLinear`, `OAI.PolycyclicRecognition.basisDynkinParameter`, `OAI.PolycyclicRecognition.bilinearDynkinPolynomial`, `OAI.PolycyclicRecognition.bracketWordLength`, `OAI.PolycyclicRecognition.bracketWordNodes`, `OAI.PolycyclicRecognition.cartanRootSubalgebra`, `OAI.PolycyclicRecognition.cartanRootSubmodule`, `OAI.PolycyclicRecognition.cellProbabilityMeasure`, `OAI.PolycyclicRecognition.chartExponentialFlow`, `OAI.PolycyclicRecognition.chartInvariantFrame`, `OAI.PolycyclicRecognition.chartVectorField`, `OAI.PolycyclicRecognition.conePolarTemplate`, `OAI.PolycyclicRecognition.conePolarWidth`, `OAI.PolycyclicRecognition.coneProbeSecond`, `OAI.PolycyclicRecognition.conjugationDifferentialHom` and 72 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_AlgebraOneParameter`, `PolycyclicRecognition_Algebra_ChartedInvariantFrame`, `PolycyclicRecognition_Algebra_ChartedVectorFieldBracket`, `PolycyclicRecognition_Algebra_ConePolarTemplate`, `PolycyclicRecognition_Algebra_ConeQuotientAutomorphism`, `PolycyclicRecognition_Algebra_CoordinateOrbitRepresentation`, `PolycyclicRecognition_Algebra_DynkinJacobian`, `PolycyclicRecognition_Algebra_DynkinLocalParameters`, `PolycyclicRecognition_Algebra_DynkinWords`, `PolycyclicRecognition_Algebra_FilteredBijection`, `PolycyclicRecognition_Algebra_FilteredDeterminant`, `PolycyclicRecognition_Algebra_FixedChartTranslation`, `PolycyclicRecognition_Algebra_GeneratorConjugation`, `PolycyclicRecognition_Algebra_GeneratorOrbit`, `PolycyclicRecognition_Algebra_MixedWordIdeal`, `PolycyclicRecognition_Algebra_NilpotentAutomorphism`, `PolycyclicRecognition_Algebra_NilpotentCoordinatesInput`, `PolycyclicRecognition_Algebra_NormalizedFreeRepresentation`, `PolycyclicRecognition_Algebra_PairAction`, `PolycyclicRecognition_Algebra_PairCharts`, `PolycyclicRecognition_Algebra_PolynomialGroupLaws`, `PolycyclicRecognition_Algebra_QuotientSectionCoordinates`, `PolycyclicRecognition_Algebra_RationalAbelianRank`, `PolycyclicRecognition_Algebra_RationalCentralLayers`, `PolycyclicRecognition_Algebra_RationalConjugation`, `PolycyclicRecognition_Algebra_RationalNilpotentQuotient`, `PolycyclicRecognition_Algebra_RealTorusContinuity`, `PolycyclicRecognition_Algebra_RelatedVectorFieldBracket`, `PolycyclicRecognition_Algebra_RightTranslationInvariant`, `PolycyclicRecognition_Algebra_SequenceSubexponential`, `PolycyclicRecognition_Algebra_SequenceSubexponentialOperations`, `PolycyclicRecognition_Algebra_SubexponentialBounds`, `PolycyclicRecognition_Algebra_SuspendedVectorFieldBracket`, `PolycyclicRecognition_Analysis_CellProfileRestriction`, `PolycyclicRecognition_Analysis_CompactPairs`, `PolycyclicRecognition_Analysis_CompactProfileEstimates`, `PolycyclicRecognition_Analysis_ConeProbeEndpoints`, `PolycyclicRecognition_Analysis_IdealSectionBoxCoordinates`, `PolycyclicRecognition_Analysis_InvariantIntegralCurve`, `PolycyclicRecognition_Analysis_JacobianMeasure`, `PolycyclicRecognition_Analysis_KernelHaarTransport`, `PolycyclicRecognition_Analysis_LinearProfilesOnBall`, `PolycyclicRecognition_Analysis_MixedWordBoxModel`, `PolycyclicRecognition_Analysis_NeighborProfileGluing`, `PolycyclicRecognition_Analysis_NilpotentBoxes`, `PolycyclicRecognition_Analysis_NilpotentHaarAutomorphisms`, `PolycyclicRecognition_Analysis_NilpotentHaarInput`, `PolycyclicRecognition_Analysis_OccupationSampling`, `PolycyclicRecognition_Analysis_ParametrizedSupportPaths`, `PolycyclicRecognition_Analysis_RescaledImageVolume`, `PolycyclicRecognition_Analysis_SupportVisitPaths`, `PolycyclicRecognition_Analysis_TranslatedBoxMass`, `PolycyclicRecognition_Analysis_TranslationCovering`, `PolycyclicRecognition_Finiteness_CompletedCohomology`, `PolycyclicRecognition_Finiteness_NormalizedSyzygyFunctor`, `PolycyclicRecognition_Geometry_AlgebraExponential`, `PolycyclicRecognition_Geometry_CanonicalExponentialMeasure`, `PolycyclicRecognition_Geometry_CartanConeInvariance`, `PolycyclicRecognition_Geometry_CartanGenerators`, `PolycyclicRecognition_Geometry_CartanJacobian`, `PolycyclicRecognition_Geometry_CartanPolarTiledChains`, `PolycyclicRecognition_Geometry_CartanSamplingParameters`, `PolycyclicRecognition_Geometry_ChartedExponentialFlow`, `PolycyclicRecognition_Geometry_ComplexCartanRotations`, `PolycyclicRecognition_Geometry_ConjugationFlow`, `PolycyclicRecognition_Geometry_ConstructExponential`, `PolycyclicRecognition_Geometry_CoordinateLieBrackets`, `PolycyclicRecognition_Geometry_ExponentialBoxCoordinates`, `PolycyclicRecognition_Geometry_ExponentialCellMass`, `PolycyclicRecognition_Geometry_ExponentialEmbedding`, `PolycyclicRecognition_Geometry_ExponentialGoodCells`, `PolycyclicRecognition_Geometry_ExponentialIdeal`, `PolycyclicRecognition_Geometry_ExponentialIntegralCurve`, `PolycyclicRecognition_Geometry_ExponentialNaturality`, `PolycyclicRecognition_Geometry_ExponentialProduct`, `PolycyclicRecognition_Geometry_ExponentialQuotientSection`, `PolycyclicRecognition_Geometry_ExponentialRightHaar`, `PolycyclicRecognition_Geometry_ExponentialSubsetVolume`, `PolycyclicRecognition_Geometry_FiniteLieNorm`, `PolycyclicRecognition_Geometry_IntrinsicAdjointDerivative`, `PolycyclicRecognition_Geometry_IntrinsicAdjointExponential`, `PolycyclicRecognition_Geometry_LieAdjointSmoothness`, `PolycyclicRecognition_Geometry_LieConjugationDifferential`, `PolycyclicRecognition_Geometry_LieExponential`, `PolycyclicRecognition_Geometry_LieIntegrationInput`, `PolycyclicRecognition_Geometry_LieWordDerivative`, `PolycyclicRecognition_Geometry_LieWordDifference`, `PolycyclicRecognition_Geometry_LieWordDifferential`, `PolycyclicRecognition_Geometry_ManifoldRelatedBracket`, `PolycyclicRecognition_Geometry_NilpotentCoordinateFlow`, `PolycyclicRecognition_Geometry_NilpotentDerivationFlow`, `PolycyclicRecognition_Geometry_NilpotentExponential`, `PolycyclicRecognition_Geometry_ParametricLieWords`, `PolycyclicRecognition_Geometry_PositiveWeightCones`, `PolycyclicRecognition_Geometry_RealNormedLieAlgebra`, `PolycyclicRecognition_Geometry_SemisimpleLieLogarithm`, `PolycyclicRecognition_Geometry_SmoothAutonomousCurve`, `PolycyclicRecognition_Geometry_SmoothExponentialCurve`, `PolycyclicRecognition_Geometry_SmoothIntegralCurve`, `PolycyclicRecognition_Geometry_SupportFlowLegs`, `PolycyclicRecognition_Geometry_TriangulableLieModel`, `PolycyclicRecognition_Geometry_WeightRotationCharacter`, `PolycyclicRecognition_Geometry_WeightSamplingPolytope`, `PolycyclicRecognition_Geometry_WeightSpaceWordSpan`, `PolycyclicRecognition_Geometry_WeightedBoxVolume`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D007`, `OAIQ093D008`, `OAIQ093D009`, `OAIQ093D010` and `OAIQ093D011`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition

section
-- module Solutions.OAIQ093_PR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential coordinates for upper unipotent matrices

The analytic matrix exponential is a finite polynomial on nilpotent matrices.
This bridges the ordered-product bounds to actual exponential increments,
rather than a separately stipulated polynomial group law.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Nilpotence truncates the analytic exponential exactly. -/
theorem exp_eq_finite_sum_of_pow_eq_zero (x : A) {c : ℕ} (hx : x ^ c = 0) :
    NormedSpace.exp x = ∑ k ∈ Finset.range c, ((k.factorial : ℝ)⁻¹) • x ^ k := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  apply tsum_eq_sum
  intro k hk
  have hck : c ≤ k := by simpa using hk
  rw [pow_eq_zero_of_le hck hx, smul_zero]

end Algebra

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConjugationFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual conjugation flow of a matrix exponential

Left and right multiplication give the exponential formula for the adjoint
operator. This supplies the conjugation identity used by root distortion.
-/

noncomputable section

namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def leftRegular : A →ₐ[ℝ] (A →L[ℝ] A) where
  toFun := ContinuousLinearMap.mul ℝ A
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

def rightRegular : Aᵐᵒᵖ →ₐ[ℝ] (A →L[ℝ] A) where
  toFun x := (ContinuousLinearMap.mul ℝ A).flip x.unop
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

theorem continuous_leftRegular : Continuous (leftRegular : A → (A →L[ℝ] A)) :=
  (ContinuousLinearMap.mul ℝ A).continuous

theorem continuous_rightRegular : Continuous (rightRegular : Aᵐᵒᵖ → (A →L[ℝ] A)) :=
  (ContinuousLinearMap.mul ℝ A).flip.continuous.comp MulOpposite.continuous_unop

def adjointOperator (x : A) : A →L[ℝ] A :=
  leftRegular x - rightRegular (MulOpposite.op x)

@[simp] theorem adjointOperator_apply (x y : A) :
    adjointOperator x y = x * y - y * x := rfl

variable [CompleteSpace A]

/-- Exponentiating the commutator operator gives actual conjugation. -/
theorem exp_adjointOperator_apply (x y : A) :
    (NormedSpace.exp (adjointOperator x)) y =
      NormedSpace.exp x * y * NormedSpace.exp (-x) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let : NormedAlgebra ℚ (A →L[ℝ] A) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ Aᵐᵒᵖ := NormedAlgebra.restrictScalars ℚ ℝ _
  have hc : Commute (leftRegular x) (-rightRegular (MulOpposite.op x)) := by
    ext z
    simp [leftRegular, rightRegular, mul_assoc]
  rw [adjointOperator, sub_eq_add_neg, NormedSpace.exp_add_of_commute hc]
  have hl := NormedSpace.map_exp (leftRegular (A := A)) continuous_leftRegular x
  have hr := NormedSpace.map_exp (rightRegular (A := A)) continuous_rightRegular
    (MulOpposite.op (-x))
  have he : rightRegular (MulOpposite.op (-x)) = -rightRegular (MulOpposite.op x) := by
    rw [MulOpposite.op_neg, map_neg]
  rw [he] at hr
  rw [← hl, ← hr]
  simp only [NormedSpace.exp_op]
  simp [leftRegular, rightRegular, mul_assoc]

theorem exp_smul_adjointOperator_apply (t : ℝ) (x y : A) :
    (NormedSpace.exp (t • adjointOperator x)) y =
      NormedSpace.exp (t • x) * y * NormedSpace.exp (-(t • x)) := by
  have h : t • adjointOperator x = adjointOperator (t • x) := by
    ext y
    simp [smul_sub]
  rw [h, exp_adjointOperator_apply]

/-- A continuous linear intertwiner also intertwines the actual analytic
operator exponentials, so restricted root actions agree with ambient ones. -/
theorem exp_intertwine_apply
    {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (f : V →L[ℝ] U) (S : V →L[ℝ] V) (T : U →L[ℝ] U)
    (hf : ∀ v, f (S v) = T (f v)) (v : V) :
    f ((NormedSpace.exp S) v) = (NormedSpace.exp T) (f v) := by
  have hp (n : ℕ) (v : V) : f ((S ^ n) v) = (T ^ n) (f v) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change f (S ((S ^ n) v)) = T ((T ^ n) (f v))
      rw [hf, ih]
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) S).map
    (f.comp (ContinuousLinearMap.apply ℝ V v))
    (f.comp (ContinuousLinearMap.apply ℝ V v)).continuous
  have ht := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) T).map
    (ContinuousLinearMap.apply ℝ U (f v))
    (ContinuousLinearMap.apply ℝ U (f v)).continuous
  have hs' : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℝ) • (T ^ n) (f v))
      (f ((NormedSpace.exp S) v)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, smul_apply, map_smul, hp] using hs
  have ht' : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℝ) • (T ^ n) (f v))
      ((NormedSpace.exp T) (f v)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
      smul_apply] using ht
  exact hs'.unique ht'

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AlgebraExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra exponentials as actual group elements

The unit-valued exponential keeps the inverse explicit. This bridges the
operator conjugation identity to a faithful group representation.
-/

noncomputable section

namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def algebraExpUnit (x : A) : Aˣ := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact
    { val := NormedSpace.exp x
      inv := NormedSpace.exp (-x)
      val_inv := by
        rw [← NormedSpace.exp_add_of_commute (Commute.refl x).neg_right,
          add_neg_cancel, NormedSpace.exp_zero]
      inv_val := by
        rw [← NormedSpace.exp_add_of_commute (Commute.refl x).neg_left,
          neg_add_cancel, NormedSpace.exp_zero] }

@[simp] theorem coe_algebraExpUnit (x : A) :
    (algebraExpUnit x : A) = NormedSpace.exp x := rfl

@[simp] theorem algebraExpUnit_neg (x : A) :
    algebraExpUnit (-x) = (algebraExpUnit x)⁻¹ := by
  apply Units.ext
  rfl

@[simp] theorem algebraExpUnit_zero : algebraExpUnit (0 : A) = 1 := by
  apply Units.ext
  exact NormedSpace.exp_zero

theorem algebraExpUnit_conj (u : Aˣ) (x : A) :
    algebraExpUnit (u * x * (u⁻¹ : Aˣ) : A) = u * algebraExpUnit x * u⁻¹ := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Units.ext
  exact NormedSpace.exp_units_conj u x

theorem algebraExpUnit_continuous : Continuous (algebraExpUnit : A → Aˣ) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Units.continuous_iff.mpr
  exact ⟨NormedSpace.exp_continuous, NormedSpace.exp_continuous.comp continuous_neg⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlgebraOneParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiable one-parameter subgroups in a real Banach algebra

The derivative at zero determines the curve. Multiplication by the inverse
exponential produces a function with zero derivative everywhere.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem oneParameter_hasDerivAt {f : ℝ → A} {v : A}
    (hadd : ∀ s t, f (s + t) = f s * f t) (hzero : HasDerivAt f v 0) (t : ℝ) :
    HasDerivAt f (v * f t) t := by
  have hbase : HasDerivAt (fun s => f s * f t) (v * f t) (t - t) := by
    rw [sub_self]
    exact hzero.mul_const (f t)
  have h := hbase.scomp (h := fun s : ℝ => s - t) t
    ((hasDerivAt_id t).sub_const t)
  have heq : (fun s : ℝ => f (s - t) * f t) = f := by
    funext s
    rw [← hadd, sub_add_cancel]
  change HasDerivAt (fun s : ℝ => f (s - t) * f t) _ t at h
  rw [heq] at h
  simpa only [sub_self, one_smul, mul_one] using h

theorem oneParameter_eq_exp {f : ℝ → A} {v : A}
    (hf0 : f 0 = 1) (hadd : ∀ s t, f (s + t) = f s * f t)
    (hzero : HasDerivAt f v 0) (t : ℝ) : f t = NormedSpace.exp (t • v) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let u : ℝ → A := fun s => NormedSpace.exp (s • (-v)) * f s
  have hu (s : ℝ) : HasDerivAt u 0 s := by
    have h := (hasDerivAt_exp_smul_const (-v) s).mul (oneParameter_hasDerivAt hadd hzero s)
    change HasDerivAt u _ s at h
    simpa only [mul_neg, neg_mul, mul_assoc, neg_add_cancel] using h
  have ht := is_const_of_deriv_eq_zero (fun s => (hu s).differentiableAt)
    (fun s => (hu s).deriv) t 0
  have hu0 : u 0 = 1 := by simp only [u, zero_smul, NormedSpace.exp_zero, one_mul, hf0]
  rw [hu0] at ht
  have hk : NormedSpace.exp (t • v) * NormedSpace.exp (t • (-v)) = 1 := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl (t • v)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  have hm := congrArg (fun z : A => NormedSpace.exp (t • v) * z) ht
  change NormedSpace.exp (t • v) * (NormedSpace.exp (t • (-v)) * f t) =
    NormedSpace.exp (t • v) * 1 at hm
  rw [← mul_assoc, hk, one_mul, mul_one] at hm
  exact hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RelatedVectorFieldBracket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Brackets of related vector fields

The relation is local, so this lemma can be applied in a manifold chart.
It will identify the bracket of the actual representation differential.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_lieBracket_of_related
    {f : E → F} {V W : E → E} {V' W' : F → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hV' : DifferentiableAt ℝ V' (f x)) (hW' : DifferentiableAt ℝ W' (f x))
    (hrelV : ∀ᶠ y in 𝓝 x, fderiv ℝ f y (V y) = V' (f y))
    (hrelW : ∀ᶠ y in 𝓝 x, fderiv ℝ f y (W y) = W' (f y)) :
    fderiv ℝ f x (VectorField.lieBracket ℝ V W x) =
      VectorField.lieBracket ℝ V' W' (f x) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hrelV' : (fun y => fderiv ℝ f y (V y)) =ᶠ[𝓝 x] V' ∘ f := hrelV
  have hrelW' : (fun y => fderiv ℝ f y (W y)) =ᶠ[𝓝 x] W' ∘ f := hrelW
  rw [VectorField.fderiv_apply_lieBracket hf (by norm_num) hW hV,
    hrelW'.fderiv_eq, hrelV'.fderiv_eq,
    fderiv_comp x hW' hfd, fderiv_comp x hV' hfd]
  simp only [ContinuousLinearMap.comp_apply, VectorField.lieBracket]
  have hVx : fderiv ℝ f x (V x) = V' (f x) := hrelV'.self_of_nhds
  have hWx : fderiv ℝ f x (W x) = W' (f x) := hrelW'.self_of_nhds
  rw [hVx, hWx]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothAutonomousCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness bootstrapping for autonomous integral curves

Only the differential equation and smoothness of its vector field are used.
This is the local analytic step needed for smooth Lie exponential curves.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffAt_of_autonomous_curve {F : E → E} {γ : ℝ → E} {t₀ : ℝ}
    (hF : ContDiffAt ℝ ∞ F (γ t₀))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (F (γ t)) t) :
    ContDiffAt ℝ ∞ γ t₀ := by
  apply contDiffAt_infty.2
  intro n
  induction n with
  | zero =>
    obtain ⟨U, hU, hder⟩ := eventually_iff_exists_mem.1 hγ
    exact contDiffAt_zero.2 ⟨U, hU, fun t ht => (hder t ht).continuousAt.continuousWithinAt⟩
  | succ n ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.2
    refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (F (γ t)), ?_, ?_⟩
    · obtain ⟨U, hU, hder⟩ := eventually_iff_exists_mem.1 hγ
      exact ⟨U, hU, fun t ht => (hder t ht).hasFDerivAt⟩
    · exact contDiffAt_const.smulRight ((hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp t₀ ih)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothIntegralCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth integral curves on a smooth manifold without boundary -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Bundle
open scoped Topology Manifold ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

/-- A smooth vector field pushed into a vector-space chart is smooth. -/
theorem contMDiffAt_chart_velocity
    {φ : M → E} {v : (x : M) → TangentSpace (𝓘(ℝ, E)) x} {x₀ : M}
    (hφ : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ x₀)
    (hv : ContMDiffAt (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, v x⟩ : TangentBundle (𝓘(ℝ, E)) M)) x₀) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞
      (fun x => (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ x) (v x)) x₀ := by
  have hϕ := hφ.mfderiv_const (m := ∞) (by simp)
  have hb := ContMDiffAt.clm_apply_of_inCoordinates hϕ hv hφ
  exact (contMDiff_snd_tangentBundle_modelSpace E (𝓘(ℝ, E))).contMDiffAt.comp x₀ hb

/-- Smoothness of a vector field upgrades its integral curves from the
defining first derivative to all finite derivatives. -/
theorem IsMIntegralCurve.contMDiff
    {γ : ℝ → M} {v : (x : M) → TangentSpace (𝓘(ℝ, E)) x}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, E)) γ v)
    (hv : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, v x⟩ : TangentBundle (𝓘(ℝ, E)) M))) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ γ := by
  intro t₀
  let φ := extChartAt (𝓘(ℝ, E)) (γ t₀)
  let V : M → E := fun x => (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ x) (v x)
  let F : E → E := V ∘ φ.symm
  let η : ℝ → E := φ ∘ γ
  have hcont : ContinuousAt γ t₀ := (hγ t₀).continuousAt
  have hφ : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ (γ t₀) :=
    contMDiffAt_extChartAt
  have hV : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ V (γ t₀) :=
    contMDiffAt_chart_velocity hφ (hv (γ t₀))
  have hinv : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ.symm (φ (γ t₀)) := by
    simpa only [φ, mfld_simps, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, E)) (n := ∞) (γ t₀))
  have hF : ContDiffAt ℝ ∞ F (η t₀) := by
    have hh := hV.comp_of_eq hinv (by simp [φ])
    exact hh.contDiffAt
  have hsource : ∀ᶠ t in 𝓝 t₀, γ t ∈ φ.source :=
    hcont.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (γ t₀))
  have hη : ∀ᶠ t in 𝓝 t₀, HasDerivAt η (F (η t)) t := by
    filter_upwards [hsource] with t ht
    have hchart : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)) :=
      (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E)) (by simpa [φ] using ht)).hasMFDerivAt
    have hh : HasFDerivAt η
        ((1 : ℝ →L[ℝ] ℝ).smulRight ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)) (v (γ t)))) t := by
      have raw : HasFDerivAt η
          ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)).comp
            ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))) t :=
        (hchart.comp t (hγ t)).hasFDerivAt
      have heq : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))) =
          (1 : ℝ →L[ℝ] ℝ).smulRight
            ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)) (v (γ t))) := by
        ext
        simp
      rw [heq] at raw
      exact raw
    change HasDerivAt η
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm (φ (γ t))))
        (v (φ.symm (φ (γ t))))) t
    rw [φ.left_inv ht]
    have hd := hh.hasDerivAt
    change HasDerivAt η ((1 : ℝ) • ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)) (v (γ t)))) t at hd
    simpa only [one_smul] using hd
  have hsmooth := contDiffAt_of_autonomous_curve hF hη
  exact (contMDiffAt_iff_target).2 ⟨hcont, hsmooth.contMDiffAt⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ChartedVectorFieldBracket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lie brackets in vector-space charts

The source chart is used only locally. This bridges the differential of an
algebra-valued map with the intrinsic bracket of vector fields.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function Bundle VectorField
open scoped Manifold ContDiff Topology

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

def chartVectorField (x₀ : M) (V : (x : M) → TangentSpace (𝓘(ℝ, E)) x) : E → E :=
  mpullback (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm V

theorem mlieBracket_eq_chartBracket
    (V W : (x : M) → TangentSpace (𝓘(ℝ, E)) x) (x₀ : M) :
    mlieBracket (𝓘(ℝ, E)) V W x₀ =
      lieBracket ℝ (chartVectorField x₀ V) (chartVectorField x₀ W)
        (extChartAt (𝓘(ℝ, E)) x₀ x₀) := by
  unfold mlieBracket
  rw [mlieBracketWithin_apply, mfderiv_extChartAt_self]
  simp only [mfld_simps, mpullbackWithin_univ]
  change (ContinuousLinearMap.id ℝ E).inverse
    (lieBracketWithin ℝ (chartVectorField x₀ V) (chartVectorField x₀ W) univ
      (extChartAt (𝓘(ℝ, E)) x₀ x₀)) = _
  rw [ContinuousLinearMap.inverse_id]
  change lieBracketWithin ℝ (chartVectorField x₀ V) (chartVectorField x₀ W) univ
    (extChartAt (𝓘(ℝ, E)) x₀ x₀) = _
  rw [lieBracketWithin_univ]
  rfl

theorem differentiableAt_chartVectorField [CompleteSpace E]
    {V : (x : M) → TangentSpace (𝓘(ℝ, E)) x} {x₀ : M}
    (hV : MDifferentiableAt (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓘(ℝ, E)) M)) x₀) :
    DifferentiableAt ℝ (chartVectorField x₀ V) (extChartAt (𝓘(ℝ, E)) x₀ x₀) := by
  have hh := (hV.mdifferentiableWithinAt (s := univ)).differentiableWithinAt_mpullbackWithin_vectorField
  apply differentiableWithinAt_univ.1
  simpa only [mfld_simps, mpullbackWithin_univ, chartVectorField] using hh

theorem mfderiv_chart_symm_base (x₀ : M) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀).symm
      (extChartAt (𝓘(ℝ, E)) x₀ x₀) = ContinuousLinearMap.id ℝ E := by
  have hrange : range (𝓘(ℝ, E)) = (univ : Set E) := by ext x; simp
  have hh := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x₀)
  rw [hrange, mfderivWithin_univ] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): the tangent-space instances and casts it
declares beside `TangentSpace` (`IsManifold/Basic.lean`, `IsManifold/ExtChartAt.lean`). -/

section TangentSpaceCompat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

instance TangentSpace.instT2SpaceCompat : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)

end TangentSpaceCompat

namespace OAI

/-! # Exponential maps of actual real Lie groups

The differential and one-parameter-subgroup characterization identifies the
ordinary Lie-group exponential without requiring a pre-existing library
construction of its global flow.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [FiniteDimensional ℝ E] [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem IsGroupExponential.map_neg
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : Exp (-v) = (Exp v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have h := hExp.map_add_smul v (-1) 1
  simpa only [neg_add_cancel, zero_smul, neg_one_smul, one_smul, hExp.map_zero] using h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialIntegralCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic exponential curves and the invariant vector field

The group law and derivative at zero determine the global differential
equation of an intrinsic exponential curve.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [FiniteDimensional ℝ E] in
theorem IsGroupExponential.isMIntegralCurve
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) (fun t : ℝ => Exp (t • v))
      (mulInvariantVectorField v) := by
  intro t
  let γ : ℝ → G := fun s => Exp (s • v)
  let D : ℝ →L[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v
  have hzero : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (t - t) D := by
    rw [sub_self]
    exact hExp.hasMFDerivAt_zero v
  have hshift : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun s : ℝ => s - t) t
      (ContinuousLinearMap.id ℝ ℝ) := by
    have hD : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) =
        ContinuousLinearMap.id ℝ ℝ := by ext; simp
    simpa only [id_eq, hD] using
      ((hasDerivAt_id t).sub_const t).hasFDerivAt.hasMFDerivAt
  have hbase := HasMFDerivAt.comp t (f := fun s : ℝ => s - t) hzero hshift
  have hleft : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g)
      (γ (t - t)) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) := by
    rw [show γ (t - t) = 1 from by simp [γ, hExp.map_zero]]
    have h : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1 :=
      (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := γ t) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun g : G => γ t * g)).mdifferentiableAt
        (by simp)
    exact h.hasMFDerivAt
  have hder := hleft.comp t hbase
  have heq : (fun s : ℝ => γ t * γ (s - t)) = γ := by
    funext s
    dsimp [γ]
    rw [← hExp.map_add_smul]
    congr 2
    ring
  change HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ t _
  change HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E))
    (fun s : ℝ => γ t * γ (s - t)) t _ at hder
  rw [heq] at hder
  apply hder.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let s : ℝ := r
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) (s • v) =
    s • (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => γ t * g) 1) v
  exact map_smul _ s v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_InvariantIntegralCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global integral curves of left-invariant vector fields -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [FiniteDimensional ℝ E] in
theorem mulInvariantVectorField_mul
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (a x : G) :
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) x)
      (mulInvariantVectorField v x) = mulInvariantVectorField v (a * x) := by
  have hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => x * g) 1 :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := x) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun g : G => x * g)).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (x * 1) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := a) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun g : G => a * g)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp (I' := 𝓘(ℝ, E)) 1 hg hf
  have heq : (fun g : G => a * g) ∘ (fun g : G => x * g) = fun g => (a * x) * g := by
    ext g
    exact (mul_assoc a x g).symm
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      ((fun g : G => a * g) ∘ (fun g : G => x * g)) 1 : E →L[ℝ] E) =
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (x * 1) : E →L[ℝ] E).comp
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => x * g) 1) at hc
  rw [heq] at hc
  have h := congrArg (fun L : E →L[ℝ] E => L v) hc
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => (a * x) * g) 1) v =
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (x * 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => x * g) 1) v) at h
  have hx : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (x * 1) : E →L[ℝ] E) =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) x : E →L[ℝ] E) := by
    congr 1
    exact mul_one x
  rw [hx] at h
  exact h.symm

omit [FiniteDimensional ℝ E] in
theorem IsMIntegralCurveOn.mul_left_invariant
    {γ : ℝ → G} {s : Set ℝ} {v : GroupLieAlgebra (𝓘(ℝ, E)) G}
    (hγ : IsMIntegralCurveOn (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v) s) (a : G) :
    IsMIntegralCurveOn (I := 𝓘(ℝ, E)) (fun t => a * γ t) (mulInvariantVectorField v) s := by
  intro t ht
  have ha : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (γ t) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := a) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun g : G => a * g)).mdifferentiableAt (by simp)
  apply (ha.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let u : ℝ := r
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => a * g) (γ t))
      (u • mulInvariantVectorField v (γ t)) = u • mulInvariantVectorField v (a * γ t)
  rw [map_smul, mulInvariantVectorField_mul]

/-- A fixed local existence time at the identity works at every point by
left translation, so the manifold uniform-time theorem supplies global curves. -/
theorem exists_global_invariant_integralCurve [T2Space G]
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (x : G) :
    ∃ γ : ℝ → G, γ 0 = x ∧ IsMIntegralCurve (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v) := by
  have hv : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) 1
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by norm_num)
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (I := 𝓘(ℝ, E)) (x₀ := (1 : G)) 0 hv.contMDiffAt
  obtain ⟨ε, hε, hγon⟩ := isMIntegralCurveAt_iff'.mp hγ
  have hγI : IsMIntegralCurveOn (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v)
      (Set.Ioo (-ε) ε) := by
    simpa only [Real.ball_eq_Ioo, sub_zero, zero_sub, zero_add] using hγon
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε _ x
  intro y
  exact ⟨fun t => y * γ t, by simp [hγ0],
    PolycyclicRecognition.IsMIntegralCurveOn.mul_left_invariant hγI y⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConstructExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Construction of the intrinsic Lie exponential from global integral curves -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

omit [FiniteDimensional ℝ E] in
theorem invariant_integralCurve_unique
    {v : GroupLieAlgebra (𝓘(ℝ, E)) G} {γ δ : ℝ → G}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v))
    (hδ : IsMIntegralCurve (I := 𝓘(ℝ, E)) δ (mulInvariantVectorField v))
    (hzero : γ 0 = δ 0) : γ = δ := by
  have hv : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) 1
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by norm_num)
  exact isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv hγ hδ hzero

omit [FiniteDimensional ℝ E] [T2Space G] in
theorem invariant_integralCurve_mul_left
    {v : GroupLieAlgebra (𝓘(ℝ, E)) G} {γ : ℝ → G}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v)) (a : G) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) (fun t => a * γ t) (mulInvariantVectorField v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  exact PolycyclicRecognition.IsMIntegralCurveOn.mul_left_invariant hγ a

/-- The global integral curve starting at the identity. Its independence of
the existence theorem's choice follows from ODE uniqueness. -/
def invariantCurve (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : ℝ → G :=
  (exists_global_invariant_integralCurve v (1 : G)).choose

@[simp] theorem invariantCurve_zero (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    invariantCurve v 0 = 1 :=
  (exists_global_invariant_integralCurve v (1 : G)).choose_spec.1

theorem invariantCurve_isMIntegralCurve (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) (invariantCurve v) (mulInvariantVectorField v) :=
  (exists_global_invariant_integralCurve v (1 : G)).choose_spec.2

theorem invariantCurve_smul (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s : ℝ) :
    invariantCurve (s • v) = invariantCurve v ∘ (· * s) := by
  apply invariant_integralCurve_unique (invariantCurve_isMIntegralCurve (s • v))
  · simpa only [mulInvariantVectorField_smul] using
      (invariantCurve_isMIntegralCurve v).comp_mul s
  · simp

theorem invariantCurve_add (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s t : ℝ) :
    invariantCurve v (s + t) = invariantCurve v s * invariantCurve v t := by
  have heq := invariant_integralCurve_unique
    ((invariantCurve_isMIntegralCurve v).comp_add s)
    (invariant_integralCurve_mul_left (invariantCurve_isMIntegralCurve v) (invariantCurve v s))
    (by simp)
  simpa only [Function.comp_apply, add_comm] using congrFun heq t

/-- The intrinsic exponential, constructed without a Lie-theoretic existence input. -/
def groupExponential (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : G := invariantCurve v 1

theorem groupExponential_smul (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s : ℝ) :
    groupExponential (s • v) = invariantCurve v s := by
  simpa only [groupExponential, Function.comp_apply, one_mul] using
    congrFun (invariantCurve_smul v s) 1

/-- Existence of the Lie exponential with its one-parameter subgroup law and
its specified tangent vector at zero. -/
theorem groupExponential_isGroupExponential :
    IsGroupExponential (groupExponential (E := E) (G := G)) where
  map_zero := by
    have h := groupExponential_smul (0 : GroupLieAlgebra (𝓘(ℝ, E)) G) 0
    simpa only [zero_smul, invariantCurve_zero] using h
  map_add_smul v s t := by
    simp only [groupExponential_smul, invariantCurve_add]
  hasMFDerivAt_zero v := by
    have hv : mulInvariantVectorField v (1 : G) = v := by
      unfold mulInvariantVectorField
      rw [show (fun x : G => 1 * x) = id from funext one_mul, mfderiv_id]
      rfl
    have hfun : (fun t : ℝ => groupExponential (t • v)) = invariantCurve v :=
      funext (groupExponential_smul v)
    rw [hfun]
    apply (invariantCurve_isMIntegralCurve v 0).congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    let s : ℝ := r
    change s • mulInvariantVectorField v (invariantCurve v 0) = s • v
    congr 1
    have heq : (mulInvariantVectorField v (invariantCurve v 0) : E) =
        (mulInvariantVectorField v 1 : E) := by
      congr 1
      exact invariantCurve_zero v
    exact heq.trans hv

theorem exists_groupExponential :
    ∃ Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G, IsGroupExponential Exp :=
  ⟨groupExponential, groupExponential_isGroupExponential⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothExponentialCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth one-parameter curves of the intrinsic exponential -/

noncomputable section
namespace PolycyclicRecognition

open Bundle Function
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem contMDiff_invariantVectorField_infty (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun g => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle (𝓘(ℝ, E)) G)) := by
  let z : G → TangentBundle (𝓘(ℝ, E)) G := fun g => TotalSpace.mk' E g 0
  let c : G → TangentBundle (𝓘(ℝ, E)) G := fun _ => TotalSpace.mk' E 1 v
  have hz : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞ z :=
    contMDiff_zeroSection _ _
  have hc : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞ c :=
    contMDiff_const
  have hj := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (n := ∞) (M := G) (M' := G))
  have hm := (contMDiff_mul (G := G) (𝓘(ℝ, E)) ∞).contMDiff_tangentMap (m := ∞) (by simp)
  have h := (hm.comp hj).comp (hz.prodMk hc)
  convert! h with g
  · simp [z, c, equivTangentBundleProd, tangentMap]
  · change mulInvariantVectorField v g =
      mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
        (fun p : G × G => p.1 * p.2) (g, 1) (0, v)
    have hp := mfderiv_prod_eq_add_apply (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, E)) (p := (g, 1)) (v := (0, v))
      ((contMDiff_mul (𝓘(ℝ, E)) ∞).mdifferentiableAt (by simp))
    have hzero : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun z : G => z * 1) g)
        (0 : TangentSpace (𝓘(ℝ, E)) g) = 0 := map_zero _
    dsimp only at hp
    let w : E := mulInvariantVectorField v g
    exact (zero_add w).symm.trans
      ((congrArg (fun z : E => z + w) hzero).symm.trans hp.symm)

theorem IsGroupExponential.contMDiff_curve
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (fun t : ℝ => Exp (t • v)) :=
  PolycyclicRecognition.IsMIntegralCurve.contMDiff (hExp.isMIntegralCurve v)
    (contMDiff_invariantVectorField_infty v)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ChartedInvariantFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A left-invariant frame in a fixed chart

Linearity in the initial tangent vector lets a finite basis handle a
varying tangent parameter with only first derivatives of the frame.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter Function
open scoped Manifold Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

def chartInvariantFrame (g₀ : G) (z : E) : E →L[ℝ] E :=
  ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) g₀).symm z).inverse).comp
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (fun h : G => (extChartAt (𝓘(ℝ, E)) g₀).symm z * h) 1)

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem chartInvariantFrame_apply (g₀ : G) (z v : E) :
    chartInvariantFrame g₀ z v =
      chartVectorField g₀ (mulInvariantVectorField (I := 𝓘(ℝ, E)) v) z := rfl

@[simp] theorem chartInvariantFrame_one :
    chartInvariantFrame (1 : G) (extChartAt (𝓘(ℝ, E)) (1 : G) 1) =
      ContinuousLinearMap.id ℝ E := by
  unfold chartInvariantFrame
  rw [mfderiv_chart_symm_base]
  have heq : (fun h : G => (extChartAt (𝓘(ℝ, E)) (1 : G)).symm
      (extChartAt (𝓘(ℝ, E)) (1 : G) 1) * h) = id := by
    ext h
    rw [extChartAt_to_inv, one_mul]
    rfl
  rw [heq, mfderiv_id]
  change (ContinuousLinearMap.id ℝ E).inverse.comp (ContinuousLinearMap.id ℝ E) = _
  rw [ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_comp]

theorem differentiableAt_chartInvariantFrame_apply [CompleteSpace E]
    (g₀ : G) (v : E) :
    DifferentiableAt ℝ (fun z => chartInvariantFrame g₀ z v)
      (extChartAt (𝓘(ℝ, E)) g₀ g₀) :=
  differentiableAt_chartVectorField
    ((contMDiff_invariantVectorField_infty (E := E) v g₀).mdifferentiableAt (by simp))

theorem differentiableAt_chartInvariantFrame_parameter [FiniteDimensional ℝ E]
    {a : ℝ → E} {t : ℝ} (ha : DifferentiableAt ℝ a t) (g₀ : G) :
    DifferentiableAt ℝ (fun q : ℝ × E => chartInvariantFrame g₀ q.2 (a q.1))
      (t, extChartAt (𝓘(ℝ, E)) g₀ g₀) := by
  let b := Module.finBasis ℝ E
  have heq : (fun q : ℝ × E => chartInvariantFrame g₀ q.2 (a q.1)) =
      (fun q => ∑ i, (b.coord i (a q.1)) • chartInvariantFrame g₀ q.2 (b i)) := by
    funext q
    conv_lhs => rw [← b.sum_repr (a q.1)]
    simp only [map_sum, map_smul, Module.Basis.coord_apply]
  rw [heq]
  apply DifferentiableAt.fun_sum
  intro i _
  have hcoeff : DifferentiableAt ℝ (fun q : ℝ × E => b.coord i (a q.1))
      (t, extChartAt (𝓘(ℝ, E)) g₀ g₀) :=
    ((b.coord i).toContinuousLinearMap.differentiableAt).comp _
      (ha.comp _ differentiableAt_fst)
  have hframe : DifferentiableAt ℝ (fun z : E => chartInvariantFrame g₀ z (b i))
      (extChartAt (𝓘(ℝ, E)) g₀ g₀) :=
    differentiableAt_chartInvariantFrame_apply g₀ (b i)
  have hfr : DifferentiableAt ℝ (fun q : ℝ × E => chartInvariantFrame g₀ q.2 (b i))
      (t, extChartAt (𝓘(ℝ, E)) g₀ g₀) :=
    hframe.comp (t, extChartAt (𝓘(ℝ, E)) g₀ g₀) (f := fun q : ℝ × E => q.2)
      differentiableAt_snd
  exact hcoeff.smul hfr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConePolarTemplate
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polar templates and their exact vanishing directions

The compact unit slice of the negative polar has support zero on the cone
and strictly positive support at every functional outside the cone. These
are the widths used in the cone-ideal covering argument.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped Pointwise

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The unit-ball slice of the negative polar of the closed weight cone. -/
def conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) : Set W :=
  {x | ‖x‖ ≤ 1 ∧ ∀ β ∈ C, β x ≤ 0}

def conePolarWidth (C : ProperCone ℝ (StrongDual ℝ W)) (β : StrongDual ℝ W) : ℝ :=
  sSup (β '' conePolarTemplate C)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteLieNorm
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bracket bounds from finitely many structure constants

The norm is the coordinate maximum in a specified basis. Consequently the
bound applies uniformly to every rescaled word basis from the box calculus.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
  (b : Basis J ℝ L)

/-- Number of input letters in a bracket word. -/
def bracketWordLength {I : Type*} : FreeMagma I → ℕ
  | .of _ => 1
  | .mul u v => bracketWordLength u + bracketWordLength v

/-- Number of bracket operations in the word. -/
def bracketWordNodes {I : Type*} : FreeMagma I → ℕ
  | .of _ => 0
  | .mul u v => bracketWordNodes u + bracketWordNodes v + 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinWords
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded finite Dynkin expansions

The analytic BCH input is separated from its elementary coordinate estimate.
A degree-`c` expansion in right-nested words, with uniformly bounded
coefficients, has polynomial growth in the number of input factors.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- A right-nested bracket in a nonempty ordered list of letters. -/
def rightNestedWord {I : Type*} : (d : ℕ) → (Fin (d + 1) → I) → FreeMagma I
  | 0, f => .of (f 0)
  | d + 1, f => .of (f 0) * rightNestedWord d (fun i => f i.succ)

@[simp] theorem rightNestedWord_nodes {I : Type*} (d : ℕ) (f : Fin (d + 1) → I) :
    bracketWordNodes (rightNestedWord d f) = d := by
  induction d with
  | zero => rfl
  | succ d hd => simp [rightNestedWord, bracketWordNodes, hd]

abbrev DynkinCoefficients (c n : ℕ) := (d : Fin c) → (Fin (d.val + 1) → Fin n) → ℝ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products in actual nilpotent exponential boxes

The published finite BCH identity is transported to a chosen Lie-algebra
model. The uniform normalized structure constants then give the polynomial
product bound in the manuscript's box calculus, for every height scale and
letter support. No coordinate growth conclusion is assumed as an input.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- The exponential image of the coordinate cube of radius `R`. With the
supremum norm on the coordinate functions this is exactly the usual box. -/
def exponentialCoordinateBox {G J : Type*} [Fintype J]
    (exp : L → G) (b : Basis J ℝ L) (R : ℝ) : Set G :=
  {g | ∃ x : L, exp x = g ∧ ‖b.equivFun x‖ ≤ R}

theorem mem_exponentialCoordinateBox_iff {G J : Type*} [Fintype J]
    (exp : L → G) (b : Basis J ℝ L) (R : ℝ) (hR : 0 ≤ R) (g : G) :
    g ∈ exponentialCoordinateBox exp b R ↔ ∃ x, exp x = g ∧
      ∀ j, |b.repr x j| ≤ R := by
  simp only [exponentialCoordinateBox, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hb⟩
    exact ⟨x, hx, fun j => (Real.norm_eq_abs _ ▸ norm_le_pi_norm (b.equivFun x) j).trans hb⟩
  · rintro ⟨x, hx, hb⟩
    refine ⟨x, hx, ?_⟩
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    rw [Real.norm_eq_abs]
    exact hb j

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentAutomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the needed nilpotent automorphisms

The finite published Dynkin identity and bijectivity of the intrinsic
exponential suffice to integrate any Lie automorphism of the nilpotent
model. No general Lie-integration theorem is assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open LieModule
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)

/-- Conjugation through the intrinsic exponential as a bijection. -/
def exponentialConjugate (F : L ≃ₗ⁅ℝ⁆ L) : G ≃ G :=
  let q : L ≃ G := Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)
  q.symm.trans (F.toLinearEquiv.toEquiv.trans q)

omit [T2Space G] in
@[simp] theorem exponentialConjugate_apply_exp (F : L ≃ₗ⁅ℝ⁆ L) (x : L) :
    exponentialConjugate e Exp hbij F (Exp (e x)) = Exp (e (F x)) := by
  change Exp (e (F ((Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)).symm
    ((Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)) x)))) = _
  rw [Equiv.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedBoxVolume
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# Exact Euclidean volume of the weighted boxes

The determinant separates into the unscaled basis determinant and the
exponential of its total weight. This gives the exact exponential volume
rate of the coordinate box, before passage to nilpotent exponential charts.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PolycyclicRecognition

variable {I : Type*} {n : ℕ}

def scaledColumnMatrix (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (r * w (b j)) * v (b j) i

/-- The coordinate weighted box is an actual linear image of a cube. -/
def weightedCoordinateBox (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (r L : ℝ) : Set (Fin n → ℝ) :=
  (Matrix.toLin' (scaledColumnMatrix v w b r)) ''
    Set.Icc (fun _ => -L) (fun _ => L)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBoxCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential boxes and the concrete weighted coordinate boxes

The sup-norm definition of a box agrees with the previously measured linear
image of a cube. This identifies group boxes with images of sets having the
exact determinant volume, without treating the two coordinate systems as an
extra hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped Matrix

variable {I L G : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- A single basis identifies its exponential box with the exponential
image of the standard coordinate cube. -/
theorem exponentialCoordinateBox_eq_cube_image {n : ℕ}
    (Exp : L → G) (b : Basis (Fin n) ℝ L) (R : ℝ) (hR : 0 ≤ R) :
    exponentialCoordinateBox Exp b R =
      (Exp ∘ b.equivFun.symm) '' Set.Icc (fun _ => -R) (fun _ => R) := by
  ext g
  rw [mem_exponentialCoordinateBox_iff Exp b R hR]
  constructor
  · rintro ⟨x, hx, hb⟩
    refine ⟨b.equivFun x, ?_, ?_⟩
    · exact ⟨fun i => (abs_le.mp (hb i)).1, fun i => (abs_le.mp (hb i)).2⟩
    · simpa only [Function.comp_apply, b.equivFun.symm_apply_apply] using hx
  · rintro ⟨t, ht, rfl⟩
    refine ⟨b.equivFun.symm t, rfl, fun i => ?_⟩
    have hi : |b.equivFun (b.equivFun.symm t) i| ≤ R := by
      rw [b.equivFun.apply_symm_apply]
      exact abs_le.mpr ⟨ht.1 i, ht.2 i⟩
    exact hi

/-- A basis sends its coordinate cube to exactly the vectors with bounded
coordinates, including dimension zero when `R` is nonnegative. -/
theorem basis_image_cube {n : ℕ} (b₀ b : Basis (Fin n) ℝ L)
    (R : ℝ) (hR : 0 ≤ R) :
    (Matrix.toLin' (b₀.toMatrix b)) '' Set.Icc (fun _ => -R) (fun _ => R) =
      b₀.equivFun '' {x : L | ‖b.equivFun x‖ ≤ R} := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨b.equivFun.symm t, ?_, ?_⟩
    · change ‖b.equivFun (b.equivFun.symm t)‖ ≤ R
      rw [b.equivFun.apply_symm_apply]
      apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro i
      exact Real.norm_eq_abs (t i) ▸ abs_le.mpr ⟨ht.1 i, ht.2 i⟩
    · change b₀.equivFun (b.equivFun.symm t) = (b₀.toMatrix b) *ᵥ t
      have h := b.toMatrix_mulVec_repr b₀ (b.equivFun.symm t)
      simpa only [← Basis.equivFun_apply, b.equivFun.apply_symm_apply] using h.symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨b.equivFun x, ?_, ?_⟩
    · constructor <;> intro i
      · exact (abs_le.mp ((Real.norm_eq_abs _ ▸ norm_le_pi_norm (b.equivFun x) i).trans hx)).1
      · exact (abs_le.mp ((Real.norm_eq_abs _ ▸ norm_le_pi_norm (b.equivFun x) i).trans hx)).2
    · exact b.toMatrix_mulVec_repr b₀ x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentHaarInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential-coordinate Haar measure

E. Le Donne, *Metric Lie Groups*, Graduate Texts in Mathematics 306,
Springer (2025), Theorem 9.4.7 (exponential coordinates) and Corollary 9.4.21.
https://doi.org/10.1007/978-3-031-98832-5_9

A global exponential chart identifies Haar measure on a simply connected
nilpotent Lie group with Lebesgue measure. The Euclidean determinant formula
then gives the volume of weighted boxes, including their scale factors.
-/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The part of the nilpotent exponential-coordinate theorem needed for Haar
volume. The hypotheses concern the actual tangent Lie algebra of the group. -/
def NilpotentExponentialHaarInput [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] : Prop :=
  (LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G) →
    ∃ Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G, IsGroupExponential Exp) ∧
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G) →
    (∃ c : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G, ∀ x, c x = Exp x) ∧
    ∀ (n : ℕ) (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)),
      (Measure.map (Exp ∘ b.equivFun.symm) volume).IsHaarMeasure

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGenerators
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The subalgebra generated by nonzero roots

The subalgebra generated by the nonzero root spaces is already an ideal.
Thus taking the ideal generated by them in the Cartan construction does not
enlarge the subgroup that must later be integrated.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
def cartanRootSubalgebra : LieSubalgebra ℝ L :=
  LieSubalgebra.lieSpan ℝ L
    {v | ∃ χ : Weight ℝ H L, χ.IsNonZero ∧ v ∈ rootSpace H χ}

set_option maxHeartbeats 1000000 in
theorem cartanRootSubalgebra_stable (h : H) {v : L}
    (hv : v ∈ cartanRootSubalgebra H) : ⁅(h : L), v⁆ ∈ cartanRootSubalgebra H := by
  induction hv using LieSubalgebra.lieSpan_induction with
  | mem v hv =>
    obtain ⟨χ, hχ, hv⟩ := hv
    apply LieSubalgebra.subset_lieSpan
    exact ⟨χ, hχ, (rootSpace H χ).lie_mem hv⟩
  | zero => simp only [lie_zero]; exact (cartanRootSubalgebra H).zero_mem
  | add x y _ _ hx hy =>
    rw [lie_add]
    exact (cartanRootSubalgebra H).add_mem hx hy
  | smul a x _ hx =>
    rw [lie_smul]
    exact (cartanRootSubalgebra H).smul_mem a hx
  | lie x y hx hy ihx ihy =>
    rw [leibniz_lie]
    exact (cartanRootSubalgebra H).add_mem
      ((cartanRootSubalgebra H).lie_mem ihx hy)
      ((cartanRootSubalgebra H).lie_mem hx ihy)

set_option maxHeartbeats 1000000 in
/-- Regard the generated subalgebra as a module for the Cartan subalgebra. -/
def cartanRootSubmodule : LieSubmodule ℝ H L where
  __ := (cartanRootSubalgebra H).toSubmodule
  lie_mem := by intro h v hv; exact cartanRootSubalgebra_stable H h hv

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialEmbedding
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closed embeddings from compatible global exponential charts

An injective map of finite-dimensional real Lie algebras is closed in linear
coordinates. Compatible global exponential charts transfer that property to
the integrated subgroup map. This supplies the properness required for
fixed-slice packing, without adding a closed-subgroup hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V U N G : Type*}
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
  [AddCommGroup U] [Module ℝ U] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [T2Space U]
  [TopologicalSpace N] [TopologicalSpace G]

/-- Global exponential charts turn an injective linear inclusion into a
closed topological embedding. No group-theoretic splitting is required. -/
theorem isClosedEmbedding_of_compatible_charts
    (cN : V ≃ₜ N) (cG : U ≃ₜ G) (j : V →ₗ[ℝ] U)
    (hj : Function.Injective j) (f : N → G)
    (hf : ∀ x, f (cN x) = cG (j x)) : Topology.IsClosedEmbedding f := by
  have he : f = cG ∘ j ∘ cN.symm := by
    funext n
    obtain ⟨x, rfl⟩ := cN.surjective n
    simpa only [Function.comp_apply, cN.symm_apply_apply] using hf x
  rw [he]
  exact cG.isClosedEmbedding.comp
    ((j.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hj)).comp cN.symm.isClosedEmbedding)

/-- The same conclusion with separately named intrinsic exponentials. -/
theorem isClosedEmbedding_of_exponential_compatibility
    (cN : V ≃ₜ N) (cG : U ≃ₜ G) (ExpN : V → N) (ExpG : U → G)
    (hN : ∀ x, cN x = ExpN x) (hG : ∀ x, cG x = ExpG x)
    (j : V →ₗ[ℝ] U) (hj : Function.Injective j) (f : N → G)
    (hf : ∀ x, f (ExpN x) = ExpG (j x)) : Topology.IsClosedEmbedding f := by
  apply isClosedEmbedding_of_compatible_charts cN cG j hj f
  intro x
  rw [hN, hG]
  exact hf x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieIntegrationInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published integration input for nilpotent subalgebras

J. M. Lee, *Introduction to Smooth Manifolds*, second edition, GTM 218,
Springer (2013), Theorem 20.19 (p.530) and Proposition 20.8(g) (p.520).
https://doi.org/10.1007/978-1-4419-9982-5
Theorem 20.19 integrates a Lie algebra homomorphism from a simply connected
Lie group; Proposition 20.8(g) supplies exponential compatibility. We retain
only nilpotent source groups, the smooth homomorphism, its prescribed
differential and its action on the intrinsic exponential. Closedness is proved separately from the
already available global charts, rather than added to the input.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN N EG G : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]

/-- Nilpotent-domain specialization of Lie's integration theorem and
naturality of the exponential. -/
def NilpotentLieIntegrationInput : Prop :=
  SimplyConnectedSpace N → LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, EN)) N) →
    ∀ (j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EG)) G)
      (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
      (ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G),
      IsGroupExponential ExpN → IsGroupExponential ExpG →
      ∃ ι : N →* G, ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι ∧
        (∀ x, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 x = j x) ∧
        ∀ x, ι (ExpN x) = ExpG (j x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MixedWordIdeal
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal used by the cone quotients -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- A bracket word is mixed when at least one of its letters is outside the
chosen cone. No property of that cone is needed for the ideal calculation. -/
def IsMixedWord (outside : I → Prop) : FreeMagma I → Prop
  | .of i => outside i
  | .mul u v => IsMixedWord outside u ∨ IsMixedWord outside v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightSpaceWordSpan
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Generalized weight spaces in a homogeneous word basis -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set
open scoped BigOperators

variable {H M J : Type*} [LieRing H] [LieAlgebra ℝ H] [LieRing.IsNilpotent H]
  [AddCommGroup M] [Module ℝ M] [LieRingModule H M] [LieModule ℝ H M]
  [Fintype J]

/-- In a basis of generalized weight vectors, any chosen collection of
weight spaces lies in the span of the basis vectors with those weights. -/
theorem genWeightSpace_le_span_basis_by_weight
    (b : Basis J ℝ M) (χ : J → Weight ℝ H M)
    (hb : ∀ j, b j ∈ genWeightSpace M (χ j))
    (selected : Weight ℝ H M → Prop) (α : Weight ℝ H M) (hα : selected α) :
    (genWeightSpace M α).toSubmodule ≤ Submodule.span ℝ (b '' {j | selected (χ j)}) := by
  classical
  let S : Weight ℝ H M → Submodule ℝ M := fun β => (genWeightSpace M β).toSubmodule
  have hsp : iSup S = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (χ j) (hb j)
  have hind : iSupIndep S :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' ℝ H M)
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsp
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) hds
  let A := fun β : Weight ℝ H M => if selected β then (S β).subtype else 0
  let D : M →ₗ[ℝ] M :=
    (DirectSum.toModule ℝ (Weight ℝ H M) M A).comp e.symm.toLinearMap
  have hD (β : Weight ℝ H M) (x : M) (hx : x ∈ S β) :
      D x = if selected β then x else 0 := by
    have he : e (DirectSum.lof ℝ (Weight ℝ H M) (fun β => S β) β ⟨x, hx⟩) = x :=
      DirectSum.coeLinearMap_lof S β ⟨x, hx⟩
    change (DirectSum.toModule ℝ (Weight ℝ H M) M A) (e.symm x) = _
    rw [← he, e.symm_apply_apply, DirectSum.toModule_lof]
    rw [he]
    by_cases hβ : selected β <;> simp only [A, hβ, ite_true, if_true, ite_false, if_false, LinearMap.zero_apply]
    rfl
  let P := Submodule.span ℝ (b '' {j | selected (χ j)})
  have hrange (y : M) : D y ∈ P := by
    rw [← b.sum_repr y, map_sum]
    apply Submodule.sum_mem
    intro j _
    rw [map_smul, hD (χ j) (b j) (hb j)]
    by_cases hj : selected (χ j)
    · rw [ite_eq_left hj]
      exact P.smul_mem _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · simp only [hj, ite_false, if_false, smul_zero]
      exact P.zero_mem
  intro x hx
  have he : D x = x := by rw [hD α x hx, ite_eq_left hα]
  exact he ▸ hrange x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Cartan automorphisms preserve the cone ideal -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

set_option maxHeartbeats 1000000 in
/-- In finite dimension an invariant subspace is also invariant under the
inverse automorphism. -/
theorem mem_submodule_equiv_iff_of_invariant
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (J : Submodule ℝ V) (e : V ≃ₗ[ℝ] V) (he : ∀ v ∈ J, e v ∈ J) (v : V) :
    e v ∈ J ↔ v ∈ J := by
  let f : J →ₗ[ℝ] J := (e.toLinearMap.comp J.subtype).codRestrict J (fun x => he x x.property)
  have hf : Function.Injective f := fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := (LinearMap.injective_iff_surjective).mp hf
  refine ⟨fun hv => ?_, he v⟩
  obtain ⟨x, hx⟩ := hsurj ⟨e v, hv⟩
  have hx' : e x = e v := congrArg Subtype.val hx
  exact e.injective hx' ▸ x.property

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Jacobian of actual Cartan conjugation

The nilpotent residual exponential has determinant one. The scalar weight
factors multiply to one by the already proved trace balance. Consequently
conjugation on the nilpotent Cartan ideal preserves coordinate volume.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

set_option maxHeartbeats 1000000 in
/-- A unipotent real endomorphism has determinant one, including in dimension
zero. This uses its actual characteristic polynomial. -/
theorem det_eq_one_of_sub_one_nilpotent
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (F : Module.End ℝ V) (hF : _root_.IsNilpotent (F - 1)) : F.det = 1 := by
  have h := congrArg (Polynomial.eval (1 : ℝ)) hF.neg.charpoly_eq_X_pow_finrank
  rw [LinearMap.eval_charpoly] at h
  have he : (algebraMap ℝ (Module.End ℝ V) 1 - -(F - 1)) = F := by
    simp only [map_one, sub_neg_eq_add]
    abel
  rw [he] at h
  simpa using h

set_option maxHeartbeats 1000000 in
/-- Finite nilpotent exponential has unit determinant. -/
theorem det_nilpotent_exp
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [Module ℚ V] [IsScalarTower ℚ ℝ V]
    (A : Module.End ℝ V) (hA : _root_.IsNilpotent A) :
    LinearMap.det (_root_.IsNilpotent.exp A) = 1 :=
  det_eq_one_of_sub_one_nilpotent _ hA.isNilpotent_exp_sub_one

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentHaarAutomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar preservation for the integrated automorphisms

A determinant-one Lie automorphism preserves Lebesgue measure in exponential
coordinates. The global chart transfers this identity to actual group Haar
measure; no invariant-measure premise for the automorphism is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  {n : ℕ} (b : Basis (Fin n) ℝ L)

omit [FiniteDimensional ℝ L] [T2Space G] in
include hchart in
/-- In exponential coordinates, the integrated automorphism preserves the
same measure exactly when its linear determinant has absolute value one.
Here the positive determinant-one case suffices for Cartan conjugation. -/
theorem exponentialConjugate_measurePreserving
    (F : L ≃ₗ⁅ℝ⁆ L) (hdet : LinearMap.det F.toLinearEquiv.toLinearMap = 1) :
    MeasurePreserving (exponentialConjugate e Exp hbij F)
      (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume)
      (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume) := by
  let A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (b.equivFun.symm.trans F.toLinearEquiv).trans b.equivFun
  let f : (Fin n → ℝ) ≃ₜ G :=
    (b.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : (f : (Fin n → ℝ) → G) = (Exp ∘ e) ∘ b.equivFun.symm := by
    funext t
    exact hchart _
  have hAdet : LinearMap.det A.toLinearMap = 1 := by
    have hd := congrArg Units.val (LinearEquiv.det_conj F.toLinearEquiv b.equivFun)
    have hd' : LinearMap.det A.toLinearMap = LinearMap.det F.toLinearEquiv.toLinearMap := by
      simpa only [LinearEquiv.coe_det] using hd
    exact hd'.trans hdet
  have hA : MeasurePreserving A volume volume := by
    refine ⟨A.toContinuousLinearEquiv.continuous.measurable, ?_⟩
    change Measure.map A.toLinearMap volume = volume
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [hAdet]; norm_num),
      hAdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul]
  have hsem : Function.Semiconj f A (exponentialConjugate e Exp hbij F) := by
    intro t
    rw [hf]
    change Exp (e (b.equivFun.symm (A t))) = _
    simp only [A, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact (exponentialConjugate_apply_exp e Exp hbij F (b.equivFun.symm t)).symm
  have heq : (exponentialConjugate e Exp hbij F : G → G) =
      f ∘ A ∘ f.symm := by
    funext g
    obtain ⟨t, rfl⟩ := f.surjective g
    simpa only [Function.comp_apply, f.symm_apply_apply] using (hsem t).symm
  have hmeas : Measurable (exponentialConjugate e Exp hbij F) := by
    rw [heq]
    exact f.continuous.measurable.comp
      (A.toContinuousLinearEquiv.continuous.measurable.comp f.symm.continuous.measurable)
  have hm := f.measurable.measurePreserving volume
  have hh := hm.of_semiconj hA hsem hmeas
  rwa [hf] at hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeQuotientAutomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient Lie automorphism and its exponential Haar multiplier -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold

/-- An automorphism preserving an ideal in both directions induces an
actual Lie equivalence on the quotient. -/
def lieQuotientAutomorphism
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (I : LieIdeal ℝ L) (F : L ≃ₗ⁅ℝ⁆ L) (hF : ∀ x, F x ∈ I ↔ x ∈ I) :
    (L ⧸ I) ≃ₗ⁅ℝ⁆ (L ⧸ I) := by
  let q := I.toSubmodule.mkQ
  let f := I.toSubmodule.mapQ I.toSubmodule F.toLinearEquiv.toLinearMap
    (fun x hx => (hF x).mpr hx)
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨v, rfl⟩ := I.toSubmodule.mkQ_surjective x
    obtain ⟨w, rfl⟩ := I.toSubmodule.mkQ_surjective y
    have hz : q (F (v - w)) = 0 := by
      change q (F v) = q (F w) at hxy
      simpa only [map_sub, sub_eq_zero] using hxy
    have hvw : v - w ∈ I := (hF (v - w)).mp
      ((Submodule.Quotient.mk_eq_zero I.toSubmodule).mp hz)
    apply sub_eq_zero.mp
    change q v - q w = 0
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr hvw
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨v, rfl⟩ := I.toSubmodule.mkQ_surjective x
    exact ⟨q (F.symm v), congrArg q (F.apply_symm_apply v)⟩
  refine { LinearEquiv.ofBijective f ⟨hinj, hsurj⟩ with map_lie' := ?_ }
  intro x y
  obtain ⟨v, rfl⟩ := I.toSubmodule.mkQ_surjective x
  obtain ⟨w, rfl⟩ := I.toSubmodule.mkQ_surjective y
  change q (F ⁅v, w⁆) = q ⁅F v, F w⁆
  rw [F.map_lie]

@[simp] theorem lieQuotientAutomorphism_mk
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (I : LieIdeal ℝ L) (F : L ≃ₗ⁅ℝ⁆ L) (hF : ∀ x, F x ∈ I ↔ x ∈ I) (x : L) :
    lieQuotientAutomorphism I F hF (I.toSubmodule.mkQ x) = I.toSubmodule.mkQ (F x) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateOrbitRepresentation
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linearizing a group through its translated coordinate functions

Right translates of separating coordinates span a faithful representation.
A uniform finite-dimensional space containing those translates makes the
representation finite dimensional; polynomial multiplication will supply it.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G I : Type*} [Group G] (q : I → G → ℝ)

def coordinateOrbitSpan : Submodule ℝ (G → ℝ) :=
  Submodule.span ℝ (Set.range (fun p : G × I => fun x => q p.2 (x * p.1)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FilteredDeterminant
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Determinant of an endomorphism that raises a finite filtration -/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem nilpotent_of_raises_filtration (F : ℕ → Submodule ℝ V)
    (hF0 : F 0 = ⊤) {c : ℕ} (hFc : F c = ⊥)
    (N : V →ₗ[ℝ] V) (hN : ∀ k v, v ∈ F k → N v ∈ F (k + 1)) : IsNilpotent N := by
  have hp : ∀ k v, (N ^ k) v ∈ F k := by
    intro k
    induction k with
    | zero => intro v; simp [hF0]
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply]
      exact hN k _ (ih v)
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  have hv := hp c v
  simpa only [hFc, Submodule.mem_bot, LinearMap.zero_apply] using hv

theorem det_one_add_of_nilpotent [FiniteDimensional ℝ V]
    (N : V →ₗ[ℝ] V) (hN : IsNilpotent N) : LinearMap.det (1 + N) = 1 := by
  have hneg : IsNilpotent (-N) := hN.neg
  have he := LinearMap.eval_charpoly (-N) (1 : ℝ)
  rw [hneg.charpoly_eq_X_pow_finrank] at he
  simpa using he.symm

theorem det_eq_one_of_raises_filtration [FiniteDimensional ℝ V]
    (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤) {c : ℕ} (hFc : F c = ⊥)
    (A : V →ₗ[ℝ] V) (hA : ∀ k v, v ∈ F k → (A - 1) v ∈ F (k + 1)) :
    LinearMap.det A = 1 := by
  have hn := nilpotent_of_raises_filtration F hF0 hFc (A - 1) hA
  have hd := det_one_add_of_nilpotent (A - 1) hn
  simpa only [add_sub_cancel] using hd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieWordDifferential
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentials of bracket words and the lower central series

Changing the basepoint in the differential of a Lie polynomial changes its
linear part only by a map that raises the lower central series. This is the
algebraic part of the Jacobian computation for nilpotent exponential coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped BigOperators

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

def rightBracketLinear (y : L) : L →ₗ[ℝ] L where
  toFun x := ⁅x, y⁆
  map_add' x z := add_lie x z y
  map_smul' c x := smul_lie c x y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RealNormedLieAlgebra
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible normed and Lie structures

Bundling the shared additive and scalar structures avoids two unrelated
copies of those structures in differentiating a Lie polynomial.
-/

namespace PolycyclicRecognition

class RealNormedLieAlgebra (L : Type*) extends NormedAddCommGroup L, LieRing L,
    NormedSpace ℝ L, LieAlgebra ℝ L

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieWordDerivative
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual derivatives of finite Lie polynomials

The finite-dimensional bracket is continuous in the given norm. The resulting
differential is the algebraic word differential.
-/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

/-- Continuous realization of the bracket in the given finite-dimensional norm. -/
def normedLieBracket : L →L[ℝ] L →L[ℝ] L :=
  (show L →ₗ[ℝ] L →L[ℝ] L from
    { toFun := fun x => Module.End.toContinuousLinearMap (𝕜 := ℝ) L (LieModule.toEnd ℝ L L x)
      map_add' := by intro x y; ext z; exact add_lie x y z
      map_smul' := by intro c x; ext z; exact smul_lie c x z }).toContinuousLinearMap

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinJacobian
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit Jacobian of left translation in nilpotent BCH coordinates -/

noncomputable section
namespace PolycyclicRecognition

open LieModule

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

def rightVariableDifferential : Fin 2 → L →ₗ[ℝ] L := ![0, 1]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of the intrinsic exponential

The exponential compatibility clause of Lie integration follows from the
chain rule and uniqueness of invariant integral curves. No integration
theorem or representation theorem is used here.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

theorem mfderiv_hom_invariant (φ : G →* H)
    (hφ : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (g : G) :
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ g) (mulInvariantVectorField v g) =
      mulInvariantVectorField ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v) (φ g) := by
  have hleft : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) 1 :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun x : G => g * x)).mdifferentiableAt (by simp)
  have hright : MDifferentiableAt (𝓘(ℝ, F)) (𝓘(ℝ, F))
      (fun y : H => φ g * y) (φ 1) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, F)) (a := φ g) :
      ContMDiff (𝓘(ℝ, F)) (𝓘(ℝ, F)) ⊤ (fun y : H => φ g * y)).mdifferentiableAt (by simp)
  have h₁ := mfderiv_comp (I' := 𝓘(ℝ, E)) 1 (hφ (g * 1)) hleft
  have h₂ := mfderiv_comp (I' := 𝓘(ℝ, F)) 1 hright (hφ 1)
  have heq : φ ∘ (fun x : G => g * x) = (fun y : H => φ g * y) ∘ φ := by
    funext x
    exact φ.map_mul g x
  rw [heq] at h₁
  have hmaps : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ (g * 1) : E →L[ℝ] F) =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ g : E →L[ℝ] F) := by
    congr 1
    exact mul_one g
  have hmapt : (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (fun y : H => φ g * y) (φ 1) : F →L[ℝ] F) =
      (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (fun y : H => φ g * y) 1 : F →L[ℝ] F) := by
    congr 1
    exact φ.map_one
  have h := congrArg (fun L : E →L[ℝ] F => L v) (h₁.symm.trans h₂)
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ (g * 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) 1) v) =
    (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (fun y : H => φ g * y) (φ 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v) at h
  rw [hmaps, hmapt] at h
  exact h

theorem invariant_integralCurve_map (φ : G →* H)
    (hφ : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ)
    {v : GroupLieAlgebra (𝓘(ℝ, E)) G} {γ : ℝ → G}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, E)) γ (mulInvariantVectorField v)) :
    IsMIntegralCurve (I := 𝓘(ℝ, F)) (φ ∘ γ)
      (mulInvariantVectorField ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v)) := by
  intro t
  apply ((hφ (γ t)).hasMFDerivAt.comp t (hγ t)).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  let s : ℝ := r
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ (γ t))
      (s • mulInvariantVectorField v (γ t)) =
    s • mulInvariantVectorField ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v) (φ (γ t))
  rw [map_smul, mfderiv_hom_invariant φ hφ]

/-- Every differentiable homomorphism commutes with the intrinsic exponential. -/
theorem IsGroupExponential.map_of_mdifferentiable [T2Space H]
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hG : IsGroupExponential ExpG) (hH : IsGroupExponential ExpH)
    (φ : G →* H) (hφ : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    φ (ExpG v) = ExpH ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v) := by
  let w : GroupLieAlgebra (𝓘(ℝ, F)) H := (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v
  have hmap : IsMIntegralCurve (I := 𝓘(ℝ, F))
      (φ ∘ fun t : ℝ => ExpG (t • v)) (mulInvariantVectorField w) :=
    invariant_integralCurve_map φ hφ (hG.isMIntegralCurve v)
  have heq := invariant_integralCurve_unique hmap (hH.isMIntegralCurve w)
    (by simp only [Function.comp_apply, zero_smul, hG.map_zero, hH.map_zero, map_one])
  have ht := congrFun heq 1
  change φ (ExpG (1 • v)) = ExpH (1 • w) at ht
  simpa only [one_smul] using ht

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieConjugationDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual differential of conjugation

This constructs the adjoint action on the tangent space from the manifold
derivative and proves its compatibility with the intrinsic exponential.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- Differential at the identity, with the codomain identified using the
homomorphism's identity law. -/
def identityDifferential (φ : G →* G) :
    GroupLieAlgebra (𝓘(ℝ, E)) G →L[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G :=
  mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ 1

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem identityDifferential_comp (φ ψ : G →* G)
    (hφ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ 1)
    (hψ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ψ 1) :
    identityDifferential (E := E) (φ.comp ψ) =
      (identityDifferential (E := E) φ).comp (identityDifferential (E := E) ψ) := by
  have hφ' : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (ψ 1) := by
    rw [map_one]
    exact hφ
  have hc := mfderiv_comp (I' := 𝓘(ℝ, E)) 1 hφ' hψ
  have hp : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (ψ 1) : E →L[ℝ] E) =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ 1 : E →L[ℝ] E) := by
    congr 1
    exact ψ.map_one
  rw [hp] at hc
  exact hc

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
@[simp] theorem identityDifferential_id :
    identityDifferential (E := E) (MonoidHom.id G) = ContinuousLinearMap.id ℝ _ := by
  change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) id 1 = _
  rw [mfderiv_id]

theorem contMDiff_conjugation (g : G) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ ((MulAut.conj g).toMonoidHom) := by
  have hl : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun x : G => g * x) :=
    contMDiff_mul_left
  have hr : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun x : G => x * g⁻¹) :=
    contMDiff_mul_right
  exact hr.comp hl

/-- The adjoint action as a monoid homomorphism into continuous linear
endomorphisms of the actual tangent Lie algebra. -/
def conjugationDifferentialHom :
    G →* (GroupLieAlgebra (𝓘(ℝ, E)) G →L[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G) where
  toFun g := identityDifferential ((MulAut.conj g).toMonoidHom)
  map_one' := by
    have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [h, identityDifferential_id]
    rfl
  map_mul' g h := by
    have heq : (MulAut.conj (g * h)).toMonoidHom =
        ((MulAut.conj g).toMonoidHom).comp ((MulAut.conj h).toMonoidHom) := by
      ext x
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MonoidHom.comp_apply, MulAut.conj_apply, mul_inv_rev, mul_assoc]
    rw [heq, identityDifferential_comp _ _
      ((contMDiff_conjugation g).mdifferentiableAt (by simp))
      ((contMDiff_conjugation h).mdifferentiableAt (by simp))]
    rfl

theorem conjugation_exponential [T2Space G]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (g : G) (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    g * Exp v * g⁻¹ = Exp (conjugationDifferentialHom g v) :=
  hExp.map_of_mdifferentiable hExp (MulAut.conj g).toMonoidHom
    ((contMDiff_conjugation g).mdifferentiable (by simp)) v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ParametricLieWords
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lie words as functions of their structure constants

The bilinear bracket itself varies in a finite-dimensional vector space.
Word evaluation is smooth jointly in that bracket and the input vectors, so
word identities and normalization equations persist under limits.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Evaluate a bracket word with a specified continuous bilinear bracket. -/
def evalBilinearWord (B : V →L[ℝ] V →L[ℝ] V) (X : I → V) : FreeMagma I → V
  | .of i => X i
  | .mul a b => B (evalBilinearWord B X a) (evalBilinearWord B X b)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {n : ℕ∞}

/-- Smooth dependence of a finite word on both bracket and generator data. -/
theorem contDiff_evalBilinearWord (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → I → V) (hB : ContDiff ℝ n B)
    (hX : ∀ i, ContDiff ℝ n (fun p => X p i)) (w : FreeMagma I) :
    ContDiff ℝ n (fun p => evalBilinearWord (B p) (X p) w) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul a b ha hb => exact (hB.clm_apply ha).clm_apply hb

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoordinateLieBrackets
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Lie law in a chosen basis

Transport the original bracket to Euclidean coordinates, retaining its exact
word identities. A bound on basis structure constants gives a bound in the
finite-dimensional parameter space used for normalized-law compactness.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
  (b : Basis (Fin n) ℝ L)

/-- Coordinate transport of the bracket, initially as a bilinear map. -/
def basisBracketLinear : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x :=
    { toFun y := b.equivFun ⁅b.equivFun.symm x, b.equivFun.symm y⁆
      map_add' := by intro y z; simp only [map_add, lie_add]
      map_smul' := by intro c y; simp only [map_smul, lie_smul, RingHom.id_apply] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change b.equivFun ⁅b.equivFun.symm (x + y), b.equivFun.symm z⁆ =
      b.equivFun ⁅b.equivFun.symm x, b.equivFun.symm z⁆ +
        b.equivFun ⁅b.equivFun.symm y, b.equivFun.symm z⁆
    rw [map_add, add_lie, map_add]
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    change b.equivFun ⁅b.equivFun.symm (c • x), b.equivFun.symm y⁆ =
      c • b.equivFun ⁅b.equivFun.symm x, b.equivFun.symm y⁆
    rw [map_smul, smul_lie, map_smul]

/-- The same coordinate bracket in the normed space of continuous bilinear maps. -/
def basisBracket : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (((LinearMap.toContinuousLinearMap :
    ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≃ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))).toLinearMap).comp
      (basisBracketLinear b)).toContinuousLinearMap

@[simp] theorem basisBracket_apply (x y : Fin n → ℝ) :
    basisBracket b x y = b.equivFun ⁅b.equivFun.symm x, b.equivFun.symm y⁆ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialGroupLaws
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial group laws in a fixed coordinate space

The binary Dynkin coefficients are fixed once in the original nilpotent
group. Changing its basis changes only the bracket. The group identities and
the straight-line one-parameter identities are closed conditions on this
finite-dimensional bracket parameter.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The finite Dynkin expression evaluated with a variable bilinear law. -/
def bilinearDynkinPolynomial {c n : ℕ} (a : DynkinCoefficients c n)
    (B : V →L[ℝ] V →L[ℝ] V) (X : Fin n → V) : V :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    a d w • evalBilinearWord B X (rightNestedWord d.val w)

/-- The binary multiplication polynomial, with fixed coefficients. -/
def dynkinProduct {c : ℕ} (a : DynkinCoefficients c 2)
    (B : V →L[ℝ] V →L[ℝ] V) (x y : V) : V :=
  bilinearDynkinPolynomial a B ![x, y]

theorem contDiff_bilinearDynkinPolynomial {c n : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c n) (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → Fin n → V) (hB : ContDiff ℝ k B)
    (hX : ∀ i, ContDiff ℝ k (fun p => X p i)) :
    ContDiff ℝ k (fun p => bilinearDynkinPolynomial a (B p) (X p)) := by
  apply ContDiff.sum
  intro d _
  apply ContDiff.sum
  intro w _
  exact (contDiff_evalBilinearWord B X hB hX _).const_smul _

@[fun_prop] theorem contDiff_dynkinProduct {c : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (x y : P → V) (hB : ContDiff ℝ k B)
    (hx : ContDiff ℝ k x) (hy : ContDiff ℝ k y) :
    ContDiff ℝ k (fun p => dynkinProduct a (B p) (x p) (y p)) := by
  apply contDiff_bilinearDynkinPolynomial a B (fun p => ![x p, y p]) hB
  intro i
  fin_cases i
  · exact hx
  · exact hy

@[fun_prop] theorem continuous_dynkinProduct {c : ℕ}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (x y : P → V) (hB : Continuous B) (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun p => dynkinProduct a (B p) (x p) (y p)) := by
  exact (contDiff_dynkinProduct (k := 0) a B x y
    (contDiff_zero.mpr hB) (contDiff_zero.mpr hx) (contDiff_zero.mpr hy)).continuous

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinLocalParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local BCH parameters without an exponential bijection

The basis-input BCH polynomial is smooth and has derivative the identity
at zero. Its derivative follows from the one-coordinate restrictions,
already determined by the actual exponential curves.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped ContDiff

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {c n : ℕ}

def basisDynkinParameter (coeff : DynkinCoefficients c n) (b : Basis (Fin n) ℝ L)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  bilinearDynkinPolynomial coeff (basisBracket b) (fun i => b.equivFun (x i • b i))

open scoped Manifold

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FilteredBijection
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverting a map whose error raises a finite filtration

The fixed-point correction terminates after the filtration length. This
gives a concrete inverse for triangular polynomial translations.
-/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def filteredNewton (f : V → V) (y : V) : ℕ → V
  | 0 => 0
  | n + 1 => filteredNewton f y n + (y - f (filteredNewton f y n))

theorem filteredNewton_error_mem (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤)
    (f : V → V)
    (hraise : ∀ k x y, x - y ∈ F k → (f x - f y) - (x - y) ∈ F (k + 1))
    (y : V) (n : ℕ) : y - f (filteredNewton f y n) ∈ F n := by
  induction n with
  | zero => rw [hF0]; exact Submodule.mem_top
  | succ n ih =>
    have hstep : filteredNewton f y (n + 1) - filteredNewton f y n ∈ F n := by
      simpa only [filteredNewton, add_sub_cancel_left] using ih
    have hh := hraise n (filteredNewton f y (n + 1)) (filteredNewton f y n) hstep
    have heq : y - f (filteredNewton f y (n + 1)) =
        -((f (filteredNewton f y (n + 1)) - f (filteredNewton f y n)) -
          (filteredNewton f y (n + 1) - filteredNewton f y n)) := by
      rw [filteredNewton]
      abel
    rw [heq]
    exact (F (n + 1)).neg_mem hh

theorem filteredNewton_right_inverse (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤)
    {c : ℕ} (hFc : F c = ⊥) (f : V → V)
    (hraise : ∀ k x y, x - y ∈ F k → (f x - f y) - (x - y) ∈ F (k + 1))
    (y : V) : f (filteredNewton f y c) = y := by
  have hh := filteredNewton_error_mem F hF0 f hraise y c
  rw [hFc, Submodule.mem_bot] at hh
  exact (sub_eq_zero.mp hh).symm

theorem injective_of_raises_difference_filtration
    (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤) {c : ℕ} (hFc : F c = ⊥)
    (f : V → V)
    (hraise : ∀ k x y, x - y ∈ F k → (f x - f y) - (x - y) ∈ F (k + 1)) :
    Function.Injective f := by
  intro x y hxy
  have hm : ∀ k, x - y ∈ F k := by
    intro k
    induction k with
    | zero => rw [hF0]; exact Submodule.mem_top
    | succ k ih =>
      have hh := hraise k x y ih
      rw [hxy, sub_self, zero_sub] at hh
      exact (F (k + 1)).neg_mem_iff.mp hh
  have hh := hm c
  rw [hFc, Submodule.mem_bot] at hh
  exact sub_eq_zero.mp hh

variable [TopologicalSpace V] [IsTopologicalAddGroup V]

omit [Module ℝ V] in
theorem continuous_filteredNewton (f : V → V) (hf : Continuous f) (n : ℕ) :
    Continuous (fun y => filteredNewton f y n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ih.add (continuous_id.sub (hf.comp ih))

omit [Module ℝ V] in
theorem continuous_parametric_filteredNewton (f : V → V → V)
    (hf : Continuous (fun p : V × V => f p.1 p.2)) (n : ℕ) :
    Continuous (fun p : V × V => filteredNewton (f p.1) p.2 n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ih.add (continuous_snd.sub (hf.comp (continuous_fst.prodMk ih)))

def homeomorphOfRaisesDifferenceFiltration
    (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤) {c : ℕ} (hFc : F c = ⊥)
    (f : V → V) (hf : Continuous f)
    (hraise : ∀ k x y, x - y ∈ F k → (f x - f y) - (x - y) ∈ F (k + 1)) : V ≃ₜ V where
  toFun := f
  invFun y := filteredNewton f y c
  left_inv x := (injective_of_raises_difference_filtration F hF0 hFc f hraise)
    (filteredNewton_right_inverse F hF0 hFc f hraise (f x))
  right_inv := filteredNewton_right_inverse F hF0 hFc f hraise
  continuous_toFun := hf
  continuous_invFun := continuous_filteredNewton f hf c

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RightTranslationInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right translation of an invariant vector field

The change in a left-invariant field under right multiplication is the
actual differential of conjugation. No representation is used.
-/

noncomputable section
namespace PolycyclicRecognition

open Function
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem mfderiv_mul_right_invariant (a g : G) (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) g
        (mulInvariantVectorField v g) =
      mulInvariantVectorField (conjugationDifferentialHom a⁻¹ v) (g * a) := by
  have hL : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * h) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ⊤)).mdifferentiable (by simp)
  have hR : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) :=
    (contMDiff_mul_right (I := 𝓘(ℝ, E)) (n := ⊤)).mdifferentiable (by simp)
  have hL' : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => (g * a) * h) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ⊤)).mdifferentiable (by simp)
  have hC := (contMDiff_conjugation (E := E) a⁻¹).mdifferentiable (by simp)
  have heq : (fun h : G => h * a) ∘ (fun h : G => g * h) =
      (fun h : G => (g * a) * h) ∘ (MulAut.conj a⁻¹).toMonoidHom := by
    ext h
    simp only [comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv]
    group
  have h₁ := mfderiv_comp (I' := 𝓘(ℝ, E)) (1 : G) (hR (g * 1)) (hL 1)
  have h₂ := mfderiv_comp (I' := 𝓘(ℝ, E)) (1 : G)
    (hL' ((MulAut.conj a⁻¹).toMonoidHom 1)) (hC 1)
  rw [heq] at h₁
  have hh := congrArg (fun D : E →L[ℝ] E => D v) (h₁.symm.trans h₂)
  have hbase : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) (g * 1) : E →L[ℝ] E) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) g := by
    congr 1
    exact mul_one g
  have htarget : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => (g * a) * h)
      ((MulAut.conj a⁻¹).toMonoidHom 1) : E →L[ℝ] E) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => (g * a) * h) 1 := by
    congr 1
    exact map_one _
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) (g * 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * h) 1) v) =
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => (g * a) * h)
      ((MulAut.conj a⁻¹).toMonoidHom 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (MulAut.conj a⁻¹).toMonoidHom 1) v) at hh
  rw [hbase, htarget] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ManifoldRelatedBracket
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Brackets of related vector fields on manifolds

Both source and target charts are local. This extends the vector-space
calculation only as far as needed to differentiate Lie-group homomorphisms.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function Bundle VectorField
open scoped Manifold ContDiff Topology

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ, F)) ∞ N]

theorem chartVectorField_apply_chart
    (x₀ : M) (V : (x : M) → TangentSpace (𝓘(ℝ, E)) x)
    {x : M} (hx : x ∈ (extChartAt (𝓘(ℝ, E)) x₀).source) :
    chartVectorField x₀ V (extChartAt (𝓘(ℝ, E)) x₀ x) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀) x (V x) := by
  have h₁ := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (I := 𝓘(ℝ, E)) hx
  have h₂ := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓘(ℝ, E)) hx
  have hrange : range (𝓘(ℝ, E)) = (univ : Set E) := by ext z; simp
  rw [hrange, mfderivWithin_univ] at h₁ h₂
  have hinv := ContinuousLinearMap.inverse_eq h₂ h₁
  unfold chartVectorField mpullback
  exact (congrArg (fun D : E →L[ℝ] E =>
    D (V ((extChartAt (𝓘(ℝ, E)) x₀).symm (extChartAt (𝓘(ℝ, E)) x₀ x)))) hinv).trans
      (congrArg (fun z : M =>
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x₀) x) (V z : E))
        ((extChartAt (𝓘(ℝ, E)) x₀).left_inv hx))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FixedChartTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right translations inside a fixed identity chart -/

noncomputable section
namespace PolycyclicRecognition

open Set Function
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem fderiv_fixed_chart_map {f : G → G}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ f)
    (g₀ : G) {z : E} (hz : z ∈ (extChartAt (𝓘(ℝ, E)) g₀).target)
    (hfz : f ((extChartAt (𝓘(ℝ, E)) g₀).symm z) ∈
      (extChartAt (𝓘(ℝ, E)) g₀).source) :
    fderiv ℝ (extChartAt (𝓘(ℝ, E)) g₀ ∘ f ∘ (extChartAt (𝓘(ℝ, E)) g₀).symm) z =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) g₀)
        (f ((extChartAt (𝓘(ℝ, E)) g₀).symm z))).comp
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f ((extChartAt (𝓘(ℝ, E)) g₀).symm z)).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) g₀).symm z)) := by
  have hi : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (extChartAt (𝓘(ℝ, E)) g₀).symm z := by
    simpa only [mfld_simps, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hz
  have ho : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (extChartAt (𝓘(ℝ, E)) g₀) (f ((extChartAt (𝓘(ℝ, E)) g₀).symm z)) :=
    mdifferentiableAt_extChartAt (by simpa only [mfld_simps] using hfz)
  apply HasFDerivAt.fderiv
  apply (hasMFDerivAt_iff_hasFDerivAt).mp
  exact ho.hasMFDerivAt.comp z
    (((hf _).mdifferentiableAt (by simp)).hasMFDerivAt.comp z hi.hasMFDerivAt)

theorem chart_rightTranslation_related (a : G) (v : E)
    {z : E} (hz : z ∈ (extChartAt (𝓘(ℝ, E)) (1 : G)).target)
    (ha : (extChartAt (𝓘(ℝ, E)) (1 : G)).symm z * a ∈
      (extChartAt (𝓘(ℝ, E)) (1 : G)).source) :
    fderiv ℝ (fun y => extChartAt (𝓘(ℝ, E)) (1 : G)
      ((extChartAt (𝓘(ℝ, E)) (1 : G)).symm y * a)) z
        (chartInvariantFrame (1 : G) z (conjugationDifferentialHom (E := E) a v)) =
      chartInvariantFrame (1 : G)
        (extChartAt (𝓘(ℝ, E)) (1 : G) ((extChartAt (𝓘(ℝ, E)) (1 : G)).symm z * a)) v := by
  let φ := extChartAt (𝓘(ℝ, E)) (1 : G)
  have hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun h : G => h * a) :=
    contMDiff_mul_right
  have hd := fderiv_fixed_chart_map hf (1 : G) hz ha
  have hD : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm z).IsInvertible := by
    simpa only [φ, mfld_simps, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) hz
  change fderiv ℝ (φ ∘ (fun h : G => h * a) ∘ φ.symm) z _ = _
  rw [hd]
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm z * a))
    ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) (φ.symm z))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm z)
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm z).inverse
          (mulInvariantVectorField (conjugationDifferentialHom (E := E) a v) (φ.symm z))))) = _
  rw [hD.self_apply_inverse, mfderiv_mul_right_invariant]
  have hinv : conjugationDifferentialHom (E := E) a⁻¹ (conjugationDifferentialHom (E := E) a v) = v := by
    change (conjugationDifferentialHom (E := E) a⁻¹ * conjugationDifferentialHom (E := E) a) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hinv, chartInvariantFrame_apply]
  exact (chartVectorField_apply_chart (1 : G) (mulInvariantVectorField v) ha).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorOrbit
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spanning by conjugated generator directions

Products of adjoint exponentials applied to a Lie-generating family span the
whole algebra. This proves the linear nondegeneracy needed to construct a
submersive generator product scheme; it does not assume controllability or a
volume estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance generatorOrbitNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance generatorOrbitNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

/-- The adjoint operator, with its finite-dimensional continuous structure. -/
def continuousAd (x : L) : L →L[ℝ] L := Module.End.toContinuousLinearMap (𝕜 := ℝ) L (LieModule.toEnd ℝ L L x)

@[simp] theorem continuousAd_apply (x y : L) : continuousAd x y = ⁅x, y⁆ := rfl

/-- A finite product of actual operator exponentials of generator adjoints. -/
def generatorAdjointWord (X : I → L) (w : List (I × ℝ)) : L →L[ℝ] L :=
  (w.map (fun p => NormedSpace.exp (p.2 • continuousAd (X p.1)))).prod

@[simp] theorem generatorAdjointWord_nil (X : I → L) :
    generatorAdjointWord X [] = 1 := rfl

@[simp] theorem generatorAdjointWord_cons (X : I → L) (i : I) (t : ℝ)
    (w : List (I × ℝ)) :
    generatorAdjointWord X ((i, t) :: w) =
      NormedSpace.exp (t • continuousAd (X i)) * generatorAdjointWord X w := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorConjugation
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group words realizing a basis of generator conjugates

A faithful exponential-compatible representation turns the operator words
from `GeneratorOrbit` into conjugation by finite words in generator
one-parameter subgroups. No generation or submersion assertion is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance generatorConjugationNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance generatorConjugationNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A Lie representation intertwines the full adjoint exponential with
ordinary algebra conjugation. -/
theorem represented_exp_continuousAd (j : L →ₗ⁅ℝ⁆ A) (x v : L) (t : ℝ) :
    j (NormedSpace.exp (t • continuousAd x) v) =
      NormedSpace.exp (t • j x) * j v * NormedSpace.exp (-(t • j x)) := by
  let f : L →L[ℝ] A := j.toLinearMap.toContinuousLinearMap
  have h := exp_intertwine_apply f (t • continuousAd x) (t • adjointOperator (j x))
    (by intro y; simp only [smul_apply, map_smul, continuousAd_apply,
      adjointOperator_apply]; exact congrArg (t • ·) (j.map_lie x y)) v
  rw [exp_smul_adjointOperator_apply] at h
  exact h

variable {G : Type*} [Group G] (X : I → L) (Exp : L → G)

variable (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
  (hExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x))

include hρ hExp in
/-- Conjugation along one generator is the exponential of its actual adjoint. -/
theorem exp_ad_eq_group_conjugation (x v : L) (t : ℝ) :
    Exp (NormedSpace.exp (t • continuousAd x) v) =
      Exp (t • x) * Exp v * (Exp (t • x))⁻¹ := by
  apply hρ
  rw [map_mul, map_mul, map_inv, hExp, hExp, hExp, map_smul,
    represented_exp_continuousAd]
  exact algebraExpUnit_conj (algebraExpUnit (t • j x)) (j v)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentCoordinatesInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing exponential existence from the nilpotent coordinate input

The global intrinsic exponential identifies a simply connected nilpotent
Lie group with its Lie algebra and transports coordinate volume to Haar measure.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- Only the global topological chart, with no measure compatibility. -/
def NilpotentGlobalExponentialChartInput [T2Space G] [SimplyConnectedSpace G] : Prop :=
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G) →
    ∃ c : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G, ∀ x, c x = Exp x

def NilpotentExponentialCoordinatesInput [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] : Prop :=
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G) →
    (∃ c : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G, ∀ x, c x = Exp x) ∧
    ∀ (n : ℕ) (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)),
      (Measure.map (Exp ∘ b.equivFun.symm) volume).IsHaarMeasure

variable {E G} [T2Space G] [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

theorem NilpotentExponentialCoordinatesInput.toHaar
    (h : NilpotentExponentialCoordinatesInput E G) : NilpotentExponentialHaarInput E G :=
  ⟨fun _ => exists_groupExponential, h⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedFreeRepresentation
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized free cover of an integral representation

The basis omits zero, and a coefficient morphism sends a basis element to zero
whenever its image is zero. Thus the free-cover functor preserves zero maps.
The augmentation is a natural epimorphism with projective source.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedFreeRepresentation (A : Rep.{0} ℤ G) : Rep.{0} ℤ G :=
  Rep.free ℤ G {a : A // a ≠ 0}

def normalizedFreeGenerator (A : Rep.{0} ℤ G) (a : A) :
    normalizedFreeRepresentation A := by
  classical
  exact if h : a = 0 then 0 else Finsupp.single ⟨a, h⟩ (MonoidAlgebra.single 1 1)

@[simp]
theorem normalizedFreeGenerator_zero (A : Rep.{0} ℤ G) :
    normalizedFreeGenerator A 0 = 0 := by
  simp [normalizedFreeGenerator]

theorem normalizedFreeGenerator_of_ne_zero (A : Rep.{0} ℤ G) (a : A) (ha : a ≠ 0) :
    normalizedFreeGenerator A a = Finsupp.single ⟨a, ha⟩ (MonoidAlgebra.single 1 1) := by
  simp [normalizedFreeGenerator, ha]
  rfl

def normalizedFreeMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    normalizedFreeRepresentation A ⟶ normalizedFreeRepresentation B :=
  Rep.freeLift ℤ G (normalizedFreeRepresentation B)
    (fun a : {a : A // a ≠ 0} => normalizedFreeGenerator B (f.hom a.1))

@[simp]
theorem normalizedFreeMap_generator {A B : Rep.{0} ℤ G} (f : A ⟶ B) (a : A) :
    (normalizedFreeMap f).hom (normalizedFreeGenerator A a) =
      normalizedFreeGenerator B (f.hom a) := by
  classical
  by_cases ha : a = 0
  · subst a
    simp
  · rw [normalizedFreeGenerator_of_ne_zero A a ha]
    change (Representation.freeLift (normalizedFreeRepresentation B).ρ
      (fun b : {b : A // b ≠ 0} => normalizedFreeGenerator B (f.hom b.1)))
      (Finsupp.single ⟨a, ha⟩ (MonoidAlgebra.single 1 1)) = _
    rw [Representation.freeLift_single_single]
    simp
    exact one_smul ℤ _

def normalizedFreeAugmentation (A : Rep.{0} ℤ G) : normalizedFreeRepresentation A ⟶ A :=
  Rep.freeLift ℤ G A (fun a : {a : A // a ≠ 0} => a.1)

@[simp]
theorem normalizedFreeAugmentation_generator (A : Rep.{0} ℤ G) (a : A) :
    (normalizedFreeAugmentation A).hom (normalizedFreeGenerator A a) = a := by
  classical
  by_cases ha : a = 0
  · subst a
    simp
  · rw [normalizedFreeGenerator_of_ne_zero A a ha]
    change (Representation.freeLift A.ρ (fun b : {b : A // b ≠ 0} => b.1))
      (Finsupp.single ⟨a, ha⟩ (MonoidAlgebra.single 1 1)) = _
    rw [Representation.freeLift_single_single]
    simp
    exact @one_smul ℤ A _ A.hV2.toMulAction a

instance normalizedFreeAugmentation_epi (A : Rep.{0} ℤ G) :
    Epi (normalizedFreeAugmentation A) := by
  apply (Rep.epi_iff_surjective _).mpr
  intro a
  exact ⟨normalizedFreeGenerator A a, normalizedFreeAugmentation_generator A a⟩

theorem normalizedFreeMap_id (A : Rep.{0} ℤ G) :
    normalizedFreeMap (𝟙 A) = 𝟙 (normalizedFreeRepresentation A) := by
  apply Rep.free_ext
  intro a
  change (normalizedFreeMap (𝟙 A)).hom
    (Finsupp.single a (MonoidAlgebra.single 1 1)) = Finsupp.single a (MonoidAlgebra.single 1 1)
  rw [← normalizedFreeGenerator_of_ne_zero A a.1 a.2, normalizedFreeMap_generator]
  rfl

theorem normalizedFreeMap_comp {A B C : Rep.{0} ℤ G} (f : A ⟶ B) (g : B ⟶ C) :
    normalizedFreeMap (f ≫ g) = normalizedFreeMap f ≫ normalizedFreeMap g := by
  apply Rep.free_ext
  intro a
  rw [← normalizedFreeGenerator_of_ne_zero A a.1 a.2]
  change (normalizedFreeMap (f ≫ g)).hom (normalizedFreeGenerator A a.1) =
    (normalizedFreeMap g).hom ((normalizedFreeMap f).hom (normalizedFreeGenerator A a.1))
  rw [normalizedFreeMap_generator, normalizedFreeMap_generator, normalizedFreeMap_generator]
  rfl

@[simp]
theorem normalizedFreeMap_zero (A B : Rep.{0} ℤ G) :
    normalizedFreeMap (0 : A ⟶ B) = 0 := by
  apply Rep.free_ext
  intro a
  rw [← normalizedFreeGenerator_of_ne_zero A a.1 a.2]
  change (normalizedFreeMap (0 : A ⟶ B)).hom (normalizedFreeGenerator A a.1) = 0
  exact (normalizedFreeMap_generator (0 : A ⟶ B) a.1).trans
    (normalizedFreeGenerator_zero B)

theorem normalizedFreeAugmentation_natural {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    normalizedFreeMap f ≫ normalizedFreeAugmentation B =
      normalizedFreeAugmentation A ≫ f := by
  apply Rep.free_ext
  intro a
  rw [← normalizedFreeGenerator_of_ne_zero A a.1 a.2]
  change (normalizedFreeAugmentation B).hom
    ((normalizedFreeMap f).hom (normalizedFreeGenerator A a.1)) =
      f.hom ((normalizedFreeAugmentation A).hom (normalizedFreeGenerator A a.1))
  rw [normalizedFreeMap_generator, normalizedFreeAugmentation_generator,
    normalizedFreeAugmentation_generator]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactPairs
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact sections of Lipschitz quasi-inverse pairs

The space consists of actual continuous maps, with the compact-open topology.
Uniform Lipschitz bounds and a bound at one point give compactness in a proper
target. The quasi-inverse conditions are closed, including their compositions.
-/

noncomputable section

open Set Metric
open scoped NNReal

namespace PolycyclicRecognition

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [ProperSpace Y]

variable (G : Type*) [Group G] [MetricSpace G] [ProperSpace G]

/-- Uniform Lipschitz, lower-distance, and two-sided quasi-inverse bounds.
The source manuscript uses the same constant in these four bounds. -/
def LipschitzPairBounds (Λ : ℝ≥0) (p : C(G, G) × C(G, G)) : Prop :=
  LipschitzWith Λ p.1 ∧ LipschitzWith Λ p.2 ∧
    (∀ x y, (Λ : ℝ)⁻¹ * dist x y - Λ ≤ dist (p.1 x) (p.1 y)) ∧
    (∀ x y, (Λ : ℝ)⁻¹ * dist x y - Λ ≤ dist (p.2 x) (p.2 y)) ∧
    (∀ x, dist (p.2 (p.1 x)) x ≤ Λ) ∧
    (∀ x, dist (p.1 (p.2 x)) x ≤ Λ)

/-- The first normalized section: the forward map sends the identity to itself. -/
def normalizedPairs (Λ : ℝ≥0) : Set (C(G, G) × C(G, G)) :=
  {p | LipschitzPairBounds G Λ p ∧ p.1 1 = 1}

/-- Actual normalized pairs, carrying their compact-open topology. -/
abbrev NormalizedPair (Λ : ℝ≥0) := normalizedPairs G Λ

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairAction
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# The normalized translation action on pairs

For a pair `(F,B)`, normalization of domain translation by `x` has forward
map `F(x)⁻¹ F(xz)` and inverse map `x⁻¹ B(F(x)z)`. These are actual maps,
with all Lipschitz and quasi-inverse bounds retained. Inverting the parameter
converts the manuscript's right action into a left action.
-/

noncomputable section

open scoped NNReal

namespace PolycyclicRecognition

open MeasureTheory

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]

/-- Normalize domain translation, on pairs of continuous maps. -/
def translatePair (x : G) (p : C(G, G) × C(G, G)) : C(G, G) × C(G, G) :=
  (⟨fun z => (p.1 x)⁻¹ * p.1 (x * z),
      continuous_const.mul (p.1.continuous.comp (continuous_const.mul continuous_id))⟩,
    ⟨fun z => x⁻¹ * p.2 (p.1 x * z),
      continuous_const.mul (p.2.continuous.comp (continuous_const.mul continuous_id))⟩)

omit [ProperSpace G] in
theorem translatePair_bounds_of_bounds (Λ : ℝ≥0) (p : C(G, G) × C(G, G))
    (hp : LipschitzPairBounds G Λ p) (x : G) :
    translatePair x p ∈ normalizedPairs G Λ := by
  obtain ⟨hF, hB, hlF, hlB, hBF, hFB⟩ := hp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist ((p.1 x)⁻¹ * p.1 (x * z))
      ((p.1 x)⁻¹ * p.1 (x * w)) ≤ _
    simpa only [dist_mul_left] using hF.dist_le_mul (x * z) (x * w)
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (x⁻¹ * p.2 (p.1 x * z))
      (x⁻¹ * p.2 (p.1 x * w)) ≤ _
    simpa only [dist_mul_left] using
      hB.dist_le_mul (p.1 x * z) (p.1 x * w)
  · intro z w
    change _ ≤ dist ((p.1 x)⁻¹ * p.1 (x * z))
      ((p.1 x)⁻¹ * p.1 (x * w))
    simpa only [dist_mul_left] using hlF (x * z) (x * w)
  · intro z w
    change _ ≤ dist (x⁻¹ * p.2 (p.1 x * z))
      (x⁻¹ * p.2 (p.1 x * w))
    simpa only [dist_mul_left] using
      hlB (p.1 x * z) (p.1 x * w)
  · intro z
    change dist (x⁻¹ * p.2 (p.1 x * ((p.1 x)⁻¹ * p.1 (x * z)))) z ≤ Λ
    simp only [mul_inv_cancel_left]
    rw [← dist_mul_left x]
    simpa only [mul_inv_cancel_left] using hBF (x * z)
  · intro z
    change dist ((p.1 x)⁻¹ * p.1 (x * (x⁻¹ * p.2 (p.1 x * z)))) z ≤ Λ
    simp only [mul_inv_cancel_left]
    rw [← dist_mul_left (p.1 x)]
    simpa only [mul_inv_cancel_left] using hFB (p.1 x * z)
  · change (p.1 x)⁻¹ * p.1 (x * 1) = 1
    simp

omit [ProperSpace G] in
theorem translatePair_bounds (Λ : ℝ≥0) (p : NormalizedPair G Λ) (x : G) :
    translatePair x p.val ∈ normalizedPairs G Λ :=
  translatePair_bounds_of_bounds Λ p.val p.property.1 x

/-- Translation as a map of the compact normalized section. -/
def normalizedTranslate {Λ : ℝ≥0} (x : G) (p : NormalizedPair G Λ) :
    NormalizedPair G Λ := ⟨translatePair x p.val, translatePair_bounds Λ p x⟩

omit [ProperSpace G] in
theorem normalizedTranslate_one {Λ : ℝ≥0} (p : NormalizedPair G Λ) :
    normalizedTranslate 1 p = p := by
  apply Subtype.ext
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro z
  · change (p.val.1 1)⁻¹ * p.val.1 (1 * z) = p.val.1 z
    simp [p.property.2]
  · change (1 : G)⁻¹ * p.val.2 (p.val.1 1 * z) = p.val.2 z
    simp [p.property.2]

omit [ProperSpace G] in
theorem normalizedTranslate_mul {Λ : ℝ≥0} (x y : G) (p : NormalizedPair G Λ) :
    normalizedTranslate y (normalizedTranslate x p) = normalizedTranslate (x * y) p := by
  apply Subtype.ext
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro z <;>
    simp [normalizedTranslate, translatePair, mul_assoc]

/-- The left action corresponding to normalized right translation. -/
instance normalizedPairAction (Λ : ℝ≥0) : MulAction G (NormalizedPair G Λ) where
  smul g p := normalizedTranslate g⁻¹ p
  one_smul p := by
    change normalizedTranslate (1 : G)⁻¹ p = p
    simpa only [inv_one] using normalizedTranslate_one p
  mul_smul g h p := by
    change normalizedTranslate (g * h)⁻¹ p =
      normalizedTranslate g⁻¹ (normalizedTranslate h⁻¹ p)
    rw [normalizedTranslate_mul, mul_inv_rev]

omit [ProperSpace G] in
@[simp] theorem normalizedPair_smul_fst {Λ : ℝ≥0} (g : G)
    (p : NormalizedPair G Λ) (z : G) :
    (g • p).val.1 z = (p.val.1 g⁻¹)⁻¹ * p.val.1 (g⁻¹ * z) := rfl

omit [ProperSpace G] in
@[simp] theorem normalizedPair_smul_snd {Λ : ℝ≥0} (g : G)
    (p : NormalizedPair G Λ) (z : G) :
    (g • p).val.2 z = g * p.val.2 (p.val.1 g⁻¹ * z) := by
  change g⁻¹⁻¹ * _ = _
  rw [inv_inv]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PairCharts
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# The two product charts of the space of quasi-inverse pairs

Target normalization gives `G × X`; inverse normalization gives `X × G`,
where the latter copy of `X` represents inverse maps. Their transition is
an actual homeomorphism. This is the geometric coordinate change used for
the inverse-coupling measure, before any disintegration or fiber averaging.
-/

noncomputable section

open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

/-- All pairs with the fixed coarse bounds, without basepoint normalization. -/
abbrev CoarsePair (G : Type*) [MetricSpace G] (Λ : ℝ≥0) :=
  {p : C(G, G) × C(G, G) // LipschitzPairBounds G Λ p}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_QuotientSectionCoordinates
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates separating a quotient and its kernel

A continuous section of the actual quotient map gives global coordinates.
The formulas retain the conjugation and section cocycle needed for product
Haar measure and the ideal-coordinate estimates.
-/

noncomputable section
namespace PolycyclicRecognition

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)

/-- The kernel component left after removing the chosen section. -/
def quotientSectionResidual (n : N) : π.ker :=
  ⟨n * (s (π n))⁻¹, by
    change π (n * (s (π n))⁻¹) = 1
    rw [map_mul, map_inv, hs, mul_inv_cancel]⟩

/-- Quotient coordinate first, followed by the actual kernel coordinate. -/
def quotientSectionHomeomorph : N ≃ₜ Q × π.ker := by
  let f : N → Q × π.ker := fun n => (π n, quotientSectionResidual π s hs n)
  let g : Q × π.ker → N := fun p => (p.2 : N) * s p.1
  have hfg (p : Q × π.ker) : f (g p) = p := by
    have hp : π p.2 = 1 := p.2.property
    apply Prod.ext
    · change π ((p.2 : N) * s p.1) = p.1
      rw [map_mul, hp, hs, one_mul]
    · apply Subtype.ext
      change ((p.2 : N) * s p.1) * (s (π ((p.2 : N) * s p.1)))⁻¹ = p.2
      rw [map_mul, hp, hs, one_mul]
      exact mul_inv_cancel_right _ _
  have hgf (n : N) : g (f n) = n := by
    change (n * (s (π n))⁻¹) * s (π n) = n
    simp
  refine
    { toFun := f
      invFun := g
      left_inv := hgf
      right_inv := hfg
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply Continuous.prodMk hπ
    apply Continuous.subtype_mk
    exact continuous_id.mul (s.continuous.comp hπ).inv
  · exact (continuous_subtype_val.comp continuous_snd).mul (s.continuous.comp continuous_fst)

/-- Conjugation on the kernel, expressed without selecting logarithms. -/
def quotientKernelConjugate (n : N) (i : π.ker) : π.ker :=
  ⟨n * i * n⁻¹, by
    have hi : π i = 1 := i.property
    simp [hi]⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalAbelianRank
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rationalizing the bounded-rank abelian subgroups

The integral dimension bound applies even to abelian subgroups which are not
finitely generated. Their rationalizations have the same rank, and the
canonical map is injective because integral cohomological dimension excludes
torsion. Thus these subgroups embed in finite-dimensional rational spaces.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct

variable {A : Type} [CommGroup A]

abbrev RationalAbelianSpace (A : Type) [CommGroup A] := ℚ ⊗[ℤ] Additive A

def rationalAbelianMap : Additive A →ₗ[ℤ] RationalAbelianSpace A :=
  TensorProduct.mk ℤ ℚ (Additive A) 1

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalConjugation
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational conjugation on an abelian normal subgroup

Conjugation extends to the rationalization. When the subgroup is torsion free,
the extended action has exactly the same kernel, namely its centralizer.
Together with the rank bound this is a finite-dimensional representation of
the centralizer quotient, without a finite-generation assumption on the
abelian subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct

variable {A : Type} [CommGroup A]

def rationalAbelianAut : MulAut A →*
    (RationalAbelianSpace A ≃ₗ[ℚ] RationalAbelianSpace A) where
  toFun e := e.toAdditive.toIntLinearEquiv.baseChange ℤ ℚ _ _
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    exact TensorProduct.AlgebraTensorModule.ext (fun _ _ => rfl)
  map_mul' e f := by
    apply LinearEquiv.toLinearMap_injective
    exact TensorProduct.AlgebraTensorModule.ext (fun _ _ => rfl)

@[simp]
theorem rationalAbelianAut_map (e : MulAut A) (a : Additive A) :
    rationalAbelianAut e (rationalAbelianMap a) =
      rationalAbelianMap (Additive.ofMul (e a.toMul)) := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalCentralLayers
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational actions on the upper central layers

Ambient conjugation preserves the characteristic upper central series.
On each central layer it therefore gives a rational linear action. Trivial
rational action implies trivial action on the layer itself, since the
successive quotients are torsion-free.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

abbrev CentralLayer (i : ℕ) := Subgroup.center (F ⧸ Subgroup.upperCentralSeries F i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalNilpotentQuotient
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful rational action on the quotient by the nilpotent radical

The finitely many upper central layers give a direct-product vector space.
For a maximal nilpotent normal subgroup, the action kernel is exactly that
subgroup, by the proved central-filtration criterion.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

abbrev CentralLayersSpace (c : ℕ) :=
  (i : Fin c) → RationalAbelianSpace (CentralLayer F i)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexCartanRotations
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotations on complex Cartan weight spaces

The imaginary parts of the generalized weights define genuine Lie algebra
automorphisms. Their coefficient vectors lie in a fixed compact torus. These
are the rotations to be removed in the real-triangulable model construction.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan

open LieAlgebra LieModule Module
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The imaginary part, viewed as a purely imaginary complex number. -/
def imaginaryPart : ℂ →ₗ[ℝ] ℂ where
  toFun z := z.im * Complex.I
  map_add' z w := by simp [add_mul]
  map_smul' r z := by simp [mul_assoc]

set_option maxHeartbeats 1000000 in
/-- Rotational scalar on a weight block. -/
def phase (h : H) (χ : H → ℂ) : ℂ := Complex.exp (imaginaryPart (χ h))

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
@[simp] theorem norm_phase (h : H) (χ : H → ℂ) : ‖phase H h χ‖ = 1 := by
  simp [phase, imaginaryPart, Complex.norm_exp]

set_option maxHeartbeats 1000000 in
omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
@[simp] theorem phase_add_weight (h : H) (χ ψ : H → ℂ) :
    phase H h (χ + ψ) = phase H h χ * phase H h ψ := by
  simp only [phase, Pi.add_apply, map_add, Complex.exp_add]

set_option maxHeartbeats 1000000 in
@[simp] theorem phase_add (h k : H) (χ : Weight ℂ H L) :
    phase H (h + k) χ = phase H h χ * phase H k χ := by
  simp only [phase, map_add, Complex.exp_add]

set_option maxHeartbeats 1000000 in
@[simp] theorem phase_zero (χ : Weight ℂ H L) : phase H 0 χ = 1 := by
  simp [phase]

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealTorusContinuity
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity of the real compact rotation action -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

local instance cartanTopologicalAddGroup : IsTopologicalAddGroup H :=
  Submodule.topologicalAddGroup H.toSubmodule

end Topology
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SubexponentialBounds
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite algebra of subexponential losses -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- An upper bound of the form `exp (o(r))`. -/
def HasSubexponentialUpperBound (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop, f r ≤ Real.exp (ε * r)

theorem subexponential_upper_const (c : ℝ) :
    HasSubexponentialUpperBound (fun _ => c) := by
  intro ε hε
  exact (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hε)).eventually
    (eventually_ge_atTop c)

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponential
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential estimates along the actual sequence of profile scales -/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

def HasSubexponentialUpperBoundSeq (scale f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n ≤ Real.exp (ε * scale n)

theorem HasSubexponentialUpperBound.along_sequence {f : ℝ → ℝ}
    (hf : HasSubexponentialUpperBound f) {scale : ℕ → ℝ}
    (hs : Tendsto scale atTop atTop) : HasSubexponentialUpperBoundSeq scale (f ∘ scale) :=
  fun ε hε => hs.eventually (hf ε hε)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SequenceSubexponentialOperations
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite algebra of losses along the profile-scale sequence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {scale : ℕ → ℝ}

theorem sequence_subexponential_upper_const (hs : Tendsto scale atTop atTop)
    (c : ℝ) : HasSubexponentialUpperBoundSeq scale (fun _ => c) := by
  simpa only [Function.comp_def] using (subexponential_upper_const c).along_sequence hs

theorem HasSubexponentialUpperBoundSeq.mul {f g : ℕ → ℝ}
    (hf : HasSubexponentialUpperBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hf0 : ∀ᶠ n in atTop, 0 ≤ f n) :
    HasSubexponentialUpperBoundSeq scale (fun n => f n * g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε), hf0]
    with n hn hm h0
  calc
    f n * g n ≤ f n * Real.exp (ε / 2 * scale n) := mul_le_mul_of_nonneg_left hm h0
    _ ≤ Real.exp (ε / 2 * scale n) * Real.exp (ε / 2 * scale n) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ = Real.exp (ε * scale n) := by rw [← Real.exp_add]; congr 1; ring

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SuspendedVectorFieldBracket
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiating a transported field along time

The bracket of the constant time field with a vertical field is its time
derivative. Naturality of brackets then identifies the derivative of a
field transported by a flow, without a separate mixed-partial computation.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_prod_apply_fst {f : ℝ × E → F} {p : ℝ × E}
    (hf : DifferentiableAt ℝ f p) (v : ℝ) :
    fderiv ℝ f p (v, 0) = fderiv ℝ (fun t => f (t, p.2)) p.1 v := by
  have hi := (hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) p.2 p.1)
  have hd := hf.hasFDerivAt.comp p.1 hi
  change HasFDerivAt (fun t => f (t, p.2)) _ p.1 at hd
  rw [hd.fderiv]
  rfl

theorem fderiv_prod_apply_snd {f : ℝ × E → F} {p : ℝ × E}
    (hf : DifferentiableAt ℝ f p) (v : E) :
    fderiv ℝ f p (0, v) = fderiv ℝ (fun z => f (p.1, z)) p.2 v := by
  have hi := (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) p.2)
  have hd := hf.hasFDerivAt.comp p.2 hi
  change HasFDerivAt (fun z => f (p.1, z)) _ p.2 at hd
  rw [hd.fderiv]
  rfl

theorem lieBracket_time_vertical {Z : ℝ × E → E} {p : ℝ × E}
    (hZ : DifferentiableAt ℝ Z p) :
    VectorField.lieBracket ℝ (fun _ : ℝ × E => ((1 : ℝ), (0 : E)))
      (fun q => ((0 : ℝ), Z q)) p = (0, fderiv ℝ Z p (1, 0)) := by
  have hd := (hasFDerivAt_const (0 : ℝ) p).prodMk hZ.hasFDerivAt
  have hc := (hasFDerivAt_const (𝕜 := ℝ) ((1 : ℝ), (0 : E)) p).fderiv
  rw [VectorField.lieBracket, hd.fderiv, hc]
  simp only [ContinuousLinearMap.prod_apply, zero_apply,
    sub_zero]

theorem lieBracket_suspended_vertical {X Y : E → E} {p : ℝ × E}
    (hX : DifferentiableAt ℝ X p.2) (hY : DifferentiableAt ℝ Y p.2) :
    VectorField.lieBracket ℝ (fun q : ℝ × E => ((1 : ℝ), X q.2))
      (fun q => ((0 : ℝ), Y q.2)) p = (0, VectorField.lieBracket ℝ X Y p.2) := by
  have hdX := (hasFDerivAt_const (1 : ℝ) p).prodMk
    (hX.hasFDerivAt.comp p (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt)
  have hdY := (hasFDerivAt_const (0 : ℝ) p).prodMk
    (hY.hasFDerivAt.comp p (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt)
  dsimp only [Function.comp_def] at hdX hdY
  rw [VectorField.lieBracket, hdY.fderiv, hdX.fderiv]
  simp only [ContinuousLinearMap.prod_apply, zero_apply,
    ContinuousLinearMap.comp_apply,
    Prod.mk_sub_mk, sub_self, VectorField.lieBracket]
  rfl

theorem transportedField_time_derivative {F : ℝ × E → ℝ × E}
    {Z : ℝ × E → E} {X Y : E → E} {x : E}
    (hF : ContDiffAt ℝ 2 F (0, x))
    (hZ : DifferentiableAt ℝ Z (0, x))
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x)
    (hbase : F (0, x) = (0, x))
    (hvertical : ∀ v, fderiv ℝ F (0, x) (0, v) = (0, v))
    (htime : ∀ᶠ q in 𝓝 (0, x), fderiv ℝ F q (1, 0) = (1, X (F q).2))
    (hfield : ∀ᶠ q in 𝓝 (0, x), fderiv ℝ F q (0, Z q) = (0, Y (F q).2)) :
    fderiv ℝ Z (0, x) (1, 0) = VectorField.lieBracket ℝ X Y x := by
  have hSX : DifferentiableAt ℝ (fun q : ℝ × E => ((1 : ℝ), X q.2)) (F (0, x)) := by
    rw [hbase]
    exact (differentiableAt_const (1 : ℝ)).prodMk (hX.comp _ differentiableAt_snd)
  have hVY : DifferentiableAt ℝ (fun q : ℝ × E => ((0 : ℝ), Y q.2)) (F (0, x)) := by
    rw [hbase]
    exact (differentiableAt_const (0 : ℝ)).prodMk (hY.comp _ differentiableAt_snd)
  have hh := fderiv_lieBracket_of_related hF (differentiableAt_const ((1 : ℝ), (0 : E)))
    ((differentiableAt_const (0 : ℝ)).prodMk hZ) hSX hVY htime hfield
  rw [lieBracket_time_vertical hZ, hvertical, hbase,
    lieBracket_suspended_vertical hX hY] at hh
  exact congrArg Prod.snd hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OccupationSampling
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual probability laws of independent chart samples -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- Uniform sampling from an actual measurable cell of positive finite mass. -/
def cellProbabilityMeasure {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (S : Set Z) (hzero : μ S ≠ 0) (hfin : μ S ≠ ⊤) :
    ProbabilityMeasure Z :=
  ⟨(μ S)⁻¹ • μ.restrict S, by
    constructor
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hzero hfin⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CellProfileRestriction
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting profile samples to their actual carrying cell -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- The normalized cell measure is carried by the cell itself. -/
theorem ae_mem_cellProbabilityMeasure {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (C : Set A) (hC : MeasurableSet C) (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ⊤) :
    ∀ᵐ a ∂(cellProbabilityMeasure μ C hC0 hCfin : Measure A), a ∈ C :=
  Measure.ae_smul_measure (ae_restrict_mem hC) _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_LinearProfilesOnBall
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite linear profiles tested on one fixed ball -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- An ambient linear label observed through a surjective height map. -/
def linearBallProfile (q : V →L[ℝ] W) (A : W →L[ℝ] W) (R : ℝ) :
    C(Metric.closedBall (0 : V) R, W) :=
  ⟨fun z => A (q z), A.continuous.comp (q.continuous.comp continuous_subtype_val)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactProfileEstimates
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three estimates used in the basepoint argument -/

noncomputable section
namespace PolycyclicRecognition
open MeasureTheory Filter Metric
open scoped Topology

/-- Affine means, vanishing offsets, and deterministic suffix concentration
for the same profiles and ordinary sampling laws. -/
structure CompactProfileEstimates
    {P G N V W L : Type*} [MeasurableSpace N] [Mul N] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (raw : P × G → ℝ → N → C(V, W)) (μ : ℝ → ProbabilityMeasure N)
    (q : V →L[ℝ] W) (A : L → W →L[ℝ] W) (R : ℝ) (B : ℝ → Set N) : Prop where
  mean : ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
    (∀ n, 1 ≤ scale n) → ∀ (p : ℕ → P) (x : ℕ → G),
    ∃ a : ℕ → L, Tendsto (fun n => ∫ k,
      dist ((raw (p n, x n) (scale n) k).restrict (closedBall 0 R))
        (linearBallProfile q (A (a n)) R + ContinuousMap.const _
          (∫ k, raw (p n, x n) (scale n) k 0 ∂(μ (scale n) : Measure N)))
      ∂(μ (scale n) : Measure N)) atTop (𝓝 0)
  zeroMean : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, ∀ p r, r₀ ≤ r →
    ‖∫ k, raw p r k 0 ∂(μ r : Measure N)‖ ≤ ε
  suffix : ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
    (∀ n, 1 ≤ scale n) → ∀ (p : ℕ → P) (x : ℕ → G) (k : ℕ → N), (∀ n, k n ∈ B (scale n)) → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => (μ (scale n) : Measure N)
      {z | ε ≤ dist ((raw (p n, x n) (scale n) (z * k n)).restrict (closedBall 0 R))
        ((raw (p n, x n) (scale n) z).restrict (closedBall 0 R))}) atTop (𝓝 0)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeProbeEndpoints
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three actual endpoints used in the cone offset comparison -/

namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {N : Type*} [Group N]

/-- The neighboring endpoint carrying the same ideal probe. -/
def coneProbeSecond (S : MulAut N) (n i k : N) : N := n * S i * S k

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IdealSectionBoxCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact linear coordinates for an ideal and its quotient

Pure quotient lifts have weight zero. In the adapted basis, projection
retains exactly those coordinates, and inclusion of the ideal retains
exactly the weighted ideal coordinates. This is the linear part of the
section-coordinate box comparison.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {V I J : Type*} [LieRing V] [LieAlgebra ℝ V]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

def quotientLinearSection : (V ⧸ U.toSubmodule) →ₗ[ℝ] V := bQ.constr ℝ lift

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_JacobianMeasure
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measure transport from a unit Jacobian

This is the change-of-variables step used by the nilpotent BCH chart.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem map_eq_self_of_unit_jacobian (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) (df : E → E →L[ℝ] E)
    (hdf : ∀ x, HasFDerivAt f (df x) x) (hf : Function.Bijective f)
    (hdet : ∀ x, (df x).det = 1) : Measure.map f μ = μ := by
  have hh := map_withDensity_abs_det_fderiv_eq_addHaar μ
    (s := univ) (MeasurableSet.univ : MeasurableSet (univ : Set E)).nullMeasurableSet
    (fun x _ => (hdf x).hasFDerivWithinAt) hf.injective.injOn
  have hdensity : (fun x => ENNReal.ofReal |(df x).det|) = fun _ => 1 := by
    funext x
    simp only [hdet x, abs_one, ENNReal.ofReal_one]
  rw [hdensity, Measure.restrict_univ, image_univ, hf.surjective.range_eq,
    Measure.restrict_univ] at hh
  have hone : μ.withDensity (fun _ : E => (1 : ℝ≥0∞)) = μ := withDensity_one
  rw [hone] at hh
  exact hh

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A homeomorphism transports additive Haar measure to Haar measure when
the conjugates of left translations preserve it. -/
theorem homeomorph_map_isHaar_of_translations
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (c : E ≃ₜ G) (μ : Measure E) [μ.IsAddHaarMeasure]
    (htranslations : ∀ g : G,
      Measure.map (fun x => c.symm (g * c x)) μ = μ) :
    (Measure.map c μ).IsHaarMeasure := by
  refine
    { map_mul_left_eq_self := ?_
      toIsFiniteMeasureOnCompacts := Measure.IsFiniteMeasureOnCompacts.map μ c
      toIsOpenPosMeasure := c.continuous.isOpenPosMeasure_map c.surjective }
  intro g
  have hleft : Measurable (fun x : G => g * x) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_map hleft c.measurable]
  have heq : (fun y : G => g * y) ∘ c = c ∘ (fun x => c.symm (g * c x)) := by
    funext x
    simp only [Function.comp_apply, c.apply_symm_apply]
  have htrans : Measurable (fun x : E => c.symm (g * c x)) :=
    (c.symm.continuous.comp (continuous_const.mul c.continuous)).measurable
  rw [heq, ← Measure.map_map c.measurable htrans, htranslations]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_KernelHaarTransport
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar measure on the actual quotient kernel

A closed realization of a Lie ideal identifies its intrinsic group with
the kernel. Equivariance transports conjugation invariance, and hence
also right invariance, to the measure used in section coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {I N Q : Type*} [Group I] [Group N] [Group Q]
  [TopologicalSpace I] [TopologicalSpace N] [IsTopologicalGroup I] [IsTopologicalGroup N]
  (π : N →* Q) (ι : I →* N) (hι : Topology.IsClosedEmbedding ι)
  (hrange : Set.range ι = (π.ker : Set N))

/-- The intrinsic ideal group and the actual kernel have the same topology
and multiplication. -/
def kernelRealization : I ≃ₜ* π.ker := by
  let e : I ≃ₜ π.ker := hι.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  refine { e with map_mul' := ?_ }
  intro x y
  apply Subtype.ext
  change ι (x * y) = ι x * ι y
  exact map_mul ι x y

omit [IsTopologicalGroup I] [IsTopologicalGroup N] in
@[simp] theorem kernelRealization_coe (x : I) :
    (kernelRealization π ι hι hrange x : N) = ι x := rfl

variable [MeasurableSpace I] [MeasurableSpace N] [BorelSpace I] [BorelSpace N]
  (μ : Measure I)

omit [IsTopologicalGroup I] in
/-- A concrete equivariant automorphism preserving intrinsic Haar measure
also preserves its image on the kernel. -/
theorem kernelRealization_conjugation_preserving (n : N) (F : I → I)
    (hF : MeasurePreserving F μ μ)
    (hequiv : ∀ x, ι (F x) = n * ι x * n⁻¹) :
    MeasurePreserving (quotientKernelConjugate π n)
      (Measure.map (kernelRealization π ι hι hrange) μ)
      (Measure.map (kernelRealization π ι hι hrange) μ) := by
  let e := kernelRealization π ι hι hrange
  have hsem : Function.Semiconj e F (quotientKernelConjugate π n) := by
    intro x
    apply Subtype.ext
    exact hequiv x
  have hc : Continuous (quotientKernelConjugate π n) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  exact (e.continuous.measurable.measurePreserving μ).of_semiconj hF hsem hc.measurable

/-- Left invariance together with the ambient conjugation invariance gives
the right invariance needed by the section cocycle. -/
theorem kernel_measure_right_invariant (ν : Measure π.ker) [ν.IsMulLeftInvariant]
    (hconj : ∀ n : N, MeasurePreserving (quotientKernelConjugate π n) ν ν) :
    ν.IsMulRightInvariant := by
  constructor
  intro k
  have hleft : MeasurePreserving (fun x : π.ker => k * x) ν ν :=
    ⟨(continuous_const.mul continuous_id).measurable, map_mul_left_eq_self ν k⟩
  have heq : (fun x : π.ker => k * quotientKernelConjugate π (k : N)⁻¹ x) =
      fun x => x * k := by
    funext x
    apply Subtype.ext
    change (k : N) * ((k : N)⁻¹ * x * ((k : N)⁻¹)⁻¹) = x * k
    group
  have hm := hleft.comp (hconj (k : N)⁻¹)
  change Measure.map (fun x : π.ker => x * k) ν = ν
  rw [← heq]
  exact hm.map_eq

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MixedWordBoxModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete nilpotent box model of a cone ideal

The finite mixed words generate the ideal even as a vector space. Using
them as an alphabet allows the existing box calculus to apply directly.
Flattening this alphabet retains the original word and its exact width.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule LieAlgebra
open scoped BigOperators

def substituteBracketWord {I J : Type*} (f : I → FreeMagma J) :
    FreeMagma I → FreeMagma J
  | .of i => f i
  | .mul u v => substituteBracketWord f u * substituteBracketWord f v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NeighborProfileGluing
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single profile on the two cells of a neighboring pair -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory

variable {N S V : Type*} [Group N] [MeasurableSpace N]
  [MeasurableSpace S]

/-- Retain the first profile on the first cell and the transported second
profile elsewhere. Compatibility makes the values agree on the overlap. -/
def glueNeighborProfile (A : Set N) (t : N) (f : N → S × S) (x : N) : S := by
  classical
  exact if x ∈ A then (f x).1 else (f (x * t⁻¹)).2

variable [MeasurableMul₂ N]

theorem measurable_glueNeighborProfile {A : Set N} (hA : MeasurableSet A)
    (t : N) {f : N → S × S} (hf : Measurable f) :
    Measurable (glueNeighborProfile A t f) := by
  classical
  exact hf.fst.ite hA (hf.snd.comp (measurable_id.mul_const t⁻¹))

omit [MeasurableSpace N] [MeasurableSpace S] [MeasurableMul₂ N] in
theorem glueNeighborProfile_pair {A : Set N} (t : N) (f : N → S × S)
    (hcompat : ∀ x ∈ A, x * t ∈ A → (f (x * t)).1 = (f x).2)
    {x : N} (hx : x ∈ A) :
    (glueNeighborProfile A t f x, glueNeighborProfile A t f (x * t)) = f x := by
  classical
  have hleft : glueNeighborProfile A t f x = (f x).1 := by
    simp [glueNeighborProfile, hx]
  have hright : glueNeighborProfile A t f (x * t) = (f x).2 := by
    by_cases hxt : x * t ∈ A
    · simpa only [glueNeighborProfile, ite_eq_left hxt] using hcompat x hx hxt
    · simp [glueNeighborProfile, hxt]
  exact Prod.ext hleft hright

omit [MeasurableSpace N] [MeasurableSpace S] [MeasurableMul₂ N] in
/-- Injective evaluation into actual profiles supplies overlap compatibility
and the correct value throughout the union of the neighboring cells. -/
theorem glueNeighborProfile_actual {A : Set N} (t : N) (f : N → S × S)
    (value : S → V) (hvalue : Function.Injective value) (actual : N → V)
    (hfirst : ∀ x ∈ A, value (f x).1 = actual x)
    (hsecond : ∀ x ∈ A, value (f x).2 = actual (x * t)) :
    (∀ x ∈ A, (glueNeighborProfile A t f x,
      glueNeighborProfile A t f (x * t)) = f x) ∧
    ∀ x ∈ A ∪ (fun y => y * t) '' A,
      value (glueNeighborProfile A t f x) = actual x := by
  classical
  refine ⟨fun x hx => glueNeighborProfile_pair t f (fun y hy hyt => ?_) hx, ?_⟩
  · exact hvalue ((hfirst (y * t) hyt).trans (hsecond y hy).symm)
  · intro x hx
    by_cases hxA : x ∈ A
    · simpa only [glueNeighborProfile, ite_eq_left hxA] using hfirst x hxA
    · rcases hx with hx | ⟨y, hy, rfl⟩
      · exact (hxA hx).elim
      · simpa [glueNeighborProfile, hxA] using hsecond y hy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SupportFlowLegs
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual one-parameter legs between support positions

The height along a translated one-parameter leg is the affine segment
between its endpoint heights. Its metric bound is uniform at scale `r`,
with one fixed additive constant for the finite-mesh argument.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [AddCommGroup W] [Module ℝ W]

def flowLeg (d : ℝ → G) (x : G) (r t : ℝ) : G := x * d (r * t)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportVisitPaths
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outward, switch, and return paths

The actual three curves are concatenated, retaining their exact heights and
the logarithmic switch error. This statement is independent of how the
switch estimate is obtained and is used below for the Cartan root curves.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped unitInterval

variable {G W : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [AddCommGroup W] [Module ℝ W]

def flowPath (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1) (x : G) (r : ℝ) :
    Path x (x * d r) where
  toFun t := flowLeg d x r t
  continuous_toFun := continuous_const.mul (hd.comp (continuous_const.mul continuous_subtype_val))
  source' := by simp [flowLeg, hzero]
  target' := by simp [flowLeg]

/-- The specified outward-switch-return path, with no choice of curves. -/
def supportVisitPath (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1) (n d₀ : G) (r b : ℝ) :
    Path (n * d₀) (n * f b * d₀) :=
  let p₀ := flowPath d hd hzero (n * d₀) r
  let p₁ := flowPath d hd hzero (n * f b * d₀) r
  let q : Path ((n * d₀) * d r) ((n * f b * d₀) * d r) := {
    toFun := fun t => n * f ((t : ℝ) * b) * (d₀ * d r)
    continuous_toFun := (continuous_const.mul
      (hf.comp (continuous_subtype_val.mul continuous_const))).mul continuous_const
    source' := by simp [hf₀, mul_assoc]
    target' := by simp [mul_assoc] }
  (p₀.trans q).trans p₁.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ParametrizedSupportPaths
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous sampling of prescribed generator words

When the generator indices are fixed and the amplitudes depend continuously
on a parameter, every fixed time sample of the explicitly constructed path
is continuous in that parameter. This retains the measurability needed for
stationary endpoint averaging.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G I : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  (d f : I → ℝ → G) (hd : ∀ i, Continuous (d i)) (hf : ∀ i, Continuous (f i))
  (hd₀ : ∀ i, d i 0 = 1) (hf₀ : ∀ i, f i 0 = 1)
  (d₀ : G) (r : ℝ)

def indexedWordProduct (u : List (I × ℝ)) : G :=
  (u.map (fun z => f z.1 z.2)).prod

def supportWordPath : (u : List (I × ℝ)) → (n : G) →
    Path (n * d₀) (n * indexedWordProduct f u * d₀)
  | [], n => (Path.refl (n * d₀)).cast rfl (by simp [indexedWordProduct])
  | (i, b) :: u, n =>
    ((supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i) n d₀ r b).trans
      (supportWordPath u (n * f i b))).cast rfl (by simp [indexedWordProduct, mul_assoc])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialSubsetVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume of arbitrary subsets in rescaled exponential coordinates

The change-of-coordinates determinant formula applies to the independently
sampled good subset, not just to an entire box. The exponential chart is a
measurable embedding, so this calculation does not assume absolute
continuity of an arbitrarily selected word parametrization.
-/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {I : Type*} {n : ℕ}

/-- Change of exponential basis on an arbitrary coordinate set. -/
theorem exponential_basis_image_eq
    {G : Type*} (Exp : L → G) (b₀ b : Basis (Fin n) ℝ L) (S : Set (Fin n → ℝ)) :
    (Exp ∘ b.equivFun.symm) '' S =
      (Exp ∘ b₀.equivFun.symm) '' ((Matrix.toLin' (b₀.toMatrix b)) '' S) := by
  have hf : (Exp ∘ b.equivFun.symm) =
      (Exp ∘ b₀.equivFun.symm) ∘ (Matrix.toLin' (b₀.toMatrix b)) := by
    funext y
    have he := b.toMatrix_mulVec_repr b₀ (b.equivFun.symm y)
    rw [← Basis.equivFun_apply, b.equivFun.apply_symm_apply] at he
    dsimp only [Function.comp_apply]
    change (Matrix.toLin' (b₀.toMatrix b)) y = b₀.equivFun (b.equivFun.symm y) at he
    rw [he, b₀.equivFun.symm_apply_apply]
  rw [hf, Set.image_comp]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

/-- The exact determinant formula for every coordinate subset in the global
nilpotent exponential chart. -/
theorem exponential_basis_subset_measure
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ b : Basis (Fin n) ℝ L) (S : Set (Fin n → ℝ)) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (((Exp ∘ e) ∘ b.equivFun.symm) '' S) =
      ENNReal.ofReal |(b₀.toMatrix b).det| * volume S := by
  let b' := b₀.map e.toLinearEquiv
  let f := (Exp ∘ e) ∘ b₀.equivFun.symm
  let c : (Fin n → ℝ) ≃ₜ G :=
    b'.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : f = c := by
    funext y
    dsimp only [f, c, Function.comp_apply, Homeomorph.trans_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, LinearEquiv.coe_toContinuousLinearEquiv]
    rw [hchart, Basis.map_equivFun]
    rfl
  have hmeas : MeasurableEmbedding f := by rw [hf]; exact c.measurableEmbedding
  rw [exponential_basis_image_eq (Exp ∘ e) b₀ b S]
  change (Measure.map f volume) (f '' _) = _
  rw [hmeas.map_apply, Set.preimage_image_eq _ hmeas.injective,
    Measure.addHaar_image_linearMap, LinearMap.det_toLin']

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_RescaledImageVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accessible logarithmic volume becomes the exact exponential Haar rate -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Continuity is obtained from the supplied intrinsic exponential chart. -/
theorem continuous_exponential_basis {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b : Basis (Fin n) ℝ L) : Continuous (((Exp ∘ e) ∘ b.equivFun.symm) : (Fin n → ℝ) → G) := by
  let b' := b.map e.toLinearEquiv
  let c : (Fin n → ℝ) ≃ₜ G :=
    b'.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have he : ((Exp ∘ e) ∘ b.equivFun.symm) = c := by
    funext y
    dsimp only [c, Function.comp_apply, Homeomorph.trans_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, LinearEquiv.coe_toContinuousLinearEquiv]
    rw [hchart, Basis.map_equivFun]
    rfl
  rw [he]
  exact c.continuous

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRightHaar
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Right invariance of exponential-coordinate Haar measure

Negation preserves coordinate Lebesgue measure and corresponds to group
inversion. Thus the exponential-coordinate left Haar measure is also right
invariant, without a separate group nilpotence assertion.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

/-- Oddness of an exponential chart makes its coordinate measure invariant
under group inversion. -/
theorem isInvInvariant_map_of_neg
    {V G : Type*} [AddCommGroup V] [MeasurableSpace V] [MeasurableNeg V]
    [Group G] [MeasurableSpace G] [MeasurableInv G]
    (ν : Measure V) [ν.IsNegInvariant]
    (f : V → G) (hf : Measurable f) (hneg : ∀ x, f (-x) = (f x)⁻¹) :
    (Measure.map f ν).IsInvInvariant := by
  constructor
  change Measure.map Inv.inv (Measure.map f ν) = Measure.map f ν
  rw [Measure.map_map measurable_inv hf]
  have hcomp : Inv.inv ∘ f = f ∘ Neg.neg := by
    funext x
    exact (hneg x).symm
  rw [hcomp, ← Measure.map_map hf measurable_neg, Measure.map_neg_eq_self]

/-- The same coordinate measure is right Haar as soon as it is left invariant. -/
theorem isMulRightInvariant_map_of_neg
    {V G : Type*} [AddCommGroup V] [MeasurableSpace V] [MeasurableNeg V]
    [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    (ν : Measure V) [ν.IsNegInvariant]
    (f : V → G) (hf : Measurable f) (hneg : ∀ x, f (-x) = (f x)⁻¹)
    [(Measure.map f ν).IsMulLeftInvariant] :
    (Measure.map f ν).IsMulRightInvariant := by
  let μ := Measure.map f ν
  let : μ.IsInvInvariant := isInvInvariant_map_of_neg ν f hf hneg
  have hi : μ.inv = μ := Measure.inv_eq_self μ
  change μ.IsMulRightInvariant
  rw [← hi]
  first | exact Measure.isProbabilityMeasure_map (by first | exact hf.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CanonicalExponentialMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar properties of the exact measure used by the image-volume formula -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The published input gives Haar invariance to this specific coordinate
measure, so recurrence and the determinant formula use the same normalization. -/
theorem exponential_basis_measure_isHaar
    (haar : NilpotentExponentialHaarInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {n : ℕ} (b : Basis (Fin n) ℝ L) :
    (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume).IsHaarMeasure := by
  have he : ((Exp ∘ e) ∘ b.equivFun.symm) =
      Exp ∘ (b.map e.toLinearEquiv).equivFun.symm := by
    funext x
    rw [Basis.map_equivFun]
    rfl
  rw [he]
  exact (haar.2 Exp hExp (e.nilpotent_iff_equiv_nilpotent.mp hnil)).2 n _

/-- Inversion corresponds to coordinate negation. Thus the same measure
is also right invariant, as required by backward recurrence. -/
theorem exponential_basis_measure_isRightInvariant
    (haar : NilpotentExponentialHaarInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {n : ℕ} (b : Basis (Fin n) ℝ L) :
    (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume).IsMulRightInvariant := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let μ := Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haar e hnil Exp hExp b
  obtain ⟨⟨chart, hc⟩, _⟩ := haar.2 Exp hExp (e.nilpotent_iff_equiv_nilpotent.mp hnil)
  apply isMulRightInvariant_map_of_neg volume _
    (continuous_exponential_basis e Exp chart hc b).measurable
  intro x
  simp only [Function.comp_apply, map_neg, hExp.map_neg]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TranslatedBoxMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume ratios for translated exponential boxes -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

/-- Right translation preserves the measure of every set, including sets
whose measurability has not yet been established separately. -/
theorem measure_image_mul_right {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant] (S : Set G) (k : G) :
    μ ((fun x => x * k) '' S) = μ S := by
  rw [← measure_preimage_mul_right μ k ((fun x => x * k) '' S),
    Set.preimage_image_eq _ (show Function.Injective (fun x : G => x * k) from
      fun _ _ h => mul_right_cancel h)]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TranslationCovering
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A covering from two-sided translation coordinates

A local group parameterization whose left and right translations are global
homeomorphisms is a covering map. No associativity on the parameter space is
needed for this step.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {V G : Type*} [TopologicalSpace V] [Zero V]
  [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  (f : V → G) (R : V → V ≃ₜ V)
  (hR : ∀ a x, f (R a x) = f x * f a)
  (hzero : f 0 = 1) (hf : IsLocalHomeomorph f)
  (hRinv : Continuous (fun p : V × V => (R p.1).symm p.2))
  (hRcont : Continuous (fun p : V × V => R p.1 p.2))

omit [IsTopologicalGroup G] in
include hzero hf in
theorem kernel_discrete : DiscreteTopology (f ⁻¹' {1}) := by
  have heq : f '' (f ⁻¹' {1}) = {1} := by
    ext g
    constructor
    · rintro ⟨v, hv, rfl⟩; exact hv
    · rintro rfl; exact ⟨0, hzero, hzero⟩
  have : DiscreteTopology (f '' (f ⁻¹' {1})) := by rw [heq]; infer_instance
  exact (hf.isLocalHomeomorphOn.mono (subset_univ _)).discreteTopology_of_image

omit [Zero V] [IsTopologicalGroup G] in
include hR in
theorem right_inverse_fiber (e : OpenPartialHomeomorph G V)
    (he : ∀ g ∈ e.source, f (e g) = g) {x : V} (hx : f x ∈ e.source) :
    f ((R (e (f x))).symm x) = 1 := by
  have hh := hR (e (f x)) ((R (e (f x))).symm x)
  rw [(R (e (f x))).apply_symm_apply, he _ hx] at hh
  apply mul_right_cancel (b := f x)
  simpa using hh.symm

include hR hf hRinv hRcont in
def translationFiberHomeomorph (e : OpenPartialHomeomorph G V)
    (he : ∀ g ∈ e.source, f (e g) = g) :
    (f ⁻¹' e.source) ≃ₜ e.source × (f ⁻¹' {1}) where
  toFun x := (⟨f x, x.2⟩,
    ⟨(R (e (f x))).symm x, right_inverse_fiber f R hR e he x.2⟩)
  invFun p := ⟨R (e p.1) p.2, by
    change f (R (e p.1) p.2) ∈ e.source
    rw [hR, show f p.2 = 1 from p.2.2, one_mul, he _ p.1.2]
    exact p.1.2⟩
  left_inv x := Subtype.ext ((R (e (f x))).apply_symm_apply x)
  right_inv p := by
    have hh : f (R (e p.1) p.2) = p.1 := by
      rw [hR, show f p.2 = 1 from p.2.2, one_mul, he _ p.1.2]
    apply Prod.ext
    · exact Subtype.ext hh
    · apply Subtype.ext
      change (R (e (f (R (e p.1) p.2)))).symm (R (e p.1) p.2) = p.2
      rw [hh, (R (e p.1)).symm_apply_apply]
  continuous_toFun := by
    have hf' : Continuous (fun x : f ⁻¹' e.source => f x) :=
      hf.continuous.comp continuous_subtype_val
    have he' : Continuous (fun x : f ⁻¹' e.source => e (f x)) :=
      e.continuousOn_toFun.comp_continuous hf' (fun x => x.2)
    exact (hf'.subtype_mk _).prodMk
      ((hRinv.comp (he'.prodMk continuous_subtype_val)).subtype_mk _)
  continuous_invFun := by
    have he' : Continuous (fun p : e.source × (f ⁻¹' {1}) => e p.1) :=
      (e.continuousOn_toFun.comp_continuous continuous_subtype_val (fun x => x.2)).comp
        continuous_fst
    exact (hRcont.comp (he'.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

omit [IsTopologicalGroup G] in
include hR hzero hf hRinv hRcont in
theorem evenlyCovered_one_of_translations : IsEvenlyCovered f 1 (f ⁻¹' {1}) := by
  let _ := kernel_discrete f hzero hf
  let e := hf.localInverseAt 0
  have hmem : (1 : G) ∈ e.source := hzero ▸ hf.apply_self_mem_localInverseAt_source (x := 0)
  have he : ∀ g ∈ e.source, f (e g) = g := fun _ hg =>
    hf.apply_localInverseAt_of_mem hg
  exact ⟨inferInstance, e.source, hmem, e.open_source,
    e.open_source.preimage hf.continuous,
    translationFiberHomeomorph f R hR hf hRinv hRcont e he, fun _ => rfl⟩

include hR hzero hf hRinv hRcont in
theorem covering_of_translations
    (L : V → V ≃ₜ V) (hL : ∀ a x, f (L a x) = f a * f x)
    (hsurj : Function.Surjective f) : IsCoveringMap f := by
  intro g
  obtain ⟨a, rfl⟩ := hsurj g
  have hh := (evenlyCovered_one_of_translations f R hR hzero hf hRinv hRcont).homeomorph_comp
    (Homeomorph.mulLeft (f a))
  have hh' := hh.comp_homeomorph (L a).symm
  have heq : (Homeomorph.mulLeft (f a) ∘ f) ∘ (L a).symm = f := by
    funext x
    exact (hL a ((L a).symm x)).symm.trans (congrArg f ((L a).apply_symm_apply x))
  rw [heq] at hh'
  have hh'' : IsEvenlyCovered f (f a) (f ⁻¹' {1}) := by simpa using hh'
  exact hh''.to_isEvenlyCovered_preimage

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedSyzygyFunctor
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Functorial syzygies from the normalized free cover -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

abbrev normalizedSyzygy (A : Rep.{0} ℤ G) : Rep.{0} ℤ G :=
  kernel (normalizedFreeAugmentation A)

def normalizedSyzygyMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    normalizedSyzygy A ⟶ normalizedSyzygy B :=
  kernel.map (normalizedFreeAugmentation A) (normalizedFreeAugmentation B)
    (normalizedFreeMap f) f (normalizedFreeAugmentation_natural f).symm

@[reassoc (attr := simp)]
theorem normalizedSyzygyMap_ι {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    normalizedSyzygyMap f ≫ kernel.ι (normalizedFreeAugmentation B) =
      kernel.ι (normalizedFreeAugmentation A) ≫ normalizedFreeMap f := by
  apply kernel.lift_ι

def normalizedSyzygyFunctor : Rep.{0} ℤ G ⥤ Rep.{0} ℤ G where
  obj := normalizedSyzygy
  map := normalizedSyzygyMap
  map_id A := by
    apply (cancel_mono (kernel.ι (normalizedFreeAugmentation A))).mp
    simp only [normalizedSyzygyMap_ι, normalizedFreeMap_id, Category.comp_id, Category.id_comp]
  map_comp f g := by
    apply (cancel_mono (kernel.ι (normalizedFreeAugmentation _))).mp
    simp only [Category.assoc, normalizedSyzygyMap_ι, normalizedSyzygyMap_ι_assoc,
      normalizedFreeMap_comp]

def normalizedSyzygySequence (A : Rep.{0} ℤ G) : ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (kernel.ι (normalizedFreeAugmentation A))
    (normalizedFreeAugmentation A) (kernel.condition _)

theorem normalizedSyzygySequence_shortExact (A : Rep.{0} ℤ G) :
    (normalizedSyzygySequence A).ShortExact := by
  refine {
    exact := ShortComplex.exact_kernel (normalizedFreeAugmentation A)
    mono_f := ?_
    epi_g := ?_ }
  · change Mono (kernel.ι (normalizedFreeAugmentation A))
    infer_instance
  · change Epi (normalizedFreeAugmentation A)
    infer_instance

def iteratedNormalizedSyzygy : ℕ → (Rep.{0} ℤ G ⥤ Rep.{0} ℤ G)
  | 0 => 𝟭 _
  | n + 1 => iteratedNormalizedSyzygy n ⋙ normalizedSyzygyFunctor

def normalizedSyzygyConnecting (A : Rep.{0} ℤ G) (n : ℕ) :
    groupCohomology ((iteratedNormalizedSyzygy n).obj A) n ⟶
      groupCohomology ((iteratedNormalizedSyzygy (n + 1)).obj A) (n + 1) :=
  groupCohomology.δ (normalizedSyzygySequence_shortExact
    ((iteratedNormalizedSyzygy n).obj A)) n (n + 1) rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedCohomology
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degree-zero complete cohomology from normalized syzygies

The transition maps are the actual connecting homomorphisms of the natural
short exact free-cover sequences. No vanishing theorem is assumed here.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

abbrev normalizedCohomologyStage (A : Rep.{0} ℤ G) (n : ℕ) : Type :=
  groupCohomology ((iteratedNormalizedSyzygy n).obj A) n

def normalizedCohomologyStageMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) (n : ℕ) :
    normalizedCohomologyStage A n →ₗ[ℤ] normalizedCohomologyStage B n :=
  (groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy n).map f) n).hom

@[simp]
theorem normalizedCohomologyStageMap_id (A : Rep.{0} ℤ G) (n : ℕ) :
    normalizedCohomologyStageMap (𝟙 A) n = LinearMap.id := by
  unfold normalizedCohomologyStageMap
  rw [CategoryTheory.Functor.map_id, groupCohomology.map_id]
  rfl

def normalizedCohomologyForward (A : Rep.{0} ℤ G) (i j : ℕ) (h : i ≤ j) :
    normalizedCohomologyStage A i →ₗ[ℤ] normalizedCohomologyStage A j where
  toFun := Nat.leRecOn h (fun {k} => (normalizedSyzygyConnecting A k).hom)
  map_add' x y := by
    induction h with
    | refl => simp only [Nat.leRecOn_self]
    | @step j h ih => simp only [Nat.leRecOn_succ h, map_add, ih]
  map_smul' r x := by
    induction h with
    | refl => simp only [Nat.leRecOn_self, RingHom.id_apply]
    | @step j h ih =>
      simp only [Nat.leRecOn_succ h, ih, RingHom.id_apply]
      exact (normalizedSyzygyConnecting A j).hom.map_smul r _

abbrev CompletedCohomology (A : Rep.{0} ℤ G) :=
  Module.DirectLimit (normalizedCohomologyStage A) (normalizedCohomologyForward A)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightSamplingPolytope
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact polyhedron used for sampling the nilpotent boxes -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]

/-- Halfspaces tangent to the unit ball, one per oriented generator ray. -/
def weightSamplingPolytope (α : I → W →L[ℝ] ℝ) : Set W :=
  {x | ∀ i, α i x ≤ ‖α i‖}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSamplingParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete parameters for the neighboring-sheet sampling argument -/

noncomputable section

namespace PolycyclicRecognition

open Set

set_option maxHeartbeats 1000000 in
/-- Source, reverse anchor, and within-tile radii, in that order. -/
def threePolarRadii (ε : ℝ) : Fin 3 → ℝ := ![2 * ε / 3, ε, ε / 3]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarTiledChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three actual chains for the polar flow partition -/

noncomputable section
namespace PolycyclicRecognition

set_option maxHeartbeats 1000000 in
/-- Normalized templates ordered as source, reverse anchor, within-tile. -/
def normalizedPolarTemplates {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (K : ProperCone ℝ (StrongDual ℝ W)) (ε : ℝ) (j : Fin 3) : Set W :=
  (fun z => threePolarRadii ε j • z) '' conePolarTemplate K

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ChartedExponentialFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The right exponential flow in an identity chart -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function
open scoped Manifold ContDiff Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- Right multiplication is the flow of the left-invariant field. -/
def chartExponentialFlow (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (v : E)
    (q : ℝ × E) : ℝ × E :=
  (q.1, extChartAt (𝓘(ℝ, E)) (1 : G)
    ((extChartAt (𝓘(ℝ, E)) (1 : G)).symm q.2 * Exp (q.1 • v)))

theorem contDiffAt_chartExponentialFlow
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) (v : E) :
    ContDiffAt ℝ ∞ (chartExponentialFlow Exp v)
      (0, extChartAt (𝓘(ℝ, E)) (1 : G) 1) := by
  let φ := extChartAt (𝓘(ℝ, E)) (1 : G)
  have hi : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ.symm (φ 1) := by
    simpa only [φ, mfld_simps, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, E)) (n := ∞) (1 : G))
  have hmul : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, E)) ∞
      (fun q : ℝ × E => φ.symm q.2 * Exp (q.1 • v)) ((0 : ℝ), φ 1) := by
    have hs : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, E)) ∞ Prod.snd ((0 : ℝ), φ 1) :=
      contDiffAt_snd.contMDiffAt
    have ht : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, ℝ)) ∞ Prod.fst ((0 : ℝ), φ 1) :=
      contDiffAt_fst.contMDiffAt
    have hc : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (fun s : ℝ => Exp (s • v)) 0 :=
      (hExp.contMDiff_curve v) 0
    have hct : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, E)) ∞
        (fun q : ℝ × E => Exp (q.1 • v)) ((0 : ℝ), φ 1) :=
      hc.comp ((0 : ℝ), φ 1) (f := fun q : ℝ × E => q.1) ht
    exact (hi.comp ((0 : ℝ), φ 1) hs).mul hct
  have hbase : φ.symm (φ 1) * Exp ((0 : ℝ) • v) = 1 := by
    simp only [φ, extChartAt_to_inv, zero_smul, one_mul]
    exact hExp.map_zero
  have hφ := (contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := (1 : G))).comp_of_eq hmul hbase
  exact contDiffAt_fst.prodMk hφ.contDiffAt

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
@[simp] theorem chartExponentialFlow_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) (v : E)
    {z : E} (hz : z ∈ (extChartAt (𝓘(ℝ, E)) (1 : G)).target) :
    chartExponentialFlow Exp v (0, z) = (0, z) := by
  unfold chartExponentialFlow
  simp only [zero_smul]
  change ((0 : ℝ), extChartAt (𝓘(ℝ, E)) (1 : G)
    ((extChartAt (𝓘(ℝ, E)) (1 : G)).symm z * Exp (0 : GroupLieAlgebra (𝓘(ℝ, E)) G))) = _
  rw [hExp.map_zero, mul_one, (extChartAt (𝓘(ℝ, E)) (1 : G)).right_inv hz]

theorem fderiv_chartExponentialFlow_vertical_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp) (v w : E) :
    fderiv ℝ (chartExponentialFlow Exp v)
      (0, extChartAt (𝓘(ℝ, E)) (1 : G) 1) (0, w) = (0, w) := by
  let z₀ := extChartAt (𝓘(ℝ, E)) (1 : G) 1
  have hd := (contDiffAt_chartExponentialFlow hExp v).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [fderiv_prod_apply_snd hd]
  have heq : (fun z => chartExponentialFlow Exp v (0, z)) =ᶠ[𝓝 z₀]
      (fun z : E => ((0 : ℝ), z)) := by
    have ht : (extChartAt (𝓘(ℝ, E)) (1 : G)).target ∈ 𝓝 z₀ := by
      simpa only [z₀, mfld_simps, nhdsWithin_univ] using
        extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) (1 : G)
    exact eventually_of_mem ht fun z hz => chartExponentialFlow_zero hExp v hz
  rw [heq.fderiv_eq]
  have hh := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) z₀).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) z₀)
  dsimp only [id_eq] at hh
  rw [hh.fderiv]
  rfl

theorem hasDerivAt_chartExponentialFlow_time
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : E) (t : ℝ) (z : E)
    (ht : (extChartAt (𝓘(ℝ, E)) (1 : G)).symm z * Exp (t • v) ∈
      (extChartAt (𝓘(ℝ, E)) (1 : G)).source) :
    HasDerivAt (fun s => (chartExponentialFlow Exp v (s, z)).2)
      (chartInvariantFrame (1 : G) (chartExponentialFlow Exp v (t, z)).2 v) t := by
  let φ := extChartAt (𝓘(ℝ, E)) (1 : G)
  have hc := invariant_integralCurve_mul_left (hExp.isMIntegralCurve v) (φ.symm z) t
  have hφ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm z * Exp (t • v)) :=
    mdifferentiableAt_extChartAt (by simpa only [φ, mfld_simps] using ht)
  let D : ℝ →L[ℝ] E :=
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm z * Exp (t • v)) : E →L[ℝ] E).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField v (φ.symm z * Exp (t • v)) : E))
  have hfd : HasFDerivAt (fun s => φ (φ.symm z * Exp (s • v))) D t := by
    apply (hasMFDerivAt_iff_hasFDerivAt).mp
    exact hφ.hasMFDerivAt.comp t hc
  have hd := hfd.hasDerivAt
  have he : chartInvariantFrame (1 : G) (φ (φ.symm z * Exp (t • v))) v =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm z * Exp (t • v)))
        (mulInvariantVectorField v (φ.symm z * Exp (t • v))) :=
    chartVectorField_apply_chart (1 : G) (mulInvariantVectorField v) ht
  dsimp only [chartExponentialFlow] at ⊢
  rw [he]
  change HasDerivAt (fun s => φ (φ.symm z * Exp (s • v)))
    ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm z * Exp (t • v)) : E →L[ℝ] E)
      ((1 : ℝ) • (mulInvariantVectorField v (φ.symm z * Exp (t • v)) : E))) t at hd
  rw [one_smul] at hd
  exact hd

theorem fderiv_chartExponentialFlow_time
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : E) {q : ℝ × E} (hq : DifferentiableAt ℝ (chartExponentialFlow Exp v) q)
    (ht : (extChartAt (𝓘(ℝ, E)) (1 : G)).symm q.2 * Exp (q.1 • v) ∈
      (extChartAt (𝓘(ℝ, E)) (1 : G)).source) :
    fderiv ℝ (chartExponentialFlow Exp v) q (1, 0) =
      (1, chartInvariantFrame (1 : G) (chartExponentialFlow Exp v q).2 v) := by
  rw [fderiv_prod_apply_fst hq]
  have hd := (hasFDerivAt_id (𝕜 := ℝ) q.1).prodMk
    (hasDerivAt_chartExponentialFlow_time hExp v q.1 q.2 ht).hasFDerivAt
  dsimp only [chartExponentialFlow, id_eq] at hd ⊢
  rw [hd.fderiv]
  simp

theorem fderiv_chartExponentialFlow_field
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (v w : E) {q : ℝ × E}
    (hq : DifferentiableAt ℝ (chartExponentialFlow Exp v) q)
    (hz : q.2 ∈ (extChartAt (𝓘(ℝ, E)) (1 : G)).target)
    (ht : (extChartAt (𝓘(ℝ, E)) (1 : G)).symm q.2 * Exp (q.1 • v) ∈
      (extChartAt (𝓘(ℝ, E)) (1 : G)).source) :
    fderiv ℝ (chartExponentialFlow Exp v) q
      (0, chartInvariantFrame (1 : G) q.2
        (conjugationDifferentialHom (E := E) (Exp (q.1 • v)) w)) =
      (0, chartInvariantFrame (1 : G) (chartExponentialFlow Exp v q).2 w) := by
  rw [fderiv_prod_apply_snd hq]
  have hp : DifferentiableAt ℝ (fun z : E => chartExponentialFlow Exp v (q.1, z)) q.2 :=
    hq.comp q.2 (f := fun z : E => (q.1, z))
      ((differentiableAt_const q.1).prodMk differentiableAt_id)
  have hsp : DifferentiableAt ℝ (fun z : E => (chartExponentialFlow Exp v (q.1, z)).2) q.2 := hp.snd
  have hd := (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2).prodMk hsp.hasFDerivAt
  dsimp only [Function.comp_def, chartExponentialFlow] at hd ⊢
  rw [hd.fderiv]
  change (0, fderiv ℝ (fun y => extChartAt (𝓘(ℝ, E)) (1 : G)
    ((extChartAt (𝓘(ℝ, E)) (1 : G)).symm y * Exp (q.1 • v))) q.2
    (chartInvariantFrame (1 : G) q.2
      (conjugationDifferentialHom (E := E) (Exp (q.1 • v)) w))) = _
  rw [chart_rightTranslation_related (Exp (q.1 • v)) w hz ht]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialGoodCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative mass is unchanged by the actual translated exponential chart -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L E G I : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] [SimplyConnectedSpace G] in
/-- The translated exponential coordinate map preserves Borel measurability
of every independently selected good subset. -/
theorem measurableEmbedding_translated_exponential_basis
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (k : G) :
    MeasurableEmbedding (fun y => ((Exp ∘ e) ∘ b.equivFun.symm) y * k) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let b' := b.map e.toLinearEquiv
  let c : (Fin n → ℝ) ≃ₜ G :=
    b'.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have he : ((Exp ∘ e) ∘ b.equivFun.symm) = c := by
    funext y
    dsimp only [c, Function.comp_apply, Homeomorph.trans_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, LinearEquiv.coe_toContinuousLinearEquiv]
    rw [hchart, Basis.map_equivFun]
    rfl
  rw [he]
  exact (MeasurableEquiv.mulRight k).measurableEmbedding.comp c.measurableEmbedding

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialCellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive finite mass of the actual translated exponential cells -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

/-- The finite-dimensional closed coordinate cube has positive finite mass. -/
theorem coordinate_cube_mass {n : ℕ} {R : ℝ} (hR : 0 < R) :
    volume (Icc (fun _ : Fin n => -R) (fun _ => R)) ≠ 0 ∧
      volume (Icc (fun _ : Fin n => -R) (fun _ => R)) ≠ ∞ := by
  rw [Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith : 0 ≤ 2 * R)]
  exact ⟨(ENNReal.ofReal_pos.mpr (pow_pos (by linarith) n)).ne', ENNReal.ofReal_ne_top⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialIdeal
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariance of Lie ideals under adjoint exponentials

Closed subspaces invariant under an operator are invariant under its
exponential, by the convergent power series. Together with the already
proved conjugation formula in a faithful representation, this proves
normality for the exponential images used by the Cartan construction.
-/

noncomputable section
namespace PolycyclicRecognition

section Operator

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem exp_apply_mem_of_stable (U : Submodule ℝ V) (hU : IsClosed (U : Set V))
    (A : V →L[ℝ] V) (hA : ∀ v ∈ U, A v ∈ U) {v : V} (hv : v ∈ U) :
    NormedSpace.exp A v ∈ U := by
  have hp (n : ℕ) : (A ^ n) v ∈ U := by
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      rw [pow_succ']
      exact hA _ ih
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map
    (ContinuousLinearMap.apply ℝ V v) (ContinuousLinearMap.apply ℝ V v).continuous
  have hs' : HasSum (fun n : ℕ => (n.factorial⁻¹ : ℝ) • (A ^ n) v)
      (NormedSpace.exp A v) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, smul_apply] using hs
  rw [← hs'.tsum_eq]
  exact tsum_mem hU fun n => U.smul_mem _ (hp n)

end Operator

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of exponential curves

Coordinates of the second kind require only smoothness of each individual
one-parameter subgroup. Their differential at zero is the sum of the
specified tangent vectors.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

def exponentialProduct (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) :
    {n : ℕ} → (Fin n → E) → (Fin n → ℝ) → G
  | 0, _, _ => 1
  | _ + 1, v, x => Exp (x 0 • v 0) * exponentialProduct Exp (v ∘ Fin.succ) (x ∘ Fin.succ)

def tangentCombination {n : ℕ} (v : Fin n → E) :
    (Fin n → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (v i)

@[simp] theorem tangentCombination_apply {n : ℕ}
    (v : Fin n → E) (x : Fin n → ℝ) :
    tangentCombination v x = ∑ i, x i • v i := by
  simp only [tangentCombination, sum_apply]
  rfl

def coordinateTail (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

@[simp] theorem coordinateTail_apply (n : ℕ) (x : Fin (n + 1) → ℝ) :
    coordinateTail n x = x ∘ Fin.succ := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialQuotientSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected pure-word section in actual exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {V J EN EQ N Q : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype J]
  [AddCommGroup EN] [Module ℝ EN] [TopologicalSpace EN]
  [IsTopologicalAddGroup EN] [ContinuousSMul ℝ EN]
  [AddCommGroup EQ] [Module ℝ EQ] [TopologicalSpace EQ] [T2Space EQ]
  [IsTopologicalAddGroup EQ] [ContinuousSMul ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace N] [TopologicalSpace Q] [Group N] [Group Q]
  (U : LieIdeal ℝ V) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)
  (eN : V ≃ₗ[ℝ] EN) (eQ : (V ⧸ U.toSubmodule) ≃ₗ[ℝ] EQ)
  (chartN : EN ≃ₜ N) (chartQ : EQ ≃ₜ Q)

/-- The prescribed linear quotient section, transported through the two
actual global exponential charts. -/
def exponentialQuotientSection : C(Q, N) :=
  let σ := (eN.toLinearMap.comp (quotientLinearSection U bQ lift)).comp eQ.symm.toLinearMap
  ⟨fun q => chartN (σ (chartQ.symm q)),
    chartN.continuous.comp (σ.continuous_of_finiteDimensional.comp chartQ.symm.continuous)⟩

omit [Fintype J] [Group N] [Group Q] in
@[simp] theorem exponentialQuotientSection_apply (q : V ⧸ U.toSubmodule) :
    exponentialQuotientSection U bQ lift eN eQ chartN chartQ (chartQ (eQ q)) =
      chartN (eN (quotientLinearSection U bQ lift q)) := by
  simp [exponentialQuotientSection]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieAdjointSmoothness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness of the actual adjoint action

Conjugation fixes the identity, so its parameter-dependent derivative has
constant source and target tangent spaces. The general derivative theorem
therefore gives smoothness in the ordinary operator norm.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Function
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

def adjointLinearMap (g : G) : E →L[ℝ] E :=
  conjugationDifferentialHom (E := E) g

theorem contMDiff_conjugationDifferentialHom :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E →L[ℝ] E)) ∞
      (adjointLinearMap (E := E) (G := G)) := by
  let c : G → G → G := fun g h => g * h * g⁻¹
  have hc : ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞ (uncurry c) :=
    (contMDiff_fst.mul contMDiff_snd).mul contMDiff_fst.inv
  intro g₀
  have h := (hc (g₀, 1)).mfderiv c (fun _ : G => (1 : G))
    (m := ∞) contMDiffAt_const (by simp)
  have heq : inTangentCoordinates (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (fun _ : G => (1 : G)) (fun g => c g 1)
      (fun g => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (c g) 1) g₀ =
      (adjointLinearMap (E := E) (G := G)) := by
    funext g
    rw [inTangentCoordinates_eq_mfderiv_comp]
    · have hrange : range (𝓘(ℝ, E)) = (univ : Set E) := by ext z; simp
      rw [hrange, mfderivWithin_univ]
      change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) (c g₀ 1))
          (c g 1) : E →L[ℝ] E).comp
          ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (c g) 1 : E →L[ℝ] E).comp
            (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) (1 : G)).symm
              (extChartAt (𝓘(ℝ, E)) (1 : G) 1) : E →L[ℝ] E)) = adjointLinearMap (E := E) g
      rw [show c g₀ 1 = 1 by simp [c], show c g 1 = 1 by simp [c],
        mfderiv_extChartAt_self, mfderiv_chart_symm_base]
      exact ContinuousLinearMap.ext fun _ => rfl
    · exact mem_chart_source _ _
    · simpa only [c, mul_one, mul_inv_cancel] using mem_chart_source E (1 : G)
  rw [heq] at h
  exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicAdjointDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The infinitesimal adjoint action

Right exponential flow transports a left-invariant field by conjugation.
Naturality of brackets on time times a chart identifies its derivative
with the intrinsic Lie bracket, without a linear representation.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function
open scoped Manifold ContDiff Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem hasDerivAt_adjoint_exponential_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    HasDerivAt (fun t : ℝ => adjointLinearMap (E := E) (Exp (t • v)) w)
      (⁅v, w⁆ : GroupLieAlgebra (𝓘(ℝ, E)) G) 0 := by
  let φ := extChartAt (𝓘(ℝ, E)) (1 : G)
  let z₀ : E := φ 1
  let X : E → E := fun z => chartInvariantFrame (1 : G) z v
  let Y : E → E := fun z => chartInvariantFrame (1 : G) z w
  let A : ℝ → E := fun t => adjointLinearMap (E := E) (Exp (t • v)) w
  let Z : ℝ × E → E := fun q => chartInvariantFrame (1 : G) q.2 (A q.1)
  let F := chartExponentialFlow Exp v
  have hAC : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun t : ℝ => adjointLinearMap (E := E) (Exp (t • v))) :=
    contMDiff_conjugationDifferentialHom.comp (hExp.contMDiff_curve v)
  have hA : DifferentiableAt ℝ A 0 :=
    (hAC.contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).clm_apply (differentiableAt_const w)
  have hZ : DifferentiableAt ℝ Z (0, z₀) :=
    differentiableAt_chartInvariantFrame_parameter hA (1 : G)
  have hX : DifferentiableAt ℝ X z₀ := differentiableAt_chartInvariantFrame_apply (E := E) (1 : G) v
  have hY : DifferentiableAt ℝ Y z₀ := differentiableAt_chartInvariantFrame_apply (E := E) (1 : G) w
  have hFsmooth : ContDiffAt ℝ ∞ F (0, z₀) := contDiffAt_chartExponentialFlow (E := E) hExp v
  have hF : ContDiffAt ℝ 2 F (0, z₀) := hFsmooth.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hbase : F (0, z₀) = (0, z₀) :=
    chartExponentialFlow_zero hExp v (mem_extChartAt_target (I := 𝓘(ℝ, E)) (1 : G))
  have hvertical : ∀ u, fderiv ℝ F (0, z₀) (0, u) = (0, u) :=
    fderiv_chartExponentialFlow_vertical_zero (E := E) hExp v
  have hdiff : ∀ᶠ q in 𝓝 (0, z₀), DifferentiableAt ℝ F q :=
    ((hFsmooth.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num)).mono
      fun _ hq => hq.differentiableAt (by norm_num)
  have htarget : ∀ᶠ q : ℝ × E in 𝓝 (0, z₀), q.2 ∈ φ.target := by
    have ht : φ.target ∈ 𝓝 z₀ := by
      simpa only [φ, z₀, mfld_simps, nhdsWithin_univ] using
        extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) (1 : G)
    exact continuous_snd.continuousAt.preimage_mem_nhds ht
  have hi : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ.symm z₀ := by
    simpa only [φ, z₀, mfld_simps, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, E)) (n := ∞) (1 : G))
  have hs : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, E)) ∞ Prod.snd ((0 : ℝ), z₀) :=
    contDiffAt_snd.contMDiffAt
  have ht : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, ℝ)) ∞ Prod.fst ((0 : ℝ), z₀) :=
    contDiffAt_fst.contMDiffAt
  have hc : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (fun t : ℝ => Exp (t • v)) 0 :=
    (hExp.contMDiff_curve v) 0
  have hct : ContMDiffAt (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, E)) ∞
      (fun q : ℝ × E => Exp (q.1 • v)) ((0 : ℝ), z₀) :=
    hc.comp ((0 : ℝ), z₀) (f := fun q : ℝ × E => q.1) ht
  have hmul := (hi.comp ((0 : ℝ), z₀) hs).mul hct
  have hsource : ∀ᶠ q : ℝ × E in 𝓝 (0, z₀), φ.symm q.2 * Exp (q.1 • v) ∈ φ.source := by
    have hb : φ.symm z₀ * Exp ((0 : ℝ) • v) = 1 := by
      simp only [z₀, φ, extChartAt_to_inv, zero_smul, hExp.map_zero, one_mul]
    have hn : φ.source ∈ 𝓝 (φ.symm z₀ * Exp ((0 : ℝ) • v)) := by
      rw [hb]
      exact extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (1 : G)
    exact hmul.continuousAt.preimage_mem_nhds hn
  have htime : ∀ᶠ q in 𝓝 (0, z₀), fderiv ℝ F q (1, 0) = (1, X (F q).2) := by
    filter_upwards [hdiff, hsource] with q hq hsrc
    exact fderiv_chartExponentialFlow_time (E := E) hExp v hq hsrc
  have hfield : ∀ᶠ q in 𝓝 (0, z₀), fderiv ℝ F q (0, Z q) = (0, Y (F q).2) := by
    filter_upwards [hdiff, htarget, hsource] with q hq htar hsrc
    exact fderiv_chartExponentialFlow_field (E := E) v w hq htar hsrc
  have hb := transportedField_time_derivative hF hZ hX hY hbase hvertical htime hfield
  have hbr : VectorField.lieBracket ℝ X Y z₀ =
      (⁅v, w⁆ : GroupLieAlgebra (𝓘(ℝ, E)) G) :=
    (mlieBracket_eq_chartBracket (mulInvariantVectorField v) (mulInvariantVectorField w)
      (1 : G)).symm
  rw [hbr] at hb
  have hj := (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) z₀ (0 : ℝ))
  have hd := (hZ.hasFDerivAt.comp (0 : ℝ) hj).hasDerivAt
  change HasDerivAt (fun t : ℝ => Z (t, z₀)) (fderiv ℝ Z (0, z₀) (1, 0)) 0 at hd
  rw [hb] at hd
  have heq : (fun t : ℝ => Z (t, z₀)) = A := by
    funext t
    dsimp only [Z, z₀]
    rw [chartInvariantFrame_one]
    rfl
  rw [heq] at hd
  exact hd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicAdjointExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The adjoint exponential without a faithful representation -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The intrinsic bracket, viewed as a continuous operator on the model space. -/
def groupAdjointOperator (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : E →L[ℝ] E :=
  let d : E →ₗ[ℝ] E := LieModule.toEnd ℝ
    (GroupLieAlgebra (𝓘(ℝ, E)) G) (GroupLieAlgebra (𝓘(ℝ, E)) G) v
  d.toContinuousLinearMap

@[simp] theorem groupAdjointOperator_apply (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    groupAdjointOperator (E := E) v w = ⁅v, w⁆ := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem adjointLinearMap_one :
    adjointLinearMap (E := E) (1 : G) = 1 :=
  (conjugationDifferentialHom (E := E)).map_one

omit [FiniteDimensional ℝ E] in
theorem adjointLinearMap_mul (a b : G) :
    adjointLinearMap (E := E) (a * b) = adjointLinearMap (E := E) a * adjointLinearMap b :=
  (conjugationDifferentialHom (E := E)).map_mul a b

theorem adjointLinearMap_exponential
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (t : ℝ) :
    adjointLinearMap (E := E) (Exp (t • v)) =
      NormedSpace.exp (t • groupAdjointOperator (E := E) v) := by
  let C : ℝ → E →L[ℝ] E := fun s => adjointLinearMap (E := E) (Exp (s • v))
  have hC : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E →L[ℝ] E)) ∞ C :=
    contMDiff_conjugationDifferentialHom.comp (hExp.contMDiff_curve v)
  have hd : HasDerivAt C (deriv C 0) 0 := (hC.contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).hasDerivAt
  have he : deriv C 0 = groupAdjointOperator (E := E) v := by
    ext w
    have hp := hd.clm_apply (hasDerivAt_const (0 : ℝ) w)
    have hbr := hasDerivAt_adjoint_exponential_zero (E := E) hExp v w
    have hu := hp.unique hbr
    rw [map_zero, add_zero] at hu
    exact hu.trans (groupAdjointOperator_apply v w).symm
  rw [he] at hd
  have hzero : C 0 = 1 := by
    change adjointLinearMap (E := E) (Exp (0 • v)) = 1
    rw [zero_smul, hExp.map_zero, adjointLinearMap_one]
  have hadd (s u : ℝ) : C (s + u) = C s * C u := by
    change adjointLinearMap (E := E) (Exp ((s + u) • v)) = _
    rw [hExp.map_add_smul, adjointLinearMap_mul]
  exact oneParameter_eq_exp hzero hadd hd t

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieWordDifference
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite differences of Lie words along the lower central series

The nonlinear part of a bracket polynomial raises the filtration also for
finite differences, not just infinitesimal ones. This supports the explicit
inverse of a BCH translation.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

omit [LieAlgebra ℝ L] in
theorem lie_sub_lie_decomposition (x y z w : L) :
    ⁅x, y⁆ - ⁅z, w⁆ = ⁅x - z, y⁆ + ⁅z, y - w⁆ := by
  rw [sub_lie, lie_sub]
  abel

/-- The degree-one part of a word as a linear map in its input letters. -/
def wordLinearPart : FreeMagma I → (I → L) →ₗ[ℝ] L
  | .of i => LinearMap.proj i
  | .mul _ _ => 0

def finiteDynkinLinearPart {c n : ℕ} (coeff : DynkinCoefficients c n) :
    (Fin n → L) →ₗ[ℝ] L :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    coeff d w • wordLinearPart (rightNestedWord d.val w)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentCoordinateFlow
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent linear flows in changing box coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-- The polynomial is independent of a norm or coordinates on the algebra. -/
def finiteEndFlow (D : Module.End ℝ V) (k : ℕ) (t : ℝ) (v : V) : V :=
  ∑ p ∈ Finset.range k, ((p.factorial : ℝ)⁻¹ * t ^ p) • ((D ^ p) v)

theorem finiteEndFlow_map {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (D : Module.End ℝ V) (E : Module.End ℝ W)
    (hf : ∀ v, f (D v) = E (f v)) (k : ℕ) (t : ℝ) (v : V) :
    f (finiteEndFlow D k t v) = finiteEndFlow E k t (f v) := by
  have hp (p : ℕ) (v : V) : f ((D ^ p) v) = (E ^ p) (f v) := by
    induction p with
    | zero => rfl
    | succ p hp => rw [pow_succ', pow_succ', Module.End.mul_apply,
        Module.End.mul_apply, hf, hp]
  simp only [finiteEndFlow, map_sum, map_smul, hp]

theorem finiteEndFlow_eq_exp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] (D : Module.End ℝ U) {k : ℕ} (hD : D ^ k = 0)
    (t : ℝ) (v : U) : finiteEndFlow D k t v =
      NormedSpace.exp (t • Module.End.toContinuousLinearMap U D) v := by
  let e := Module.End.toContinuousLinearMap (𝕜 := ℝ) U
  have hzero : (t • e D) ^ k = 0 := by
    rw [smul_pow, ← map_pow, hD, map_zero, smul_zero]
  rw [exp_eq_finite_sum_of_pow_eq_zero _ hzero]
  simp only [finiteEndFlow, sum_apply, smul_apply, smul_pow, ← map_pow, smul_smul]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentDerivationFlow
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-parameter Lie automorphisms from a nilpotent derivation -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

local instance instModuleRat_solutions : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

local instance q145LieRatGeometryNilpotentDerivationFlow : LieAlgebra ℚ L where
  lie_smul t x y := lie_smul (algebraMap ℚ ℝ t) x y

def nilpotentDerivationFlow (t : ℝ) : L ≃ₗ⁅ℝ⁆ L :=
  (t • D).exp (by
    change IsNilpotent (t • D.toLinearMap)
    exact hD.smul t)

theorem nilpotentDerivationFlow_zero (x : L) : nilpotentDerivationFlow D hD 0 x = x := by
  change IsNilpotent.exp (0 • D.toLinearMap) x = x
  rw [zero_smul, IsNilpotent.exp_zero]
  rfl

theorem nilpotentDerivationFlow_add (s t : ℝ) (x : L) :
    nilpotentDerivationFlow D hD (s + t) x =
      nilpotentDerivationFlow D hD s (nilpotentDerivationFlow D hD t x) := by
  change IsNilpotent.exp ((s + t) • D.toLinearMap) x =
    IsNilpotent.exp (s • D.toLinearMap) (IsNilpotent.exp (t • D.toLinearMap) x)
  have hc : Commute (s • D.toLinearMap) (t • D.toLinearMap) := by
    change (s • D.toLinearMap) * (t • D.toLinearMap) =
      (t • D.toLinearMap) * (s • D.toLinearMap)
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm s t]
  rw [add_smul, IsNilpotent.exp_add_of_commute hc (hD.smul s) (hD.smul t)]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PositiveWeightCones
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive parts of the ray and two-generator cones -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The ray with its vertex omitted. Generator weights are nonzero. -/
def positiveWeightRay (α : V) : Set V := {β | ∃ c : ℝ, 0 < c ∧ β = c • α}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemisimpleLieLogarithm
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite power of a semisimple Lie automorphism has a derivation logarithm

The logarithm uses one additive character on the generated spectral group,
so the derivative respects every bracket relation.
-/

noncomputable section
namespace PolycyclicRecognition

/-- The analytic and Lie structures share their additive and scalar data. -/
class ComplexNormedLieAlgebra (L : Type*) extends NormedAddCommGroup L, LieRing L,
    NormedSpace ℂ L, LieAlgebra ℂ L

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangulableLieModel
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published reduction to a real-triangulable Lie model

Y. Cornulier and R. Tessera, *Geometric presentations of Lie groups and
their Dehn functions*, Publications Mathématiques de l'IHÉS 125 (2017),
79–219, Lemma 3.A.1, p.108, gives proper continuous homomorphisms with
cocompact images `G ← G₁ → G₂ ← G₃`, with `G₃` real triangulable.
Definition 1.1, p.83, identifies this last property with being isomorphic
to a closed connected group of invertible upper triangular real matrices.

The input below keeps precisely that topological reduction. Its metric
consequence is proved using the separately identified compatible-metric
existence input and the explicit inverse-map composition lemmas. No
adjoint basis, height control, or recognition conclusion is placed in the
published input.
-/

noncomputable section

namespace PolycyclicRecognition

/-- Only the locally compact group data used from an intermediate Lie
group in the CT reduction; the smooth structure is unnecessary here. -/
structure CompactlyGeneratedLCModel where
  carrier : Type
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [topologicalGroup : IsTopologicalGroup carrier]
  [t2Space : T2Space carrier]
  [locallyCompactSpace : LocallyCompactSpace carrier]
  [secondCountableTopology : SecondCountableTopology carrier]
  compactlyGenerated : ∃ K : Set carrier, IsCompact K ∧ Subgroup.closure K = ⊤

attribute [instance] CompactlyGeneratedLCModel.group CompactlyGeneratedLCModel.topologicalSpace
  CompactlyGeneratedLCModel.topologicalGroup CompactlyGeneratedLCModel.t2Space
  CompactlyGeneratedLCModel.locallyCompactSpace CompactlyGeneratedLCModel.secondCountableTopology

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightRotationCharacter
attribute [-instance] _root_.TangentSpace.instT2SpaceCompat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compact rotation character on the actual adjoint-weight quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped TensorProduct

variable {L : Type*}
  [LieRing L]
  [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  {n : ℕ}
  (H : LieSubalgebra ℝ L)
  [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

section Topology
variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

local instance characterCartanTopologicalAddGroup : IsTopologicalAddGroup H :=
  Submodule.topologicalAddGroup H.toSubmodule

end Topology
end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end


