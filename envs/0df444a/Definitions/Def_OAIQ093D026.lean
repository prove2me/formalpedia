-- Prove2me | Definitions.Def_OAIQ093D026
-- name    : OAIQ093D026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:15:05.005887+00:00
-- url     : https://prove2.me/theorems/ad4829f5-ea16-4cbe-b9d9-d4669726a1f3
-- title:
--   Definitions bundle OAIQ093D026 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 1 definition, 1 inductive type or structure and 4 theorems. The definitions and types are `OAI.PolycyclicRecognition.CartanWordModel.NeighborSamplingRow`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint.cartanComponent`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`PolycyclicRecognition_Algebra_ComplexFactorParameters`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/ComplexFactorParameters.lean), [`PolycyclicRecognition_Algebra_PolynomialCoordinateCurves`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/PolynomialCoordinateCurves.lean), [`PolycyclicRecognition_Geometry_CartanNeighborSamplingRow`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNeighborSamplingRow.lean), [`PolycyclicRecognition_Geometry_ExponentialBoxCoordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/ExponentialBoxCoordinates.lean), [`PolycyclicRecognition_Geometry_NilpotentLieModel`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/NilpotentLieModel.lean), [`PolycyclicRecognition_Geometry_WeightedBoxVolume`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/WeightedBoxVolume.lean).
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D007` and `OAIQ093D008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D016`, `OAIQ093D017` and `OAIQ093D018`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexFactorParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear parameters for the two actual complex-weight factors -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

def cartanComponent : L →ₗ[ℝ] H :=
  (T.cartanWeightSection H).comp T.weightMap.rangeRestrict

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedBoxVolume
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
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

/-- The exact coordinate-volume formula; in particular, the exponent is
the total weight of the selected basis. -/
theorem volume_weightedCoordinateBox (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (r L : ℝ) :
    volume (weightedCoordinateBox v w b r L) =
      ENNReal.ofReal |(columnBasisMatrix v b).det| *
        ENNReal.ofReal (Real.exp (r * columnBasisWeight w b)) *
          ENNReal.ofReal (2 * L) ^ n := by
  rw [weightedCoordinateBox, Measure.addHaar_image_linearMap,
    LinearMap.det_toLin', det_scaledColumnMatrix, abs_mul,
    abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)),
    Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ac_rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialBoxCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
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

/-- The group box is the exponential image of the exact weighted coordinate
box used by the determinant-volume theorem. -/
theorem exponentialCoordinateBox_eq_weighted_image
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X S)
    (cost : S → ℝ) (r R : ℝ) (hR : 0 ≤ R) (Exp : L → G) :
    exponentialCoordinateBox Exp
      (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun i => cost (β.val i)) r) R =
    (Exp ∘ b₀.equivFun.symm) '' weightedCoordinateBox
      (wordListCoordinates X S b₀) cost β.val r R := by
  rw [weightedCoordinateBox, scaledColumnMatrix_eq_basis_toMatrix,
    basis_image_cube _ _ R hR, ← Set.image_comp]
  ext g
  simp only [exponentialCoordinateBox, Set.mem_ofPred_eq, Set.mem_image,
    Function.comp_apply, b₀.equivFun.symm_apply_apply]
  constructor
  · rintro ⟨x, hx, hb⟩
    exact ⟨x, hb, hx⟩
  · rintro ⟨x, hb, hx⟩
    exact ⟨x, hx, hb⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentLieModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The simply connected nilpotent Lie models needed by Cartan factorization

J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013),
Theorem 20.21, p.531, gives the simply connected integration of a finite
dimensional real Lie algebra. For the nilpotent case, exponential coordinates
have a finite polynomial BCH law: F. Baudoin, *An Introduction to the Geometry
of Stochastic Flows* (2004), Appendix B.5–B.6, pp.123–126. These coordinates
give the analytic Lie-group model used here. No metric-growth, Haar-volume,
Cartan-factorization, or quasi-isometry conclusion is included in this input.

The universe of the model can be chosen to match the algebra by using its
finite-dimensional coordinate space (or a lifted copy).
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

universe u

namespace NilpotentLieModel

variable {L : Type u} [LieRing L] [LieAlgebra ℝ L] (M : NilpotentLieModel L)

/-- The separate published exponential theorem supplies an actual chart
on the chosen model. -/
theorem exists_exponential_chart (hnil : LieRing.IsNilpotent L)
    (haar : NilpotentExponentialHaarInput M.modelSpace M.carrier) :
    ∃ Exp : GroupLieAlgebra (𝓘(ℝ, M.modelSpace)) M.carrier → M.carrier,
      IsGroupExponential Exp ∧
      ∃ chart : GroupLieAlgebra (𝓘(ℝ, M.modelSpace)) M.carrier ≃ₜ M.carrier,
        ∀ x, chart x = Exp x := by
  have hn := M.tangent_nilpotent hnil
  obtain ⟨Exp, hExp⟩ := haar.1 hn
  exact ⟨Exp, hExp, (haar.2 Exp hExp hn).1⟩

end NilpotentLieModel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateCurves
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial scalar curves in polynomial group coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L J : Type*} [RealNormedLieAlgebra L] [Fintype J]
  (b : Module.Basis J ℝ L)

omit [Fintype J] in
theorem hasPolynomialLineCoordinates_const (v : L) : HasPolynomialLineCoordinates b (fun _ => v) :=
  fun j => polynomialFunctions_const (b.repr v j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanNeighborSamplingRow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original neighboring samples before their affine limit is identified -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [Fintype I] [DecidableEq I]
  (π : G →* Multiplicative W)
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (β : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (c B δ : ℝ)
  (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
  {Λ : ℝ≥0}

set_option maxHeartbeats 1000000 in
/-- Actual samples, root step and weak law, with no affine-limit premise. -/
structure NeighborSamplingRow where
  scale : ℕ → ℝ
  grows : Tendsto scale atTop atTop
  strict_mono : StrictMono scale
  scale_ge_one : ∀ n, 1 ≤ scale n
  pair : ℕ → NormalizedPair G Λ
  center : ℕ → G
  radius : ℕ → ℝ
  radius_nonneg : ∀ n, 0 ≤ radius n
  radius_subexponential : HasSubexponentialUpperBoundSeq scale radius
  base : ℕ → F.N.carrier
  step : ℕ → F.N.carrier
  base_mem : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
    ((fun w => (1 + δ) • w) '' cell) β (scale n) (radius n)
  step_mem : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
    ((fun w => (1 + δ) • w) '' cell) β (scale n) (radius n)
  mode : Fin M.letterCount
  time : ℕ → ℝ
  time_bound : ∀ n, |time n| ≤ radius n * Real.exp
    ((M.weight mode (pivot mode) + δ * B) * scale n)
  root_step : ∀ n, F.inclusionN (step n) =
    Exp (time n • (M.letter mode : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  profile : ℕ → F.N.carrier → Profiles
  measurable_profile : ∀ n, Measurable (profile n)
  actual : ∀ n q, q ∈ (fun v => v * base n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell β (scale n) 1 ∪
    (fun v => v * base n * step n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell β (scale n) 1 → ∀ z,
    (profile n q).val z = rescaledMapProfile
      (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
      (max (Real.log (scale n)) 0)
      (F.profileChart (exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0))) z
  law : ProbabilityMeasure (Profiles × Profiles)
  converges : Tendsto (fun n => ProbabilityMeasure.map
    (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN bN
      cell β (scale n) (base n)) (f := (fun q => (profile n q, profile n (q * step n)))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      atTop (𝓝 law)
  point : Profiles × Profiles
  supported : point ∈ (law : Measure (Profiles × Profiles)).support

end PolycyclicRecognition.CartanWordModel

end

end OAI
end


