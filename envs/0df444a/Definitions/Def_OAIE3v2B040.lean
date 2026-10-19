-- Prove2me | Definitions.Def_OAIE3v2B040
-- name    : OAIE3v2B040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:12:47.773178+00:00
-- url     : https://prove2.me/theorems/c0f08f4c-4c7d-4620-a20b-991cb0682c74
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 41 of 311
-- statement:
--   Definitions bundle 41 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B005` of this split.
--
--   Modules: `Dynamics/FlatPatchReset.lean`, `Estimates/CircleFejerAverage.lean`, `Estimates/DependentPatchValue.lean`, `Estimates/FreeLieTreeCoefficientBounds.lean`, `Estimates/FreePrimitiveCriterion.lean`, `Estimates/FrozenCosetVariation.lean`, `Estimates/IteratedCircleAverageIntegral.lean`, `Estimates/NativeGraphSmallDifference.lean`, `Estimates/NativeResidualMultiplier.lean`, `Estimates/PeriodicIsometricAction.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/SquarefreeExponents.lean`, `Estimates/SquarefreeSplitCount.lean`, `Estimates/WeightedPatchReparam.lean`, `Fourier/CircleActionFourierMetric.lean`, `Fourier/RectangularGridCharacter.lean`, `Geometry/AuxiliaryBoxPartition.lean`, `Geometry/CommonStrideCoordinates.lean`, `Geometry/CoordinateQuotientModel.lean`, `Geometry/RightCosetMetricMap.lean`, `Geometry/SupportedSubquotient.lean`, `Geometry/WeightedTranslationIntegralCoordinates.lean`, `Lattices/BufferedIntegerLift.lean`, `Lattices/ComparableResidueProgressionPartition.lean`, `Lattices/FactorialIntegerScalars.lean`, `Lattices/IntegerBoxCoordinateEquiv.lean`, `Lattices/ResidueEventOrDescent.lean`, `Lattices/ResidueStrideRebase.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Linear/BasisProjectionRealification.lean`, `Linear/WeightedParameterPatchRankPadding.lean`, `Nilpotent/BCHQuotientLocalIsometry.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/PolynomialPatchProductBudget.lean`, `Polynomial/PolynomialTranslationActionCompatibility.lean`, `Polynomial/PolynomialTranslationSeries.lean`, `Polynomial/RealPolynomialMassBox.lean`, `Polynomial/SquarefreeBlockDegree.lean`, `Sampling/IntegralGridFunctional.lean`.
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
import Definitions.Def_OAIE3v2B005

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace TriangularSlots

variable {d : ℕ}

theorem integer_unique (A : TriangularSlots d) {b c : Fin d → ℤ} {r t : ℝ}
    (hgap : r + t < 1)
    (hb : ∀ i, |A.residual b i| ≤ r) (hc : ∀ i, |A.residual c i| ≤ t) : b = c := by
  have hall : ∀ n : ℕ, ∀ i : Fin d, i.val = n → b i = c i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      have hcenter : A.center (fun j => (b j : ℝ)) i = A.center (fun j => (c j : ℝ)) i := by
        apply A.lower
        intro j hj
        have hjn : j.val < n := by simpa only [Fin.lt_def, ← hi] using hj
        rw [ih j.val hjn j rfl]
      have heq : ((b i - c i : ℤ) : ℝ) = A.residual b i - A.residual c i := by
        simp only [residual, Int.cast_sub, hcenter]
        ring
      have habs : |((b i - c i : ℤ) : ℝ)| < 1 := by
        rw [heq]
        exact (abs_sub _ _).trans_lt ((add_le_add (hb i) (hc i)).trans_lt hgap)
      have hl : (-1 : ℤ) < b i - c i := by exact_mod_cast (abs_lt.mp habs).1
      have hr : b i - c i < (1 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
      omega
  exact funext (fun i => hall i.val i rfl)

end TriangularSlots

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FlatPatchReset
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

def constantSlots {d : ℕ} (x : Fin d → ℝ) : TriangularSlots d where
  center _ := x
  lower _ _ _ _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

abbrev circleHaar : Measure Circle := AddCircle.haarAddCircle

end
end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CircleFejerAverage
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators

theorem circle_integrable_of_continuous {E : Type*} [NormedAddCommGroup E]
    {f : Circle → E} (hf : Continuous f) : Integrable f circleHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreePrimitiveCriterion
namespace OAI

section

namespace Erdos3
open TensorProduct
variable {X : Type*}

theorem FreePrimitive.smul {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) (r : ℚ) :
    FreePrimitive (r • p) := by
  unfold FreePrimitive at hp ⊢
  simp only [map_smul, hp, smul_add, smul_tmul', tmul_smul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

namespace FreeCoefficientBound

variable {s D E M N : ℕ} {p q : FreeAlgebra ℚ X}

theorem smul {r : ℚ} {a : ℤ} (hp : FreeCoefficientBound s D M p)
    (ha : (a : ℚ) = (E : ℚ) * r) (hbound : a.natAbs ≤ N) :
    FreeCoefficientBound s (E * D) (N * M) (r • p) := by
  intro w hw
  obtain ⟨b, hb, hbM⟩ := hp w hw
  refine ⟨a * b, ?_, ?_⟩
  · simp only [Int.cast_mul, Nat.cast_mul, map_smul, Finsupp.smul_apply, smul_eq_mul, ha, hb]
    ring
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul hbound hbM

end FreeCoefficientBound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RightCosetMetricMap
namespace OAI

section

namespace Erdos3

open _root_.Set

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem rightCosetMetricSpace_edist_mk (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) (x y : G) :
    letI := rightCosetMetricSpace Γ hΓ
    edist (QuotientGroup.mk x : G ⧸ Γ) (QuotientGroup.mk y) = ⨅ γ : Γ, edist x (y * γ) := rfl

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G H : Type*} [Group G] [Group H]

variable [PseudoEMetricSpace G] [PseudoEMetricSpace H]

theorem rightCosetEDist_map_le (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) {C : ℝ≥0} (hLip : LipschitzWith C φ) (x y : G) :
    rightCosetEDist Λ (φ x) (φ y) ≤ C * rightCosetEDist Γ x y := by
  unfold rightCosetEDist
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro γ
  let δ : Λ := ⟨φ γ, hφ γ.property⟩
  calc
    (⨅ a : Λ, edist (φ x) (φ y * a)) ≤ edist (φ x) (φ y * δ) := iInf_le _ δ
    _ = edist (φ x) (φ (y * γ)) := by simp only [δ, map_mul]
    _ ≤ C * edist x (y * γ) := hLip x (y * γ)

variable [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]

theorem quotientRightEDist_map_le (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) {C : ℝ≥0} (hLip : LipschitzWith C φ) (x y : G ⧸ Γ) :
    quotientRightEDist Λ (cosetMap Γ Λ φ hφ x) (cosetMap Γ Λ φ hφ y) ≤
      C * quotientRightEDist Γ x y :=
  Quotient.inductionOn₂ x y (rightCosetEDist_map_le Γ Λ φ hφ hLip)

end Erdos3

namespace Erdos3

open scoped NNReal

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

theorem lipschitz_cosetMap (Γ : Subgroup G) (Λ : Subgroup H)
    (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
    (φ : G →* H) (hφ : Γ ≤ Λ.comap φ) {C : ℝ≥0} (hLip : LipschitzWith C φ) :
    letI := rightCosetMetricSpace Γ hΓ
    letI := rightCosetMetricSpace Λ hΛ
    LipschitzWith C (cosetMap Γ Λ φ hφ) := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  intro x y
  exact quotientRightEDist_map_le Γ Λ φ hφ hLip x y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenCosetVariation
namespace OAI

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G : Type*} [Group G] [PseudoEMetricSpace G]

theorem rightCosetEDist_left_mul_le (Γ : Subgroup G) (a : G) {C : ℝ≥0}
    (hLip : LipschitzWith C (fun x => a * x)) (x y : G) :
    rightCosetEDist Γ (a * x) (a * y) ≤ C * rightCosetEDist Γ x y := by
  unfold rightCosetEDist
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro γ
  apply (iInf_le (fun δ : Γ => edist (a * x) (a * y * δ)) γ).trans
  simpa only [mul_assoc] using hLip x (y * γ)

variable [IsIsometricSMul Gᵐᵒᵖ G]

theorem quotientRightEDist_left_smul_le (Γ : Subgroup G) (a : G) {C : ℝ≥0}
    (hLip : LipschitzWith C (fun x => a * x)) (x y : G ⧸ Γ) :
    quotientRightEDist Γ (a • x) (a • y) ≤ C * quotientRightEDist Γ x y :=
  Quotient.inductionOn₂ x y (rightCosetEDist_left_mul_le Γ a hLip)

theorem quotientRightEDist_orbit_le (Γ : Subgroup G) (x : G ⧸ Γ) (a b : G) :
    quotientRightEDist Γ (a • x) (b • x) ≤ edist a b := by
  induction x using Quotient.inductionOn with
  | h x =>
    exact (quotientRightEDist_mk_le Γ (a * x) (b * x)).trans_eq (edist_mul_right a b x)

end Erdos3

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem lipschitz_quotient_left_smul (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (a : G) {C : ℝ≥0} (hLip : LipschitzWith C (fun x => a * x)) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith C (fun x : G ⧸ Γ => a • x) := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y
  exact quotientRightEDist_left_smul_le Γ a hLip x y

theorem lipschitz_quotient_orbit (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) (x : G ⧸ Γ) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith 1 (fun a : G => a • x) := by
  let := rightCosetMetricSpace Γ hΓ
  intro a b
  change quotientRightEDist Γ (a • x) (b • x) ≤ 1 * edist a b
  simpa only [one_mul] using quotientRightEDist_orbit_le Γ x a b

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G X : Type*} [Group G] [MetricSpace G]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G] [PseudoEMetricSpace X]

theorem rightCosetMetricSpace_lipschitz_lift (Γ : Subgroup G)
    (hΓ : IsClosed (Γ : Set G)) (f : G ⧸ Γ → X) {C : ℝ≥0}
    (hf : LipschitzWith C (fun x : G => f (QuotientGroup.mk x))) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith C f := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      rw [rightCosetMetricSpace_edist_mk, ENNReal.mul_iInf (by simp)]
      apply le_iInf
      intro γ
      simpa only [quotient_mk_mul_mem] using hf x (y * γ)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G]

variable [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem isometry_quotient_central_smul (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (g : G) (hc : ∀ a : G, Commute g a) :
    letI := rightCosetMetricSpace Γ hΓ
    Isometry (fun x : G ⧸ Γ => g • x) := by
  let := rightCosetMetricSpace Γ hΓ
  have hgroup : LipschitzWith 1 (fun a : G => g * a) := by
    have heq : (fun a : G => g * a) = (fun a : G => a * g) := funext (fun a => (hc a).eq)
    rw [heq]
    exact (isometry_mul_right g).lipschitz
  have hinv : LipschitzWith 1 (fun a : G => g⁻¹ * a) := by
    have heq : (fun a : G => g⁻¹ * a) = (fun a : G => a * g⁻¹) :=
      funext (fun a => (hc a).inv_left.eq)
    rw [heq]
    exact (isometry_mul_right g⁻¹).lipschitz
  have hforward := lipschitz_quotient_left_smul Γ hΓ g hgroup
  have hback := lipschitz_quotient_left_smul Γ hΓ g⁻¹ hinv
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · simpa only [NNReal.coe_one, one_mul] using hforward.dist_le_mul x y
  · simpa only [inv_smul_smul, NNReal.coe_one, one_mul] using hback.dist_le_mul (g • x) (g • y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CircleActionFourierMetric
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {X : Type*} [AddAction Circle X]

noncomputable def circleFourierComponent (n : ℤ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ t : Circle, character ((-n) • t) * f (t +ᵥ x) ∂circleHaar

theorem norm_circleFourierComponent_le (n : ℤ) (f : X → ℂ) {B : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖circleFourierComponent n f x‖ ≤ B := by
  apply (norm_integral_le_integral_norm _).trans
  have h := integral_mono_of_nonneg
    (ae_of_all circleHaar (fun t : Circle => norm_nonneg (character ((-n) • t) * f (t +ᵥ x))))
    (integrable_const B) (ae_of_all circleHaar (fun t : Circle => by
      simpa only [norm_mul, norm_character, one_mul] using hB (t +ᵥ x)))
  simpa using h

variable [TopologicalSpace X] [ContinuousVAdd Circle X]

theorem integrable_circleFourierComponent (n : ℤ) {f : X → ℂ} (hf : Continuous f) (x : X) :
    Integrable (fun t : Circle => character ((-n) • t) * f (t +ᵥ x)) circleHaar := by
  exact circle_integrable_of_continuous
    ((fourier (-n)).continuous.mul (hf.comp (continuous_id.vadd continuous_const)))

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X] [AddAction Circle X] [ContinuousVAdd Circle X]

theorem lipschitz_circleFourierComponent (n : ℤ) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hact : ∀ t : Circle, Isometry (fun x : X => t +ᵥ x)) :
    LipschitzWith L (circleFourierComponent n f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  unfold circleFourierComponent
  rw [← integral_sub (integrable_circleFourierComponent n hf.continuous x)
    (integrable_circleFourierComponent n hf.continuous y)]
  apply (norm_integral_le_integral_norm _).trans
  have hpoint (t : Circle) :
      ‖character ((-n) • t) * f (t +ᵥ x) - character ((-n) • t) * f (t +ᵥ y)‖ ≤
        (L : ℝ) * dist x y := by
    rw [← mul_sub, norm_mul, norm_character, one_mul, ← dist_eq_norm]
    exact (hf.dist_le_mul _ _).trans_eq (by rw [(hact t).dist_eq])
  have h := integral_mono_of_nonneg
    (ae_of_all circleHaar (fun t : Circle => norm_nonneg
      (character ((-n) • t) * f (t +ᵥ x) - character ((-n) • t) * f (t +ᵥ y))))
    (integrable_const ((L : ℝ) * dist x y)) (ae_of_all circleHaar hpoint)
  simpa using h

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeriodicIsometricAction
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X : Type*} [AddAction Circle X]

noncomputable def fejerComponent (N : ℕ) (h : ℤ) (f : X → ℂ) (x : X) : ℂ :=
  (fejerCoefficient N h : ℂ) * circleFourierComponent (-h) f x

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal BigOperators

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

theorem toContinuousVAdd (A : IsometricCircleAction X) :
    letI := A.toAddAction
    ContinuousVAdd Circle X := by
  let := A.toAddAction
  exact ⟨A.continuous_act⟩

noncomputable def component (A : IsometricCircleAction X) (N : ℕ) (h : ℤ) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  fejerComponent N h f

end IsometricCircleAction
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open Function
open scoped NNReal

variable {X : Type*}

noncomputable def periodicFlowAct (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (t : Circle) (x : X) : X :=
  (hper x).lift t

theorem periodicFlowAct_coe (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (r : ℝ) (x : X) :
    periodicFlowAct flow hper (r : Circle) x = flow r x := (hper x).lift_coe r

theorem periodicFlowAct_zero (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (hzero : ∀ x, flow 0 x = x) (x : X) :
    periodicFlowAct flow hper 0 x = x := by
  change periodicFlowAct flow hper ((0 : ℝ) : Circle) x = x
  rw [periodicFlowAct_coe, hzero]

theorem periodicFlowAct_add (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1)
    (hadd : ∀ r t x, flow (r + t) x = flow r (flow t x)) (t u : Circle) (x : X) :
    periodicFlowAct flow hper (t + u) x = periodicFlowAct flow hper t (periodicFlowAct flow hper u x) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective u
  rw [← QuotientAddGroup.mk_add]
  simp only [periodicFlowAct_coe, hadd]

variable [PseudoMetricSpace X]

theorem periodicFlowAct_isometry (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (hiso : ∀ r, Isometry (flow r)) (t : Circle) :
    Isometry (periodicFlowAct flow hper t) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  have heq : periodicFlowAct flow hper (r : Circle) = flow r := funext (periodicFlowAct_coe flow hper r)
  rw [heq]
  exact hiso r

theorem periodicFlowAct_displacement (flow : ℝ → X → X)
    (hper : ∀ x, Periodic (fun r => flow r x) 1) (D : ℝ≥0)
    (hbound : ∀ r x, dist (flow r x) x ≤ D * |r|) (t : Circle) (x : X) :
    dist (periodicFlowAct flow hper t x) x ≤ D * ‖t‖ := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  have heq : periodicFlowAct flow hper (r : Circle) x = flow (r - round r) x := by
    rw [show (r : Circle) = ((r - round r : ℝ) : Circle) by simp [sub_eq_add_neg]]
    exact periodicFlowAct_coe flow hper _ x
  rw [heq, UnitAddCircle.norm_eq]
  exact hbound _ x

theorem circleAct_joint_lipschitz (act : Circle → X → X)
    (_hzero : ∀ x, act 0 x = x) (hadd : ∀ t u x, act (t + u) x = act t (act u x))
    (hiso : ∀ t, Isometry (act t)) (D : ℝ≥0)
    (hbound : ∀ t x, dist (act t x) x ≤ D * ‖t‖) :
    LipschitzWith (D + 1) (fun p : Circle × X => act p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨t, x⟩ ⟨u, y⟩
  have htime : dist (act t y) (act u y) ≤ D * dist t u := by
    calc
      dist (act t y) (act u y) = dist (act u (act (t - u) y)) (act u y) := by
        rw [← hadd, show u + (t - u) = t by abel]
      _ = dist (act (t - u) y) y := (hiso u).dist_eq _ _
      _ ≤ D * ‖t - u‖ := hbound (t - u) y
      _ = D * dist t u := by rw [dist_eq_norm]
  calc
    dist (act t x) (act u y) ≤ dist (act t x) (act t y) + dist (act t y) (act u y) := dist_triangle _ _ _
    _ ≤ dist x y + D * dist t u := by rw [(hiso t).dist_eq]; exact add_le_add le_rfl htime
    _ ≤ dist (t, x) (u, y) + D * dist (t, x) (u, y) := by
      gcongr
      · exact le_max_right _ _
      · exact le_max_left _ _
    _ = (D + 1 : ℝ≥0) * dist (t, x) (u, y) := by push_cast; ring

noncomputable def isometricCircleActionOfFlow (flow : ℝ → X → X)
    (hzero : ∀ x, flow 0 x = x)
    (hadd : ∀ r t x, flow (r + t) x = flow r (flow t x))
    (hperiod : ∀ x, flow 1 x = x) (hiso : ∀ r, Isometry (flow r)) (D : ℝ≥0)
    (hbound : ∀ r x, dist (flow r x) x ≤ D * |r|) : IsometricCircleAction X where
  act := periodicFlowAct flow (realFlow_periodic flow hadd hperiod)
  zero_act := periodicFlowAct_zero flow _ hzero
  add_act := periodicFlowAct_add flow _ hadd
  continuous_act := (circleAct_joint_lipschitz _ (periodicFlowAct_zero flow _ hzero)
    (periodicFlowAct_add flow _ hadd) (periodicFlowAct_isometry flow _ hiso) D
    (periodicFlowAct_displacement flow _ D hbound)).continuous
  isometry_act := periodicFlowAct_isometry flow _ hiso

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IteratedCircleAverageIntegral
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators NNReal

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def average (A : IsometricCircleAction X) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  circleFourierComponent 0 f

theorem average_lipschitz (A : IsometricCircleAction X) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : LipschitzWith L (A.average f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_circleFourierComponent 0 hf A.isometry_act

theorem average_norm_le (A : IsometricCircleAction X) {f : X → ℂ} {B : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖A.average f x‖ ≤ B := by
  let := A.toAddAction
  exact norm_circleFourierComponent_le 0 f hf x

end IsometricCircleAction
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedCircleAverage (A : α → IsometricCircleAction X) :
    List α → (X → ℂ) → X → ℂ
  | [], f => f
  | i :: is, f => (A i).average (iteratedCircleAverage A is f)

theorem iteratedCircleAverage_lipschitz (A : α → IsometricCircleAction X) (is : List α)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (iteratedCircleAverage A is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).average_lipschitz ih

theorem iteratedCircleAverage_norm_le (A : α → IsometricCircleAction X) (is : List α)
    {f : X → ℂ} {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    ∀ x, ‖iteratedCircleAverage A is f x‖ ≤ B := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).average_norm_le ih

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Pointwise

variable {σ : Type*}

theorem scalarDirectionalDerivative_mul [Fintype σ] (h : σ → ℚ) (p q : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative h (p * q) = scalarDirectionalDerivative h p * q +
      p * scalarDirectionalDerivative h q := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem polynomialTranslationPath_eval (x : σ → ℚ) (t : ℚ)
    (V : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x V).eval (C t) =
      polynomialTranslate (fun i => -(t * x i)) V := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, polynomialTranslationPath_X,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, polynomialTranslate_X]
    congr 1
    simp only [map_neg, map_mul]
    ring

@[simp] theorem polynomialTranslationPath_eval_zero (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x V).eval 0 = V := by
  have h := polynomialTranslationPath_eval x 0 V
  simp only [map_zero, zero_mul, neg_zero] at h
  exact h.trans (polynomialTranslate_zero V)

theorem polynomialTranslationPath_derivative [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x V).derivative =
      -polynomialTranslationPath x (scalarDirectionalDerivative x V) := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, neg_add_rev]
    abel
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.derivative_mul, hp,
      polynomialTranslationPath_X, Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_X, zero_sub, scalarDirectionalDerivative_mul,
      scalarDirectionalDerivative_X, map_add, polynomialTranslationPath_C]
    ring

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

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem reparam_slots (A : PolynomialSlots σ d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (A.reparam f hf).slots t = A.slots (fun a => aeval t (f a)) := by
  apply TriangularSlots.ext
  intro x i
  simp only [slots, reparam, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext v
  cases v with
  | inl a =>
    simp only [parameterSubstitution, Sum.elim_inl, MvPolynomial.comp_aeval_apply, aeval_X]
  | inr j => simp [parameterSubstitution]

end PolynomialSlots

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

theorem reparam_value (A : PolynomialPatch σ s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (A.reparam f hf).value t = A.value (fun a => aeval t (f a)) := by
  change ((A.form.reparam f hf).slots t).patchValue A.kernel = _
  rw [PolynomialSlots.reparam_slots]
  rfl

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisCoordinateProjection_eq_self (b : Basis ι K V) (S : Set ι) (x : V)
    (hx : x ∈ Submodule.span K (b '' S)) : basisCoordinateProjection b S x = x := by
  classical
  apply b.repr.injective
  ext i
  rw [basisCoordinateProjection_repr]
  split_ifs with hi
  · rfl
  · exact ((basis_mem_span_image_iff b S x).mp hx i hi).symm

theorem basisCoordinateProjection_basis (b : Basis ι K V) (S : Set ι)
    [DecidablePred (· ∈ S)] (i : ι) :
    basisCoordinateProjection b S (b i) = if i ∈ S then b i else 0 := by
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    exact basisCoordinateProjection_eq_self b S (b i) (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply b.repr.injective
    ext j
    classical
    by_cases hj : j ∈ S <;> by_cases hij : i = j <;>
      simp_all [basisCoordinateProjection_repr]

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem supportedQuotientBasis_map_span (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (T : Set ι) :
    (Submodule.span K (b '' T)).map P.mkQ = Submodule.span K
      (supportedQuotientBasis b P S hP '' {i : {i // i ∉ S} | (i : ι) ∈ T}) := by
  rw [Submodule.map_span, Set.image_image]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    by_cases hs : i ∈ S
    · have hz : P.mkQ (b i) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (by
        rw [hP]
        exact Submodule.subset_span ⟨i, hs, rfl⟩)
      change P.mkQ (b i) ∈ _
      rw [hz]
      exact Submodule.zero_mem _
    · have h := Submodule.subset_span (R := K)
        (show supportedQuotientBasis b P S hP ⟨i, hs⟩ ∈
          supportedQuotientBasis b P S hP '' {j : {i // i ∉ S} | (j : ι) ∈ T} from
            ⟨⟨i, hs⟩, hi, rfl⟩)
      simpa only [supportedQuotientBasis_apply] using h
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    rw [supportedQuotientBasis_apply]
    exact Submodule.subset_span ⟨i.val, hi, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.IntegralGridFunctional
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

def coordinateGridModule (e : Basis ι ℚ L) (B : ℕ) : Submodule ℤ L where
  carrier := {x | e.equivFun x ∈ scaledIntegerGrid B}
  zero_mem' := ⟨fun _ => 0, by ext i; simp⟩
  add_mem' := by
    rintro x y ⟨z, hz⟩ ⟨w, hw⟩
    refine ⟨fun i => z i + w i, ?_⟩
    rw [map_add, hz, hw]
    ext i
    simp [mul_add]
  smul_mem' := by
    rintro n x ⟨z, hz⟩
    refine ⟨fun i => n * z i, ?_⟩
    rw [map_zsmul, hz]
    ext i
    simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, Int.cast_mul]
    ring

theorem scaled_basis_mem_coordinateGridModule (e : Basis ι ℚ L) (B : ℕ) (i : ι) :
    (B : ℚ) • e i ∈ coordinateGridModule e B := by
  classical
  refine ⟨fun j => if i = j then 1 else 0, ?_⟩
  ext j
  simp only [map_smul, Pi.smul_apply, Basis.equivFun_self, Int.cast_ite, Int.cast_one,
    Int.cast_zero]

end Erdos3

end

section

namespace Erdos3

open Module

theorem coordinateGridModule_map_of_basis {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M)
    (hφ : ∀ i, ∃ j, φ (b i) = c j) (B : ℕ) {x : L}
    (hx : x ∈ coordinateGridModule b B) : φ x ∈ coordinateGridModule c B := by
  classical
  obtain ⟨z, hz⟩ := hx
  rw [← b.sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro i _
  obtain ⟨j, hj⟩ := hφ i
  have hi : b.repr x i = (B : ℚ) * (z i : ℚ) := congrFun hz i
  rw [map_smul, hi, hj]
  have hm := (coordinateGridModule c B).smul_mem (z i) (scaled_basis_mem_coordinateGridModule c B j)
  simpa only [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm] using hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeExponents
namespace OAI

section

namespace Erdos3

theorem squarefreeExponent_add_iff {ι : Type*} (a b : ι →₀ ℕ)
    (ha : SquarefreeExponent a) (hb : SquarefreeExponent b) :
    SquarefreeExponent (a + b) ↔ Disjoint a.support b.support := by
  classical
  rw [Finset.disjoint_left]
  constructor
  · intro h i hi hj
    have hsum : a i + b i ≤ 1 := h i
    have hai := Finsupp.mem_support_iff.mp hi
    have hbi := Finsupp.mem_support_iff.mp hj
    omega
  · intro h i
    have hai := ha i
    have hbi := hb i
    change a i + b i ≤ 1
    by_cases hzero : a i = 0
    · omega
    · have hz : b i = 0 := by
        by_contra hn
        exact h (Finsupp.mem_support_iff.mpr hzero) (Finsupp.mem_support_iff.mpr hn)
      omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreeBlockDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι]

theorem blockDegree_apply [DecidableEq σ] (π : ι → σ) (a : ι →₀ ℕ) (i : σ) :
    blockDegree π a i = ∑ j, if π j = i then a j else 0 := by
  classical
  unfold blockDegree
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : π j = i <;> simp only [h, ite_true, ite_false]

@[simp] theorem blockDegree_zero (π : ι → σ) : blockDegree π 0 = 0 := by
  classical
  ext i
  simp only [blockDegree_apply, Finsupp.zero_apply, ite_self, Finset.sum_const_zero, Pi.zero_apply]

theorem blockDegree_add (π : ι → σ) (a b : ι →₀ ℕ) :
    blockDegree π (a + b) = blockDegree π a + blockDegree π b := by
  classical
  ext i
  simp only [blockDegree_apply, Finsupp.add_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [add_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem realificationLieHom_basis (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (k : κ) (i : ι) :
    (f.baseChange ℝ).repr (realificationLieHom φ ((e.baseChange ℝ) i)) k =
      (f.repr (φ (e i)) k : ℝ) := by
  simp only [Basis.baseChange_apply, realificationLieHom_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ]

noncomputable def blockExponent (π : ι → σ) (a : ι →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (blockDegree π a)

@[simp] theorem blockExponent_apply (π : ι → σ) (a : ι →₀ ℕ) (i : σ) :
    blockExponent π a i = blockDegree π a i := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*}

noncomputable def polynomialExponentialPath (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    Polynomial (MvPolynomial σ ℚ) :=
  polynomialPrimitive (polynomialTranslationPath x P)

@[simp] theorem polynomialExponentialPath_derivative (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialExponentialPath x P).derivative = polynomialTranslationPath x P :=
  polynomialPrimitive_derivative _

@[simp] theorem polynomialExponentialPath_eval_zero (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) : (polynomialExponentialPath x P).eval 0 = 0 :=
  polynomialPrimitive_eval_zero _

theorem polynomialExponentialPath_unique (x : σ → ℚ) (P : MvPolynomial σ ℚ)
    {F : Polynomial (MvPolynomial σ ℚ)}
    (hderiv : F.derivative = polynomialTranslationPath x P) (hzero : F.eval 0 = 0) :
    polynomialExponentialPath x P = F :=
  polynomialPrimitive_unique hderiv hzero

noncomputable def polynomialExponentialCoordinate (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  (polynomialExponentialPath x P).eval 1

theorem polynomialExponentialCoordinate_formula (x : σ → ℚ) (P : MvPolynomial σ ℚ) :
    polynomialExponentialCoordinate x P =
      ∑ n ∈ (polynomialTranslationPath x P).support,
        (((n + 1 : ℕ) : ℚ)⁻¹ • (polynomialTranslationPath x P).coeff n) := by
  classical
  simp only [polynomialExponentialCoordinate, polynomialExponentialPath,
    polynomialPrimitive, Polynomial.sum_def, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, one_pow, mul_one]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

@[simp] theorem polynomialTranslationPath_zero (P : MvPolynomial σ ℚ) :
    polynomialTranslationPath (0 : σ → ℚ) P = Polynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

@[simp] theorem polynomialExponentialPath_C (x : σ → ℚ) (c : ℚ) :
    polynomialExponentialPath x (C c) = Polynomial.C (C c) * Polynomial.X := by
  apply polynomialExponentialPath_unique <;> simp

@[simp] theorem polynomialExponentialPath_zero (P : MvPolynomial σ ℚ) :
    polynomialExponentialPath (0 : σ → ℚ) P = Polynomial.C P * Polynomial.X := by
  apply polynomialExponentialPath_unique <;> simp

@[simp] theorem polynomialExponentialCoordinate_C (x : σ → ℚ) (c : ℚ) :
    polynomialExponentialCoordinate x (C c) = C c := by
  simp [polynomialExponentialCoordinate]

@[simp] theorem polynomialExponentialCoordinate_zero (P : MvPolynomial σ ℚ) :
    polynomialExponentialCoordinate (0 : σ → ℚ) P = P := by
  simp [polynomialExponentialCoordinate]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem polynomialTranslationPath_translate_reflection (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x P).map (polynomialTranslate x).toRingHom =
      (polynomialTranslationPath (-x) P).comp (1 - Polynomial.X) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Polynomial.map_add, Polynomial.add_comp, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, Polynomial.mul_comp]
    rw [hp]
    congr 1
    simp only [polynomialTranslationPath_X, Polynomial.map_sub, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      polynomialTranslate_X, polynomialTranslate_C, Polynomial.sub_comp,
      Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, Pi.neg_apply,
      map_neg, map_add, Polynomial.neg_comp]
    ring

theorem polynomialExponentialPath_translate_reflection (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialExponentialPath x P).map (polynomialTranslate x).toRingHom =
      Polynomial.C (polynomialExponentialCoordinate (-x) P) -
        (polynomialExponentialPath (-x) P).comp (1 - Polynomial.X) := by
  apply polynomial_eq_of_derivative_of_eval_zero
  · rw [Polynomial.derivative_map, polynomialExponentialPath_derivative,
      polynomialTranslationPath_translate_reflection, Polynomial.derivative_sub,
      Polynomial.derivative_C, Polynomial.derivative_comp_one_sub_X,
      polynomialExponentialPath_derivative, zero_sub, neg_neg]
  · have hz := Polynomial.eval_map_apply (p := polynomialExponentialPath x P)
        (polynomialTranslate x).toRingHom 0
    simp only [map_zero, polynomialExponentialPath_eval_zero] at hz
    rw [hz]
    simp [polynomialExponentialCoordinate, Polynomial.eval_comp]

theorem polynomialTranslate_exponentialCoordinate (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    polynomialTranslate x (polynomialExponentialCoordinate x P) =
      polynomialExponentialCoordinate (-x) P := by
  have h := congrArg (fun Q : Polynomial (MvPolynomial σ ℚ) => Q.eval 1)
    (polynomialExponentialPath_translate_reflection x P)
  have he := Polynomial.eval_map_apply (p := polynomialExponentialPath x P)
    (polynomialTranslate x).toRingHom 1
  simp only [map_one] at he
  rw [he] at h
  simpa [polynomialExponentialCoordinate, Polynomial.eval_comp] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem polynomialTranslate_comp (h k : σ → ℚ) (V : MvPolynomial σ ℚ) :
    polynomialTranslate h (polynomialTranslate k V) = polynomialTranslate (h + k) V := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, polynomialTranslate_X, map_add, polynomialTranslate_C,
      Pi.add_apply]
    rw [add_assoc]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem polynomialTranslationPath_neg_derivative (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (polynomialTranslationPath (-x) P).derivative =
      polynomialTranslationPath (-x) (scalarDirectionalDerivative x P) := by
  rw [polynomialTranslationPath_derivative, scalarDirectionalDerivative_neg, map_neg, neg_neg]

theorem polynomialTranslationPath_neg_coeff (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) (i : ℕ) :
    (polynomialTranslationPath (-x) P).coeff i =
      ((i.factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P := by
  induction i generalizing P with
  | zero =>
      simpa only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
        Module.End.one_apply, Polynomial.coeff_zero_eq_eval_zero]
        using polynomialTranslationPath_eval_zero (-x) P
  | succ i ih =>
      have hc := congrArg (fun Q : Polynomial (MvPolynomial σ ℚ) => Q.coeff i)
        (polynomialTranslationPath_neg_derivative x P)
      rw [Polynomial.coeff_derivative] at hc
      have hmul : ((i + 1 : ℕ) : ℚ) • (polynomialTranslationPath (-x) P).coeff (i + 1) =
          (polynomialTranslationPath (-x) (scalarDirectionalDerivative x P)).coeff i := by
        rw [Nat.cast_smul_eq_nsmul ℚ, nsmul_eq_mul']
        simpa only [Nat.cast_add, Nat.cast_one] using hc
      have hinv : (polynomialTranslationPath (-x) P).coeff (i + 1) =
          (((i + 1 : ℕ) : ℚ)⁻¹) •
            (polynomialTranslationPath (-x) (scalarDirectionalDerivative x P)).coeff i := by
        rw [← hmul, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)), one_smul]
      rw [hinv, ih, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev,
        pow_succ, Module.End.mul_apply]
      congr 1
      exact mul_comm _ _

theorem polynomialTranslationPath_neg_support_of_nilpotent (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ}
    (hP : ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0) :
    (polynomialTranslationPath (-x) P).support ⊆ Finset.range (n + 1) := by
  intro i hi
  apply Finset.mem_range.mpr
  by_contra hn
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
  have hz : ((scalarDirectionalDerivative x).toLinearMap ^ i) P = 0 := by
    rw [show i = j + (n + 1) by omega, pow_add, Module.End.mul_apply, hP, map_zero]
  exact Polynomial.mem_support_iff.mp hi (by
    rw [polynomialTranslationPath_neg_coeff, hz, smul_zero])

theorem polynomialExponentialCoordinate_neg_series_of_nilpotent (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ}
    (hP : ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0) :
    polynomialExponentialCoordinate (-x) P =
      ∑ i ∈ Finset.range (n + 1),
        (((i + 1).factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P := by
  classical
  rw [polynomialExponentialCoordinate_formula]
  calc
    _ = ∑ i ∈ Finset.range (n + 1),
        (((i + 1 : ℕ) : ℚ)⁻¹) • (polynomialTranslationPath (-x) P).coeff i := by
      apply Finset.sum_subset (polynomialTranslationPath_neg_support_of_nilpotent x hP)
      intro i hi hni
      rw [Polynomial.notMem_support_iff.mp hni, smul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [polynomialTranslationPath_neg_coeff, smul_smul, Nat.factorial_succ,
        Nat.cast_mul, mul_inv_rev]
      congr 1
      exact mul_comm _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationActionCompatibility
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem mem_integerCoefficientPolynomials_iff (P : MvPolynomial σ ℚ) :
    P ∈ integerCoefficientPolynomials σ ↔ ∀ a, ∃ z : ℤ, P.coeff a = (z : ℚ) := by
  change P ∈ (MvPolynomial.mapAlgHom (Int.castRingHom ℚ).toIntAlgHom).range.toSubmodule ↔ _
  rw [MvPolynomial.range_mapAlgHom, MvPolynomial.mem_coeffsIn]
  constructor
  · intro h a
    obtain ⟨z, hz⟩ := h a
    exact ⟨z, hz.symm⟩
  · intro h a
    obtain ⟨z, hz⟩ := h a
    exact ⟨z, hz.symm⟩

theorem integerCoefficientPolynomials_rat_smul {c : ℚ} (hc : ∃ z : ℤ, c = (z : ℚ))
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    c • P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨z, rfl⟩ := hc
  apply (mem_integerCoefficientPolynomials_iff _).mpr
  intro a
  obtain ⟨v, hv⟩ := (mem_integerCoefficientPolynomials_iff P).mp hP a
  refine ⟨z * v, ?_⟩
  simp [hv]

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem integerCoefficientPolynomials_C_iff (c : ℚ) :
    (C c : MvPolynomial σ ℚ) ∈ integerCoefficientPolynomials σ ↔
      ∃ z : ℤ, c = (z : ℚ) := by
  constructor
  · intro hc
    simpa using
      (mem_integerCoefficientPolynomials_iff (C c)).mp hc 0
  · rintro ⟨z, rfl⟩
    exact integerCoefficientPolynomials_C z

theorem integerCoefficientPolynomials_rename_iff (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ ℚ) :
    rename f P ∈ integerCoefficientPolynomials τ ↔
      P ∈ integerCoefficientPolynomials σ := by
  constructor
  · intro hP
    apply (mem_integerCoefficientPolynomials_iff P).mpr
    intro a
    simpa only [MvPolynomial.coeff_rename_mapDomain f hf] using
      (mem_integerCoefficientPolynomials_iff (rename f P)).mp hP (a.mapDomain f)
  · exact integerCoefficientPolynomials_rename f

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialMassBox
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

theorem abs_aeval_sub_aeval_mass_box_bound {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℝ)
    (v w : σ → ℝ) {B δ : ℝ} {s : ℕ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hv : ∀ i, |v i| ≤ B) (hw : ∀ i, |w i| ≤ B) (hvw : ∀ i, |v i - w i| ≤ δ)
    (hdegree : P.totalDegree ≤ s) :
    |aeval v P - aeval w P| ≤
      realPolynomialMass P * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)) * δ := by
  classical
  have hmonomial (m : σ →₀ ℕ) (hm : m ∈ P.support) :
      |(∏ i, v i ^ m i) - ∏ i, w i ^ m i| ≤
        Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ := by
    have hmdeg (i : σ) : m i ≤ s :=
      (monomial_le_degreeOf i hm).trans ((degreeOf_le_totalDegree P i).trans hdegree)
    have hpow (u : σ → ℝ) (hu : ∀ i, |u i| ≤ B) (i : σ) : |u i ^ m i| ≤ B ^ s := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hu i) _).trans (pow_le_pow_right₀ hB (hmdeg i))
    simpa only [Finset.card_univ] using
      abs_finset_prod_sub_prod_le Finset.univ (fun i => v i ^ m i) (fun i => w i ^ m i)
        (one_le_pow₀ hB) (by positivity)
        (fun i _ => hpow v hv i) (fun i _ => hpow w hw i)
        (fun i _ => abs_pow_sub_pow_box_bound hB hδ (hv i) (hw i) (hvw i) (hmdeg i))
  change |P.eval₂ (RingHom.id ℝ) v - P.eval₂ (RingHom.id ℝ) w| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  simp only [RingHom.id_apply]
  calc
    _ ≤ ∑ m ∈ P.support, |P.coeff m * ∏ i, v i ^ m i - P.coeff m * ∏ i, w i ^ m i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ P.support, |P.coeff m| *
        (Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hmonomial m hm) (abs_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [realPolynomialMass, Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FactorialIntegerScalars
namespace OAI

section

namespace Erdos3

theorem factorial_log_scalar_integer (s k : ℕ) (hk : k ≤ s) :
    ∃ z : ℤ, (s.factorial : ℚ) * ((-1 : ℚ) ^ (k + 1) / k) = (z : ℚ) := by
  by_cases hzero : k = 0
  · exact ⟨0, by simp [hzero]⟩
  obtain ⟨z, hz⟩ := rat_nat_div_integer_of_dvd (Nat.dvd_factorial (Nat.pos_of_ne_zero hzero) hk)
  refine ⟨(-1 : ℤ) ^ (k + 1) * z, ?_⟩
  push_cast
  rw [show (s.factorial : ℚ) * ((-1 : ℚ) ^ (k + 1) / k) =
    (-1 : ℚ) ^ (k + 1) * ((s.factorial : ℚ) / k) by ring, hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

omit [Fintype ι] [Fintype κ] in
theorem basis_reindex_span_weights (b : Basis ι ℚ L) (e : ι ≃ κ)
    (w : ι → ℕ) (j : ℕ) :
    Submodule.span ℚ ((b.reindex e) '' {i | j ≤ w (e.symm i)}) =
      Submodule.span ℚ (b '' {i | j ≤ w i}) := by
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e.symm i, hi, (Basis.reindex_apply b e i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e i, ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, Equiv.symm_apply_apply] using hi
    · simp only [Basis.reindex_apply, Equiv.symm_apply_apply]

omit [Fintype ι] [Fintype κ] in
theorem lieStructureConstants_reindex (b : Basis ι ℚ L) (e : ι ≃ κ) (i j k : κ) :
    lieStructureConstants (b.reindex e) i j k =
      lieStructureConstants b (e.symm i) (e.symm j) (e.symm k) := by
  simp only [lieStructureConstants, Basis.reindex_apply, Basis.repr_reindex_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*}

def replicatedPermutation (bound : σ → ℕ) (e : ∀ i, Equiv.Perm (Fin (bound i))) :
    Equiv.Perm (ReplicatedIndex bound) := Equiv.sigmaCongrRight e

theorem replicatedPermutation_block (bound : σ → ℕ) (e : ∀ i, Equiv.Perm (Fin (bound i)))
    (j : ReplicatedIndex bound) : (replicatedPermutation bound e j).1 = j.1 := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} (bound : σ → ℕ)

theorem replicatedPermutation_one :
    replicatedPermutation bound (1 : ReplicatedPermutation bound) = 1 := by
  apply Equiv.ext
  intro i
  cases i
  rfl

theorem replicatedPermutation_mul (e f : ReplicatedPermutation bound) :
    replicatedPermutation bound (e * f) = replicatedPermutation bound e * replicatedPermutation bound f := by
  apply Equiv.ext
  intro i
  cases i
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonStrideCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem commonStrideIndex_point {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m) (x : I → ℤ) :
    commonStrideIndex c m (commonStridePoint c m x) = x := by
  funext i
  simp only [commonStrideIndex, commonStridePoint, add_sub_cancel_left]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisProjectionRealification
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

theorem basisCoordinateProjection_baseChange (b : Basis ι ℚ V) (S : Set ι) :
    (basisCoordinateProjection b S).baseChange ℝ = basisCoordinateProjection (b.baseChange ℝ) S := by
  classical
  apply (b.baseChange ℝ).ext
  intro i
  rw [basisCoordinateProjection_basis, Basis.baseChange_apply, LinearMap.baseChange_tmul,
    basisCoordinateProjection_basis]
  split_ifs <;> simp only [TensorProduct.tmul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BufferedIntegerLift
namespace OAI

section

namespace Erdos3

namespace PatchKernel

theorem buffered_lift_unique {m : ℕ} (Ψ : PatchKernel m) (x : Fin m → ℝ)
    (β γ : Fin m → ℤ) (hβ : ∀ i, |x i - (β i : ℝ)| ≤ 1 / 2)
    (hγ : Ψ.value (fun i => x i - (γ i : ℝ)) ≠ 0) : γ = β := by
  apply (constantSlots x).integer_unique (b := γ) (c := β) (by norm_num : (1 : ℝ) / 4 + 1 / 2 < 1)
  · intro i
    simpa only [TriangularSlots.residual, constantSlots, abs_sub_comm] using Ψ.support _ hγ i
  · intro i
    simpa only [TriangularSlots.residual, constantSlots, abs_sub_comm] using hβ i

end PatchKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedTranslationIntegralCoordinates
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

theorem integral_C_iff {τ : Type*} (c : ℚ) :
    (C c : MvPolynomial τ ℚ) ∈ integerCoefficientPolynomials τ ↔
      ∃ z : ℤ, c = (z : ℚ) := by
  classical
  constructor
  · intro h
    simpa [MvPolynomial.coeff_C] using
      (mem_integerCoefficientPolynomials_iff _).mp h 0
  · rintro ⟨z, rfl⟩
    exact integerCoefficientPolynomials_C z

theorem integral_rename_iff {σ τ : Type*} (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ ℚ) :
    rename f P ∈ integerCoefficientPolynomials τ ↔
      P ∈ integerCoefficientPolynomials σ := by
  constructor
  · intro h
    apply (mem_integerCoefficientPolynomials_iff _).mpr
    intro a
    simpa only [coeff_rename_mapDomain f hf] using
      (mem_integerCoefficientPolynomials_iff _).mp h (a.mapDomain f)
  · intro h
    obtain ⟨Q, hQ⟩ := (mem_integerCoefficientPolynomials P).mp h
    apply (mem_integerCoefficientPolynomials _).mpr
    refine ⟨rename f Q, ?_⟩
    rw [MvPolynomial.map_rename, hQ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateQuotientModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

noncomputable def quotientFinBasis :
    Basis (Fin (Fintype.card {i // i ∉ S})) ℚ (L ⧸ I) :=
  (supportedQuotientBasis b I.toSubmodule S hspan).reindex (Fintype.equivFin _)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ComparableResidueProgressionPartition
namespace OAI

section

namespace Erdos3.FiniteProgressionPartition

noncomputable def residues (N q : ℕ) (hq : 0 < q) :
    FiniteProgressionPartition N := by
  let len : Fin q → ℕ := fun r => truncatedProgressionLength N r.val q N
  let f : (Σ r : Fin q, Fin (len r)) → Fin N := fun x =>
    ⟨x.1.val + q * x.2.val, ((lt_truncatedProgressionLength_iff hq).mp x.2.isLt).2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨r, j⟩ ⟨s, k⟩ heq
      have he : r.val + q * j.val = s.val + q * k.val := congrArg Fin.val heq
      have hrs : r = s := by
        apply Fin.ext
        have hm := congrArg (fun n => n % q) he
        simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt,
          Nat.mod_eq_of_lt s.isLt] using hm
      cases hrs
      have hjk : j = k := Fin.ext (mul_left_cancel₀ hq.ne' (Nat.add_left_cancel he))
      cases hjk
      rfl
    · intro n
      let r : Fin q := ⟨n.val % q, Nat.mod_lt _ hq⟩
      have hj : n.val / q < len r := by
        apply (lt_truncatedProgressionLength_iff hq).mpr
        exact ⟨lt_of_le_of_lt (Nat.div_le_self _ _) n.isLt,
          by simpa only [r, Nat.mod_add_div] using n.isLt⟩
      exact ⟨⟨r, ⟨n.val / q, hj⟩⟩, Fin.ext (Nat.mod_add_div _ _)⟩
  exact {
    Label := Fin q
    labelFintype := inferInstance
    start := fun r => r.val
    step := fun _ => q
    length := len
    step_pos := fun _ => hq
    equiv := Equiv.ofBijective f hf
    equiv_val := fun _ _ => rfl }

@[simp] theorem residues_start (N q : ℕ) (hq : 0 < q)
    (r : (residues N q hq).Label) : (residues N q hq).start r = r.val := rfl

@[simp] theorem residues_step (N q : ℕ) (hq : 0 < q)
    (r : (residues N q hq).Label) : (residues N q hq).step r = q := rfl

theorem residues_length_lower {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (r : (residues N q hq).Label) :
    H ≤ (residues N q hq).length r := by
  have hHN : H ≤ N := le_trans (Nat.le_mul_of_pos_left H hq) hfit
  have hpoint : r.val + q * (H - 1) < N := by
    have heq : q * (H - 1) + q = q * H := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    have hlt := Nat.add_lt_add_right r.isLt (q * (H - 1))
    omega
  have hj : H - 1 < (residues N q hq).length r :=
    (lt_truncatedProgressionLength_iff hq).mpr ⟨by omega, hpoint⟩
  omega

noncomputable def comparableResidueProgressions (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) : FiniteProgressionPartition N :=
  (residues N q hq).bind (fun r =>
    mergedIntervals ((residues N q hq).length r) H hH
      (residues_length_lower hq hH hfit r))

@[simp] theorem comparableResidueProgressions_step (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidueProgressions N q H hq hH hfit).Label) :
    (comparableResidueProgressions N q H hq hH hfit).step i = q := by
  rcases i with ⟨r, j⟩
  simp [comparableResidueProgressions]

end Erdos3.FiniteProgressionPartition

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

def weightedPatchVariableWeight {σ : Type*} {d : ℕ}
    (p : σ → ℕ) (w : Fin d → ℕ) (i : Fin d) : σ ⊕ Fin i.val → ℕ :=
  Sum.elim p (fun j => w (earlierSlot i j))

structure WeightedParameterSlots (σ : Type*) (p : σ → ℕ) (d : ℕ) (w : Fin d → ℕ) where
  center : (i : Fin d) → MvPolynomial (σ ⊕ Fin i.val) ℝ
  degree : ∀ i, center i ∈ weightedSupportLE (weightedPatchVariableWeight p w i) (w i)

namespace WeightedParameterSlots

variable {σ : Type*} {p : σ → ℕ} {d : ℕ} {w : Fin d → ℕ}

noncomputable def slots (A : WeightedParameterSlots σ p d w) (t : σ → ℝ) :
    TriangularSlots d where
  center x i := aeval (Sum.elim t (fun j => x (earlierSlot i j))) (A.center i)
  lower i x y hxy := by
    apply congrArg (fun f : σ ⊕ Fin i.val → ℝ => aeval f (A.center i))
    funext v
    cases v with
    | inl a => rfl
    | inr j => exact hxy (earlierSlot i j) j.isLt

end WeightedParameterSlots

structure WeightedParameterPatch (σ : Type*) (p : σ → ℕ) (s d : ℕ) where
  weight : Fin d → ℕ
  weight_pos : ∀ i, 1 ≤ weight i
  weight_le : ∀ i, weight i ≤ s
  weight_mono : Monotone weight
  form : WeightedParameterSlots σ p d weight
  kernel : PatchKernel d

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

noncomputable def value (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) : ℝ :=
  (A.form.slots t).patchValue A.kernel

end WeightedParameterPatch

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

def weightedParameters (A : PolynomialPatch σ s d) :
    WeightedParameterPatch σ (fun _ => 1) s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := { center := A.form.center, degree := A.form.degree }
  kernel := A.kernel

@[simp] theorem weightedParameters_value (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.weightedParameters.value t = A.value t := rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterSlots

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {d : ℕ} {w : Fin d → ℕ}

theorem parameterSubstitution_degree (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) (i : Fin d) (a : σ ⊕ Fin i.val) :
    parameterSubstitution f i a ∈ weightedSupportLE (weightedPatchVariableWeight q w i)
      (weightedPatchVariableWeight p w i a) := by
  cases a with
  | inl a =>
    apply weightedSupportLE_aeval q (weightedPatchVariableWeight q w i)
    · intro b
      exact weightedSupportLE_X _ (Sum.inl b)
    · exact hf a
  | inr j => exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def reparam (A : WeightedParameterSlots σ p d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) : WeightedParameterSlots τ q d w where
  center i := aeval (parameterSubstitution f i) (A.center i)
  degree i := weightedSupportLE_aeval _ _ _ (parameterSubstitution_degree f hf i) (A.degree i)

end WeightedParameterSlots

namespace WeightedParameterPatch

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {s d : ℕ}

noncomputable def reparam (A : WeightedParameterPatch σ p s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) : WeightedParameterPatch τ q s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.form.reparam f hf
  kernel := A.kernel

@[simp] theorem reparam_lip (A : WeightedParameterPatch σ p s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) :
    (A.reparam f hf).kernel.lip = A.kernel.lip := rfl

end WeightedParameterPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedParameterPatchRankPadding
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators NNReal

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s D E : ℕ}

def castRank {d e : ℕ} (P : WeightedParameterPatch σ p s d) (h : d = e) :
    WeightedParameterPatch σ p s e := h ▸ P

@[simp] theorem castRank_value {d e : ℕ} (P : WeightedParameterPatch σ p s d)
    (h : d = e) (t : σ → ℝ) : (P.castRank h).value t = P.value t := by
  subst e
  rfl

@[simp] theorem castRank_kernel_lip {d e : ℕ} (P : WeightedParameterPatch σ p s d)
    (h : d = e) : (P.castRank h).kernel.lip = P.kernel.lip := by
  subst e
  rfl

end WeightedParameterPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCoordinateEquiv
namespace OAI

section

namespace Erdos3

variable {X Y : Type*}

def integerPointCoordinateEquiv (e : X ≃ Y) : (X → ℤ) ≃ (Y → ℤ) where
  toFun x y := x (e.symm y)
  invFun y x := y (e x)
  left_inv x := by funext i; simp only [e.symm_apply_apply]
  right_inv y := by funext j; simp only [e.apply_symm_apply]

@[simp] theorem integerPointCoordinateEquiv_apply (e : X ≃ Y) (x : X → ℤ) (y : Y) :
    integerPointCoordinateEquiv e x y = x (e.symm y) := rfl

@[simp] theorem integerPointCoordinateEquiv_symm_apply (e : X ≃ Y) (y : Y → ℤ) (x : X) :
    (integerPointCoordinateEquiv e).symm y x = y (e x) := rfl

@[simp] theorem integerPointCoordinateEquiv_symm (e : X ≃ Y) :
    integerPointCoordinateEquiv e.symm = (integerPointCoordinateEquiv e).symm := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AuxiliaryBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev AuxiliaryBoxLabels {I : Type*} {N : I → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d : I → ℕ) (u : I → ℤ) :=
  ∀ i, (P i).Label × CompatibleAuxResidue (M i) (d i) (u i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueStrideRebase
namespace OAI

section

namespace Erdos3

def residueBoxStrideValue {I : Type*} {a b r v : I → ℤ}
    (f : (I → ℤ) → ℂ) (u : I → ℤ) (M : ℕ) (x : IntegerResidueBox a b r v) : ℂ :=
  f (commonStrideIndex u M (fun i => (x i).val))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3

def correlationInput {A : Type*} (h n : A) : Fin 2 → A := Fin.cases h (fun _ => n)

def mixedCorrelationDegree (s : ℕ) : Fin 2 → ℕ := correlationInput 1 s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedSubquotient
namespace OAI

section

namespace Erdos3

open Module

theorem supportedSubmoduleBasis_comap_span {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (P Q : Submodule K V) (S T : Set ι)
    (hP : P = Submodule.span K (b '' S)) (hQ : Q = Submodule.span K (b '' T)) :
    Q.comap P.subtype = Submodule.span K
      (supportedSubmoduleBasis b P S hP '' {i : S | i.val ∈ T}) := by
  ext x
  change x.val ∈ Q ↔ _
  rw [hQ, basis_mem_span_image_iff, basis_mem_span_image_iff]
  constructor
  · intro h i hi
    rw [supportedSubmoduleBasis_repr]
    exact h i.val hi
  · intro h i hi
    by_cases hs : i ∈ S
    · have hh := h ⟨i, hs⟩ hi
      simpa only [supportedSubmoduleBasis_repr] using hh
    · exact (basis_mem_span_image_iff b S x.val).mp (hP.le x.property) i hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGraphSmallDifference
namespace OAI

section

namespace Finset
open scoped _root_.Finset

variable {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]

scoped[Combinatorics.Additive'] notation3:max "E[" s ", " t "]" => _root_.OAI.Finset.addEnergy' s t
scoped[Combinatorics.Additive'] notation3:max "E[" s "]" => _root_.OAI.Finset.addEnergy' s s

end Finset

end

section

namespace Erdos3.BSG

open _root_.Finset _root_.OAI.Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate Indicator
  Combinatorics.Additive'

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [Semifield K] [CharZero K] [StarRing K]

def dconv (f g : G → K) : G → K :=
  fun a => 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2

scoped[BSGConvolution] infixl:71 " ○ " => _root_.OAI.Erdos3.BSG.dconv

open scoped BSGConvolution

theorem dconv_eq_expect_add (f g : G → K) (a : G) :
    (f ○ g) a = 𝔼 t, f (a + t) * conj (g t) := by
  unfold dconv
  refine expect_nbij (fun x => x.2) (fun x _ => mem_univ _) ?_ ?_ fun b _ =>
    ⟨(a + b, b), mem_filter.mpr ⟨mem_univ _, add_sub_cancel_right _ _⟩, rfl⟩
  · intro x hx
    have heq : x.1 = a + x.2 := (sub_eq_iff_eq_add).mp (mem_filter.mp hx).2
    simp only [heq, Pi.conj_apply]
  · unfold Set.InjOn
    intro x hx y hy hxy
    apply Prod.ext
    · have hx' := (sub_eq_iff_eq_add).mp (mem_filter.mp hx).2
      have hy' := (sub_eq_iff_eq_add).mp (mem_filter.mp hy).2
      simp only [hx', hy', hxy]
    · exact hxy

theorem dconv_eq_expect_sub (f g : G → K) (a : G) :
    (f ○ g) a = 𝔼 t, f t * conj (g (t - a)) := by
  rw [dconv_eq_expect_add]
  symm
  refine Fintype.expect_equiv (Equiv.subRight a) _ _ fun t => ?_
  simp only [Equiv.subRight_apply]
  rw [add_comm a, sub_add_cancel]

theorem expect_dconv_mul (f g h : G → K) :
    𝔼 a, (f ○ g) a * h a = 𝔼 a, 𝔼 b, f a * conj (g b) * h (a - b) := by
  simp_rw [dconv_eq_expect_sub, expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ => Fintype.expect_equiv (Equiv.subLeft x) _ _ fun y => by simp

theorem expect_dconv (f g : G → K) :
    𝔼 a, (f ○ g) a = (𝔼 a, f a) * 𝔼 a, conj (g a) := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_dconv_mul f g 1

theorem dconv_indicator_one (f : G → K) (s : Finset G) :
    f ○ 𝟭_[s] = (∑ a ∈ s, τ (-a) f) /ℚ Fintype.card G := by
  ext
  simp [dconv_eq_expect_add, Set.indicator_apply, expect]

theorem indicator_one_dconv_indicator_one_eq_dens (s t : Finset G) (a : G) :
    (𝟭_[s, K] ○ 𝟭_[t]) a = (s ∩ (a +ᵥ t)).dens := by
  rw [← dens_vadd_finset (-a), inter_comm, vadd_finset_inter]
  simp [dconv_indicator_one, Set.indicator_apply, NNRat.smul_def, dens, div_eq_inv_mul,
    ← filter_mem_eq_inter, ← neg_vadd_mem_iff, sub_eq_add_neg]

theorem indicator_one_dconv_indicator_one_eq_addConvolution_div (s t : Finset G) (a : G) :
    (𝟭_[s, K] ○ 𝟭_[t]) a = s.addConvolution (-t) a / card G := by
  rw [indicator_one_dconv_indicator_one_eq_dens, dens, card_inter_vadd]
  simp

theorem expect_indicator_one_dconv_indicator_one (s t : Finset G) :
    𝔼 a, (𝟭_[(s : Set G), K] ○ 𝟭_[t]) a = s.dens * t.dens := by
  simp [expect_dconv, Set.conj_indicator_one_apply]
  simp [← Pi.one_def]

theorem expect_indicator_one_dconv_indicator_sq (s t : Finset G) :
    𝔼 x, (𝟭_[(s : Set G), K] ○ 𝟭_[t]) x ^ 2 = E[s, t] := by
  suffices
      ∑ x, #{yz ∈ s ×ˢ t | yz.1 - yz.2 = x} ^ 2 =
        #{x ∈ (s ×ˢ s) ×ˢ t ×ˢ t | x.1.1 + x.2.1 = x.1.2 + x.2.2} by
    simp only [expect, card_univ, indicator_one_dconv_indicator_one_eq_dens, dens, NNRat.cast_div,
      NNRat.cast_natCast, sq, div_mul_div_comm, ← sum_div, NNRat.smul_def, NNRat.cast_inv,
      addEnergy', NNRat.cast_pow, card_inter_vadd, ← card_sub_eq]
    field_simp
    norm_cast
  simp only [_root_.Finset.card_eq_sum_ones, sq, Finset.sum_mul_sum, sum_filter, sum_product, boole_mul,
    univ.sum_comm, Finset.sum_ite_eq, mem_univ, ite_true, sub_eq_sub_iff_add_eq_add]
  exact sum_comm

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open _root_.Finset _root_.OAI.Finset Function
open scoped ComplexConjugate BSGConvolution

variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [Semifield K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
  [StarRing K] [StarOrderedRing K] {f g : G → K}

omit [IsStrictOrderedRing K] in
theorem dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  fun _ => expect_nonneg fun x _ => mul_nonneg (hf x.1) (star_nonneg_iff.mpr (hg x.2))

omit [IsStrictOrderedRing K] in
theorem dconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ○ g) a :=
  dconv_nonneg hf hg a

theorem dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  change 0 < f a at ha
  change 0 < g b at hb
  refine ⟨dconv_nonneg hf hg, a - b, ?_⟩
  change 0 < (f ○ g) (a - b)
  rw [dconv_eq_expect_add]
  apply expect_pos' (fun x _ => mul_nonneg (hf (a - b + x)) (star_nonneg_iff.mpr (hg x)))
  refine ⟨b, mem_univ _, ?_⟩
  rw [sub_add_cancel]
  exact mul_pos ha (star_pos_iff.mpr hb)

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open _root_.Finset hiding card
open _root_.OAI.Finset
open Fintype
open scoped BigOperators Pointwise Combinatorics.Additive' Indicator BSGConvolution

section
variable {α : Type*} [Fintype α] [DecidableEq α] {H : Finset (α × α)} {A B X : Finset α} {a b x : α}
  {K : ℝ}

noncomputable def oneOfPair (H : Finset (α × α)) (X : Finset α) : Finset α :=
  {x ∈ X | (3 / 4 : ℝ) * X.dens ≤ {c ∈ X | (x, c) ∈ H}.dens}

lemma mem_oneOfPair :
    x ∈ oneOfPair H X ↔ x ∈ X ∧ (3 / 4 : ℝ) * X.dens ≤ {c ∈ X | (x, c) ∈ H}.dens := mem_filter

lemma quadruple_bound_c {a b : α} (ha : a ∈ oneOfPair H X) (hb : b ∈ oneOfPair H X) :
    (X.dens : ℝ) / 2 ≤ {c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.dens := by
  rw [mem_oneOfPair] at ha hb
  rw [filter_and, cast_dens_inter, ← filter_or]
  have : ({c ∈ X | (a, c) ∈ H ∨ (b, c) ∈ H}.dens : ℝ) ≤ X.dens := by grw [filter_subset]
  linarith [ha.2, hb.2, this]

end

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A B : Finset G} {x : G}

omit [Fintype G] in
lemma quadruple_bound_right {a b : G} (H : Finset (G × G)) (X : Finset G) (h : x = a - b) :
    (#({c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.sigma fun c ↦ ((B ×ˢ B) ×ˢ B ×ˢ B).filter
        fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) : ℝ)
      ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = a - b) := by
  rw [← h, Nat.cast_le]
  refine card_le_card_of_injOn Sigma.snd (by simp +contextual [Set.MapsTo, *]) ?_
  simp +contextual [Set.InjOn]
  aesop

variable {K : Type*} [Semifield K] [CharZero K] [StarRing K]

section lemma1

lemma claim_one : 𝔼 x : G, (𝟭_[A, K] ○ 𝟭_[B]) x * (A ∩ (x +ᵥ B)).dens = E[A, B] := by
  simp only [← expect_indicator_one_dconv_indicator_sq, ← indicator_one_dconv_indicator_one_eq_dens,
    sq]

lemma claim_two :
    (E[A, B]) ^ 2 / (A.dens * B.dens) ≤
      𝔼 x, (𝟭_[(A : Set G), ℝ] ○ 𝟭_[B]) x * (A ∩ (x +ᵥ B)).dens ^ 2 := by
  let f := fun x ↦ ((𝟭_[(A : Set G), ℝ] ○ 𝟭_[B]) x).sqrt
  have hf : ∀ x, f x ^ 2 = (𝟭_[A, ℝ] ○ 𝟭_[B]) x := by
    intro x
    rw [Real.sq_sqrt]
    exact dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg x
  have := expect_mul_sq_le_sq_mul_sq univ f (fun x ↦ f x * (A ∩ (x +ᵥ B)).dens)
  refine div_le_of_le_mul₀ (by positivity) ?_ ?_
  · refine expect_nonneg fun i _ ↦ ?_

    exact mul_nonneg (dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg _)
      (by positivity)
  simp only [← sq, ← mul_assoc, hf, expect_indicator_one_dconv_indicator_one, mul_pow, claim_one]
    at this
  grind

lemma claim_three {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ H).dens =
      (∑ ab ∈ H, 𝔼 x, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] (ab.1 - x) * 𝟭_[B] (ab.2 - x)))
        / card G ^ 2 := by
  simp only [dens, Fintype.card_prod, Nat.cast_mul, NNRat.cast_div, NNRat.cast_natCast,
    NNRat.cast_mul, mul_div, Fintype.expect_eq_sum_div_card, ← sum_div]
  field_simp
  simp only [sum_comm (s := H), mul_sum, _root_.Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  congr! 1 with x
  rw [inter_comm, ← filter_mem_eq_inter, sum_filter]
  congr! 1 with ⟨a, b⟩ hab
  have : a ∈ A ∧ b ∈ A := by simpa using hH hab
  simp [this, Set.indicator_apply, ← neg_vadd_mem_iff, neg_add_eq_sub]
  grind

lemma claim_four (ab : G × G) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] (ab.1 - x) * 𝟭_[B] (ab.2 - x)) ≤
      B.dens * (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2) := by
  obtain ⟨a, b⟩ := ab
  have (x : G) : (𝟭_[A, ℝ] ○ 𝟭_[B]) x ≤ B.dens := by
    simp only [dconv_eq_expect_add, Set.conj_indicator_one_apply, dens,
      Fintype.expect_eq_sum_div_card, NNRat.cast_div, NNRat.cast_natCast]
    gcongr
    simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    simp only [Set.indicator_apply, mul_boole, SetLike.mem_coe,
      ← sum_filter (· ∈ B), filter_mem_eq_inter, univ_inter]
    gcongr with i
    grind
  have : 𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] ((a, b).1 - x) * 𝟭_[B] ((a, b).2 - x)) ≤
    B.dens * 𝔼 x : G, (𝟭_[B] ((a, b).1 - x) * 𝟭_[B] ((a, b).2 - x)) := by
    rw [mul_expect]
    gcongr with s hs
    · exact mul_nonneg Set.indicator_one_apply_nonneg Set.indicator_one_apply_nonneg
    · exact this _
  refine this.trans_eq ?_
  congr 1
  simp only [dconv_eq_expect_add]
  exact Fintype.expect_equiv (Equiv.subLeft b) _ _ <| by simp

lemma claim_five {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ H).dens ≤
      B.dens * (∑ ab ∈ H, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2)) / card G ^ 2 := by
  rw [claim_three hH, mul_sum]; gcongr; exact claim_four _

noncomputable def choiceH (A B : Finset G) (c : ℝ) : Finset (G × G) :=
  {ab ∈ A ×ˢ A |
    (𝟭_[B, ℝ] ○ 𝟭_[B]) (ab.1 - ab.2) ≤ c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))}

lemma choiceH_subset {c : ℝ} : choiceH A B c ⊆ A ×ˢ A := filter_subset ..

lemma claim_six (c : ℝ) (hc : 0 ≤ c) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens ≤
      c / 2 * (E[A, B] ^ 2 / (A.dens * B.dens)) := by
  have : ∑ ab ∈ choiceH A B c, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2) ≤
      #(choiceH A B c) * (c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))) := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2
  replace : (∑ ab ∈ choiceH A B c, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2)) / card G ^ 2 ≤
      (choiceH A B c).dens * (c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))) := by
    grw [this, mul_div_right_comm]; simp [dens, sq]
  have hH : ((choiceH A B c).dens : ℝ) ≤ A.dens ^ 2 := by grw [choiceH_subset]; simp [sq]
  grw [claim_five choiceH_subset, ← mul_div, this, hH]
  field_simp
  rfl

lemma claim_seven {c : ℝ} (hc : 0 ≤ c) :
    𝔼 x : G,
      (𝟭_[A, ℝ] ○ 𝟭_[B]) x *
          ((c / 2) * (E[A, B] ^ 2 / (A.dens ^ 2 * B.dens ^ 2)) +
            ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens) ≤
      𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (c * (A ∩ (x +ᵥ B)).dens ^ 2) :=
  calc
    _ = (c / 2 * (E[A, B] ^ 2 / (A.dens * B.dens))) + 𝔼 x : G,
          (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens := by
        simp only [mul_add, expect_add_distrib, expect_indicator_one_dconv_indicator_one,
          ← expect_mul, ← mul_pow]
        field_simp
    _ ≤ _ := by
      grw [claim_six c hc, ← add_mul, add_halves]
      simp only [mul_left_comm _ c, ← mul_expect]
      gcongr
      exact claim_two

lemma claim_eight {c : ℝ} (hc : 0 ≤ c) (A B : Finset G) :
    ∃ x : G, ((c / 2) * (E[A, B] ^ 2 / (A.dens ^ 2 * B.dens ^ 2)) +
          ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens) ≤
      c * (A ∩ (x +ᵥ B)).dens ^ 2 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  by_contra!
  refine (claim_seven hc (A := A) (B := B)).not_gt <| expect_lt_expect (fun x _ ↦ ?_) ?_
  · grw [this x]
    exact dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg x
  have : 0 < 𝟭_[(A : Set G), ℝ] ○ 𝟭_[B] := by apply dconv_pos <;> simpa
  rw [Pi.lt_def] at this
  obtain ⟨-, i, hi : 0 < _⟩ := this
  exact ⟨i, by simp, mul_lt_mul_of_pos_left (this i) hi⟩

lemma lemma_one {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hE : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B])
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x : G, ∃ X ⊆ A ∩ (x +ᵥ B), A.dens / (Real.sqrt 2 * K) ≤ X.dens ∧
      (1 - c) * X.dens ^ 2 ≤
      ((X ×ˢ X).filter fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * A.dens ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)).dens := by
  obtain ⟨x, hx⟩ := claim_eight hc.le A B
  set X := A ∩ (x +ᵥ B)
  refine ⟨x, X, subset_rfl, ?_, ?_⟩
  · have : (2 : ℝ)⁻¹ * (E[A, B] / (A.dens * B.dens)) ^ 2 ≤ X.dens ^ 2 := by
      refine le_of_mul_le_mul_left (hx.trans' ?_) hc
      exact (le_add_of_nonneg_right <| NNRat.cast_nonneg _).trans_eq' (by ring)
    grw [← sq_le_sq₀ (by positivity) (by positivity), ← this, ← hE]

    field_simp
    norm_num
  rw [one_sub_mul, sub_le_comm]
  refine ((le_add_of_nonneg_left (by positivity)).trans hx).trans' ?_
  rw [sq, ← NNRat.cast_mul, ← dens_product, ← cast_dens_sdiff (filter_subset _ _), ← filter_not,
    ← filter_mem_eq_inter]
  gcongr ↑(dens ?_)
  rintro ⟨a, b⟩
  simp +contextual only [not_le, mem_product, mem_inter, and_imp, mem_filter, choiceH, and_self,
    true_and, X]
  rintro _ _ _ _ h
  grw [h, ← hE]
  apply le_of_eq
  field_simp [hA, hB, hK, le_div_iff₀, div_le_iff₀] at hE ⊢

lemma lemma_one' {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hE : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B])
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x : G, ∃ X ⊆ A ∩ (x +ᵥ B), A.dens / (2 * K) ≤ X.dens ∧
      (1 - c) * X.dens ^ 2 ≤
      ((X ×ˢ X).filter fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * A.dens ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)).dens := by
  obtain ⟨x, X, hX₁, hX₂, hX₃⟩ := lemma_one hc hK hE hA hB
  refine ⟨x, X, hX₁, hX₂.trans' ?_, hX₃⟩
  gcongr _ / (?_ * _)
  rw [Real.sqrt_le_iff]
  norm_num

end lemma1

section lemma2
variable {H : Finset (G × G)} {X : Finset G}

lemma quadruple_bound_other {a b c : G} {K : ℝ} {H : Finset (G × G)}
    (hac : (a, c) ∈ H) (hbc : (b, c) ∈ H)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    (A.dens / (2 ^ 4 * K ^ 2)) ^ 2 ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 2 := by
  rw [filter_product (s := B ×ˢ B) (t := B ×ˢ B) (fun z ↦ z.1 - z.2 = a - c)
    (fun z ↦ z.1 - z.2 = b - c), card_product, sq, sq (card G : ℝ), Nat.cast_mul,
      mul_div_mul_comm]
  gcongr ?_ * ?_
  · grw [card_sub_eq, hH _ hac, indicator_one_dconv_indicator_one_eq_addConvolution_div]
  · grw [card_sub_eq, hH _ hbc, indicator_one_dconv_indicator_one_eq_addConvolution_div]

lemma quadruple_bound_left {a b : G} {K : ℝ} {H : Finset (G × G)}
    (ha : a ∈ oneOfPair H X) (hb : b ∈ oneOfPair H X)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    X.dens / 2 * (A.dens / (2 ^ 4 * K ^ 2)) ^ 2 ≤
      #({c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.sigma fun c ↦
      ((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 3  :=
  calc
    _ ≤ (∑ c ∈ X with (a, c) ∈ H ∧ (b, c) ∈ H, ((A.dens / (2 ^ 4 * K ^ 2)) ^ 2 : ℝ))
      / card G := by
      grw [sum_const, quadruple_bound_c ha hb]
      apply le_of_eq
      simp [dens]
      ring
    _ ≤ (∑ c ∈ X with (a, c) ∈ H ∧ (b, c) ∈ H, #(((B ×ˢ B) ×ˢ B ×ˢ B).filter
        fun ((a₁, a₂), a₃, a₄) ↦ a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 2 : ℝ)
          / card G := by
      gcongr with i hi
      simp only [mem_filter] at hi
      convert quadruple_bound_other hi.2.1 hi.2.2 hH
    _ = _ := by rw [_root_.Finset.card_sigma, Nat.cast_sum, ← sum_div]; ring

lemma quadruple_bound {K : ℝ} {x : G} (hx : x ∈ oneOfPair H X - oneOfPair H X)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    (A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4) ≤
      #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
      card G ^ 3 := by
  rw [mem_sub] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  grw [← quadruple_bound_right H X rfl, ← quadruple_bound_left ha hb hH]
  apply le_of_eq
  ring

lemma big_quadruple_bound {K : ℝ}
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2))
    (hX : A.dens / (2 * K) ≤ X.dens) :
    (oneOfPair H X - oneOfPair H X).dens * (A.dens ^ 3 / (2 ^ 10 * K ^ 5)) ≤ B.dens ^ 4 :=
  calc
    _ = (oneOfPair H X - oneOfPair H X).dens * ((A.dens ^ 2 * (A.dens / (2 * K)))
      / (2 ^ 9 * K ^ 4)) := by ring
    _ ≤ (oneOfPair H X - oneOfPair H X).dens * ((A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4)) := by
      gcongr
    _ = (∑ _x ∈ oneOfPair H X - oneOfPair H X, (A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4) : ℝ)
      / card G := by simp [dens]; ring
    _ ≤ (∑ x ∈ oneOfPair H X - oneOfPair H X,
          #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
            card G ^ 3 : ℝ)
      / card G := by gcongr (∑ _ ∈ _, ?_) / _ with x hx; exact quadruple_bound hx hH
    _ ≤ 𝔼 x, (#(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
          card G ^ 3 : ℝ) := by grw [Fintype.expect_eq_sum_div_card, ← subset_univ]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, ← sum_div]
      norm_cast
      rw [← card_eq_sum_card_fiberwise (by simp [Set.mapsTo_univ])]
      simp [dens]
      field_simp

end lemma2

end Erdos3.BSG

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

noncomputable def residuePairMean {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℤ) → ℂ) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u v : I → ℤ)
    (J : I → ℕ) (flag : Bool) : ℂ :=
  𝔼 x : IntegerResidueBox lo (fun i => lo i + N i)
    (fun i => (M * residuePairStep J flag i : ℕ)) (residuePairValue u v flag),
    residueBoxStrideValue f u M x

@[simp] theorem residuePairMean_false {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℤ) → ℂ) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u v : I → ℤ) (J : I → ℕ) :
    residuePairMean f lo N M u v J false =
      𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u,
        residueBoxStrideValue f u M x := by
  exact congrArg
    (fun r : I → ℤ => 𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) r u,
      residueBoxStrideValue f u M x)
    (show (fun _ : I => ((M * 1 : ℕ) : ℤ)) = (fun _ => (M : ℤ)) by
      funext i
      rw [Nat.mul_one])

@[simp] theorem residuePairMean_true {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℤ) → ℂ) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u v : I → ℤ) (J : I → ℕ) :
    residuePairMean f lo N M u v J true =
      𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v,
        residueBoxStrideValue f u M x := rfl

end Erdos3

end

end OAI
end


