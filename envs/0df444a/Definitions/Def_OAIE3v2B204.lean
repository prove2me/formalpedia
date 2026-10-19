-- Prove2me | Definitions.Def_OAIE3v2B204
-- name    : OAIE3v2B204
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:00:04.559912+00:00
-- url     : https://prove2.me/theorems/eb79a404-0e5f-4199-a6fb-d89cb75d1db2
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 208 of 311
-- statement:
--   Definitions bundle 208 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B181`, `OAIE3v2B186`, `OAIE3v2B187`, `OAIE3v2B188` of this split.
--
--   Modules: `Estimates/CommonDependentCoveredModel.lean`, `Estimates/CommonMarkedMultidegree.lean`, `Estimates/CommonUniformCoefficientCorrections.lean`, `Estimates/CoveredQuotientCorrelation.lean`, `Estimates/MarkedPureEvaluation.lean`, `Estimates/MarkedShiftGeneratorBounds.lean`, `Estimates/NativeCommonModelQuadruples.lean`, `Estimates/NativeResidualCrossInduction.lean`, `Estimates/UnitVerticalDifference.lean`, `Estimates/UnitVerticalNativeInverseModels.lean`, `Geometry/MarkedDirectionCoordinates.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Lattices/MarkedDirectionLatticeScale.lean`, `Lattices/NormalizedMarkedLattice.lean`, `Lattices/RealMarkedAffineShift.lean`, `Linear/BinaryLowerRankFamily.lean`, `Linear/LowerRankObservableDifference.lean`, `Linear/MarkedProjectionBounds.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/NativeRankIteration.lean`, `Nilpotent/NativeRankZeroNiltest.lean`, `Polynomial/LocalPhaseMarkedObservable.lean`, `Polynomial/MarkedPolynomialGenerators.lean`, `Polynomial/PhaseBandCoordinateLifts.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B186
import Definitions.Def_OAIE3v2B187
import Definitions.Def_OAIE3v2B188

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeRankZeroNiltest
namespace OAI

section

namespace Erdos3.NativeDegreeRankFamily

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily (s + 1) 0 A p)

theorem lowerComponent_eval (i : Fin W.outputDim) (a : A) (n : ℤ) :
    (W.lowerComponent i a).eval (fun _ => n) = W.eval i a n := by
  rw [lowerComponent, RationalFilteredNilmanifold.Niltest.dropTop_eval, W.component_eval]

theorem lowerComponent_evalCyclic (N : ℕ) [NeZero N] (i : Fin W.outputDim) (a : A) (n : ZMod N) :
    (W.lowerComponent i a).evalCyclic N (fun _ => n) = W.evalCyclic N i a n :=
  W.lowerComponent_eval i a _

theorem lowerComponent_complexity (hp : 0 ≤ p) (i : Fin W.outputDim) (a : A) :
    (W.lowerComponent i a).ComplexityLE (p + 4) :=
  (W.component i a).dropTop_complexity W.rankZero_top_eq_bot (W.component_complexity hp i a)

end Erdos3.NativeDegreeRankFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem projectedDenominator_bound (hP : 0 ≤ P) :
    (D.projectedDenominator : ℝ) ≤ Real.exp ((P + 2) ^ 3 + P) := by
  have hdim := D.adapted_complexity.1.1
  apply NilpotentLieFiltration.original_coordinate_denominator_bound D.adapted.basis
    (pi (I.productModels D.index)).basis hP
  · simpa only [Fintype.card_fin] using hdim
  · simpa only [← finrank_eq_card_basis (pi (I.productModels D.index)).basis] using hdim
  · exact D.forward
  · exact D.denominator_bound

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonUniformCoefficientCorrections
namespace OAI

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval.SunflowerWitness

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q}

theorem mono_projectedDenominator (D : I.SunflowerWitness P) (hPQ : P ≤ Q) :
    (D.mono hPQ).projectedDenominator = D.projectedDenominator := rfl

end NativeRankInterval.SunflowerWitness

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BinaryLowerRankFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

def HasUniformLowerRankUnitFamily {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure (r + 1))
    (v : I → D.Space → ℂ) (w : σ → ℕ) (p : ℝ) : Prop :=
  ∃ n : ℕ, n ≤ d ∧
    ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
      ∃ U : Q.DegreeRankStructure r, U.ComplexityLE p ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
           IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 Q.basis
         ∃ K : I → Q.Niltest w,
           (∀ i, (K i).normBound = 1) ∧ (∀ i, (K i).ComplexityLE p) ∧
           (∀ y : Q.Space, ∑ i, ‖(K i).observable y‖ ^ 2 = 1) ∧
           ∃ a : D.filtration.realification.PolynomialOrbit w →
               Q.filtration.realification.PolynomialOrbit w,
             (∀ g, D.filtration.realification.polynomialOrbitEval w 0 g = 1 →
               Q.filtration.realification.polynomialOrbitEval w 0 (a g) = 1) ∧
             ∀ g i x, ((K i).withOrbit (a g)).eval x = v i
               (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)))

universe u v t

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalDifference
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators NNReal

variable {L I J : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] [Fintype J]
  {s d : ℕ} [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p) (U : D.UnitVerticalObservable T J p)

noncomputable def differenceObservable (a : I × J) (x : D.Space) : ℂ :=
  V.observable a.1 x * star (U.observable a.2 x)

theorem differenceObservable_unit (x : D.Space) :
    ∑ a, ‖V.differenceObservable U a x‖ ^ 2 = 1 := by
  simp only [differenceObservable, norm_mul, norm_star, mul_pow, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, U.unit, mul_one, V.unit]

theorem differenceObservable_norm (a : I × J) (x : D.Space) :
    ‖V.differenceObservable U a x‖ ≤ 1 := by
  simpa only [differenceObservable, norm_mul, norm_star, mul_one] using
    mul_le_mul (V.norm a.1 x) (U.norm a.2 x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem differenceObservable_lipschitz (a : I × J) :
    letI := D.metricSpace
    LipschitzWith (V.lipBound + U.lipBound) (V.differenceObservable U a) := by
  let := D.metricSpace
  exact (lipschitz_mul_star_of_bounds (V.observable a.1) (U.observable a.2)
    (Bf := 1) (Bg := 1) (V.lipschitz a.1) (U.lipschitz a.2)
    (V.norm a.1) (U.norm a.2)).weaken (by simp only [one_mul]; exact le_of_eq (add_comm _ _))

variable {r : ℕ} (R : D.DegreeRankStructure r)
  (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
  (U : D.UnitVerticalObservable (R.realSubgroup s r) J p)
  (hfreq : ∀ x ∈ R.filtration.layer s r, V.frequency x = U.frequency x)

include hfreq in
theorem differenceObservable_rank_invariant (a : I × J) (z : D.RealGroup)
    (hz : z ∈ R.realSubgroup s r) (x : D.Space) :
    V.differenceObservable U a (z • x) = V.differenceObservable U a x := by
  have heq := realifyFunctional_eq_on_submodule (R.filtration.layer s r)
    V.frequency U.frequency hfreq z.coord hz
  let c := CircleFourier.character
    ((realifyFunctional U.frequency z.coord : ℝ) : CircleFourier.Circle)
  have hc : c * star c = 1 := by
    dsimp only [c]
    rw [← CircleFourier.character_neg, ← CircleFourier.character_add,
      add_neg_cancel, CircleFourier.character_zero]
  unfold differenceObservable
  rw [V.vertical a.1 z hz, U.vertical a.2 z hz, heq, star_mul]
  change (c * V.observable a.1 x) * (star (U.observable a.2 x) * star c) = _
  calc
    _ = (c * star c) * (V.observable a.1 x * star (U.observable a.2 x)) := by ring
    _ = _ := by rw [hc, one_mul]

noncomputable def rankDifference :
    D.UnitVerticalObservable (R.realSubgroup s r) (I × J) (p + 2) where
  observable := V.differenceObservable U
  unit := V.differenceObservable_unit U
  norm := V.differenceObservable_norm U
  lipBound := V.lipBound + U.lipBound
  lip_bound := by
    change (V.lipBound : ℝ) + U.lipBound ≤ Real.exp (p + 2)
    calc
      _ ≤ 2 * Real.exp p := by linarith [V.lip_bound, U.lip_bound]
      _ ≤ Real.exp 2 * Real.exp p := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  lipschitz := V.differenceObservable_lipschitz U
  frequency := 0
  height i := by
    have hp := (rationalLogHeight_nonneg (V.frequency (D.basis i))).trans (V.height i)
    simpa [rationalLogHeight] using (show (0 : ℝ) ≤ p + 2 by linarith)
  vertical a z hz x := by
    simpa only [realifyFunctional_zero, AddCircle.coe_zero,
      CircleFourier.character_zero, one_mul] using
      differenceObservable_rank_invariant R V U hfreq a z hz x
  integral _ _ _ := ⟨0, by simp only [realifyFunctional_zero, Int.cast_zero]⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LowerRankObservableDifference
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem HasUniformLowerRankUnitFamily.mono {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype I] {s r d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {R : D.DegreeRankStructure (r + 1)} {v : I → D.Space → ℂ} {w : σ → ℕ}
    {p q : ℝ} (h : HasUniformLowerRankUnitFamily D R v w p) (hpq : p ≤ q) :
    HasUniformLowerRankUnitFamily D R v w q := by
  obtain ⟨n, hn, Q, S, hS, hK⟩ := h
  refine ⟨n, hn, Q, S, hS.mono S hpq, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, hKe⟩ := hK
  exact ⟨K, hKn, (fun i => (hKc i).mono hpq), hKu, a, ha0, hKe⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredQuotientCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {L M I J : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] [Fintype J] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup D.RealGroup} {S : Subgroup E.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p) (U : E.UnitVerticalObservable S J p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

noncomputable def mapDifferenceObservable (a : I × J) (x : D.Space) : ℂ :=
  V.observable a.1 x * star (U.observable a.2 (D.nativeSpaceMap E φ hφ x))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialGenerators
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedPolynomialAlgebra_le_adapted {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) :
    markedPolynomialAlgebra (σ := σ) v w marked ≤ F.associatedDegree.adaptedLieSubalgebra (fun _ => 1) := by
  intro p hp α
  have ha := hp α
  rw [Nat.zero_add] at ha
  exact markedLieSpan_le_markedDegree F v w marked hw hv 0 _ 0 ha

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {I σ L : Type*} [Fintype I] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem finiteMarkedPolynomialValues_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ finiteMarkedPolynomialValues v w marked s d k l) :
    p ∈ markedPolynomialLayer v w marked d k l := by
  classical
  obtain ⟨α, _, hα⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hα
  exact monomial_mem_markedPolynomialLayer v w marked d k l α
    (finiteMarkedLieValues_mem v w marked s d _ l hx)

theorem monomial_mem_span_finiteMarkedPolynomialValues {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
    (d k l : ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight (fun _ : σ => 1) α ≤ s)
    {x : L} (hx : x ∈ markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l) :
    monomial (R := ℚ) α x ∈
      Submodule.span ℚ (finiteMarkedPolynomialValues (σ := σ) v w marked s d k l : Set (VectorPolynomial σ ℚ L)) := by
  classical
  rw [markedLieSpan_eq_finite_span F v w marked hw hv] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    exact Submodule.subset_span (Finset.mem_biUnion.mpr
      ⟨α, (mem_markedParameterExponents s α).mpr hα, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩)
  | zero => simp only [monomial, TensorProduct.tmul_zero, Submodule.zero_mem]
  | add y z _ _ hy hz =>
    simpa only [monomial, TensorProduct.tmul_add] using Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    simpa only [monomial, TensorProduct.tmul_smul] using Submodule.smul_mem _ c hy

theorem markedPolynomialLayer_eq_finite_span {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedPolynomialLayer (σ := σ) v w marked d k l =
      Submodule.span ℚ (finiteMarkedPolynomialValues (σ := σ) v w marked s d k l : Set (VectorPolynomial σ ℚ L)) := by
  classical
  apply le_antisymm
  · intro p hp
    have hdeg := (degreeLE_iff (fun _ : σ => 1) s p).mp
      (markedPolynomialLayer_degreeLE F v w marked hw hv hp)
    rw [← sum_monomial_coefficients p]
    simp only [Finsupp.sum]
    apply Submodule.sum_mem
    intro α hα
    exact monomial_mem_span_finiteMarkedPolynomialValues F v w marked hw hv d k l α
      (hdeg α hα) (hp α)
  · exact Submodule.span_le.mpr
      (fun _ hp => finiteMarkedPolynomialValues_mem v w marked s d k l hp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds
namespace OAI

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

theorem markedShiftDirection_lie_left (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    (⁅markedShiftDirection F v w marked t h, x⁆).val.left.val =
      directionalDerivative h x.val.left.val := by
  change ⁅(0 : VectorPolynomial (Fin t) ℚ L), x.val.left.val⁆ +
    directionalDerivative h x.val.left.val - directionalDerivative x.val.right 0 = _
  have hz : ⁅(0 : VectorPolynomial (Fin t) ℚ L), x.val.left.val⁆ = 0 :=
    zero_lie (L := VectorPolynomial (Fin t) ℚ L) x.val.left.val
  have hd : directionalDerivative x.val.right (0 : VectorPolynomial (Fin t) ℚ L) = 0 := map_zero _
  exact (congrArg₂ (fun a b : VectorPolynomial (Fin t) ℚ L =>
    a + directionalDerivative h x.val.left.val - b) hz hd).trans (by simp)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def markedPolynomialGeneratorFamily (t d k l : ℕ)
    (p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l) :
    markedPolynomialLayer (σ := Fin t) v w marked d k l :=
  ⟨p.val, finiteMarkedPolynomialValues_mem v w marked s d k l p.property⟩

include hw hv in
theorem markedPolynomialGeneratorFamily_span (t d k l : ℕ) :
    Submodule.span ℚ (Set.range (markedPolynomialGeneratorFamily (s := s) v w marked t d k l)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  have hrange : Set.range (fun p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l =>
      (p.val : VectorPolynomial (Fin t) ℚ L)) =
      (finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l : Set (VectorPolynomial (Fin t) ℚ L)) := by
    ext p
    exact ⟨fun ⟨q, hq⟩ => hq ▸ q.property, fun hp => ⟨⟨p, hp⟩, rfl⟩⟩
  change Submodule.span ℚ (Set.range (fun p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l =>
    (p.val : VectorPolynomial (Fin t) ℚ L))) = _
  rw [hrange]
  exact (markedPolynomialLayer_eq_finite_span F v w marked hw hv d k l).symm

noncomputable def markedShiftLayerPolynomialMap (t d k l : ℕ) :
    markedPolynomialLayer (σ := Fin t) v w marked d k l →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun p :=
    let hp := markedPolynomialLayer_antitone v w marked (Nat.zero_le d) (Nat.zero_le k) (Nat.zero_le l) p.property
    ⟨⟨⟨p.val, markedPolynomialAlgebra_le_adapted F v w marked hw hv hp⟩, 0⟩, hp⟩
  map_add' p q := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      rfl
    · exact (zero_add (0 : RationalTorus.Algebra t)).symm
  map_smul' c p := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      rfl
    · exact (smul_zero c : c • (0 : RationalTorus.Algebra t) = 0).symm

noncomputable def markedShiftGenerator (t h n : ℕ) :
    MarkedShiftGeneratorIndex (s := s) v w marked t h n → markedShiftSubalgebra F v w marked t
  | .inl p => markedShiftLayerPolynomialMap F v w marked hw hv t n h 0
      (markedPolynomialGeneratorFamily v w marked t n h 0 p)
  | .inr i => markedShiftDirectionMap F v w marked t (RationalTorus.basis t i.val)

theorem markedShiftGenerator_mem (t h n : ℕ)
    (i : MarkedShiftGeneratorIndex (s := s) v w marked t h n) :
    markedShiftGenerator F v w marked hw hv t h n i ∈ markedShiftBiLayer F v w marked t h n := by
  rcases i with p | i
  · exact ⟨finiteMarkedPolynomialValues_mem v w marked s n h 0 p.property, fun _ => rfl⟩
  · refine ⟨(markedPolynomialLayer v w marked n h 0).zero_mem, ?_⟩
    intro hc
    have hi := i.property
    omega

theorem markedShiftGenerator_span (t h n : ℕ) :
    Submodule.span ℚ (Set.range (markedShiftGenerator F v w marked hw hv t h n)) =
      markedShiftBiLayer F v w marked t h n := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ ⟨i, hi⟩ => hi ▸ markedShiftGenerator_mem F v w marked hw hv t h n i)
  · intro x hx
    let S := Submodule.span ℚ (Set.range (markedShiftGenerator F v w marked hw hv t h n))
    have hpoly (p : markedPolynomialLayer (σ := Fin t) v w marked n h 0) :
        markedShiftLayerPolynomialMap F v w marked hw hv t n h 0 p ∈ S := by
      have hp : p ∈ Submodule.span ℚ
          (Set.range (markedPolynomialGeneratorFamily (s := s) v w marked t n h 0)) := by
        rw [markedPolynomialGeneratorFamily_span F v w marked hw hv]
        trivial
      induction hp using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨i, rfl⟩ := hq
        exact Submodule.subset_span ⟨.inl i, rfl⟩
      | zero => rw [map_zero]; exact S.zero_mem
      | add p q _ _ hp hq => rw [map_add]; exact S.add_mem hp hq
      | smul c p _ hp => rw [map_smul]; exact S.smul_mem c hp
    have hdir : markedShiftDirectionMap F v w marked t x.val.right ∈ S := by
      by_cases ha : n = 0 ∧ h ≤ 1
      · rw [← (RationalTorus.basis t).sum_repr x.val.right, map_sum]
        apply S.sum_mem
        intro i _
        rw [map_smul]
        exact S.smul_mem _ (Submodule.subset_span ⟨.inr ⟨i, ha⟩, rfl⟩)
      · rw [hx.2 (by omega), map_zero]
        exact S.zero_mem
    have he : markedShiftLayerPolynomialMap F v w marked hw hv t n h 0 ⟨x.val.left.val, hx.1⟩ +
        markedShiftDirectionMap F v w marked t x.val.right = x := by
      apply Subtype.ext
      apply LieAlgebra.SemiDirectSum.ext
      · apply Subtype.ext
        change x.val.left.val + 0 = x.val.left.val
        exact add_zero _
      · change 0 + x.val.right = x.val.right
        exact zero_add _
    exact he ▸ S.add_mem (hpoly ⟨x.val.left.val, hx.1⟩) hdir

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def markedShiftTranslate (h : Fin t → ℚ) :
    markedShiftSubalgebra F v w marked t →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun x :=
    ⟨⟨⟨translate h x.val.left.val,
        markedPolynomialAlgebra_le_adapted F v w marked hw hv
          (markedPolynomialLayer_translate v w marked h x.property)⟩, x.val.right⟩,
      markedPolynomialLayer_translate v w marked h x.property⟩
  map_add' x y := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (VectorPolynomial.translate h).map_add x.val.left.val y.val.left.val
    · rfl
  map_smul' a x := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (VectorPolynomial.translate h).map_smul a x.val.left.val
    · rfl

theorem markedShiftEval_translate (h a : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    markedShiftEval F v w marked t a (markedShiftTranslate F v w marked hw hv t h x) =
      markedShiftEval F v w marked t (a + h) x :=
  eval_translate h a x.val.left.val

theorem markedShiftTranslate_second_mem (h : Fin t → ℚ) {x : markedShiftSubalgebra F v w marked t}
    (hx : x ∈ markedShiftSecondIdeal F v w marked t) :
    markedShiftTranslate F v w marked hw hv t h x ∈ markedShiftSecondIdeal F v w marked t :=
  ⟨hx.1, markedPolynomialLayer_translate v w marked h hx.2⟩

noncomputable def markedQuotientTranslate (h : Fin t → ℚ) :
    MarkedShiftQuotient F v w marked t →ₗ[ℚ] MarkedShiftQuotient F v w marked t :=
  (markedShiftSecondIdeal F v w marked t).toSubmodule.liftQ
    ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.comp
      (markedShiftTranslate F v w marked hw hv t h)) (by
        intro x hx
        exact (lieQuotientMap_eq_zero _ _).mpr (markedShiftTranslate_second_mem F v w marked hw hv t h hx))

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

variable {I σ ι L : Type*} [Fintype I] [Fintype σ] [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L]

theorem finiteMarkedPolynomialValues_coefficient_height
    (b : Basis ι ℚ L) (v : I → L) (w : I → ℕ) (marked : I → Bool) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H) (s d k l : ℕ)
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ finiteMarkedPolynomialValues v w marked s d k l)
    (α : σ →₀ ℕ) (j : ι) :
    RationalHeightLE (b.repr (coefficients p α) j) (lieTreeHeight (Fintype.card ι) H s) := by
  classical
  obtain ⟨β, _, hβ⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hβ
  rw [coefficients_monomial]
  by_cases h : β = α
  · subst β
    rw [Finsupp.single_eq_same]
    exact finiteMarkedLieValues_coordinate_height b v w marked hc hv s d _ l hx j
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (hH.trans (lieTreeHeight_ge_input _ _ _))

variable {s r : ℕ} (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

omit [Fintype σ] in
include hH hc hgen in
theorem markedShiftGenerator_coordinate_height (t h n : ℕ)
    (i : MarkedShiftGeneratorIndex (s := s) v w marked t h n)
    (j : NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (markedShiftGenerator F v w marked hw hv t h n i).val j)
      (lieTreeHeight (Fintype.card ι) H s) := by
  have hbound := hH.trans (lieTreeHeight_ge_input (Fintype.card ι) H s)
  rcases i with p | i
  · rcases j with z | j
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inl]
      exact finiteMarkedPolynomialValues_coefficient_height b v w marked hH hc hgen s n h 0
        p.property z.val.1 z.val.2
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inr]
      exact rationalHeightLE_zero hbound
  · rcases j with z | j
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inl]
      change RationalHeightLE (b.repr (coefficients (0 : VectorPolynomial (Fin t) ℚ L) z.val.1) z.val.2) _
      simp only [map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero hbound
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inr]
      change RationalHeightLE ((RationalTorus.basis t).repr (RationalTorus.basis t i.val) j) _
      exact (basis_repr_height_one (RationalTorus.basis t) i.val j).mono hbound

omit [Fintype σ] in
include hw hv hH hc hgen in
theorem exists_markedShiftLayer_bounded_basis (hω : ∀ i, ω i ≤ s) (t h n : ℕ) :
    ∃ e : Basis (Fin (finrank ℚ (markedShiftBiLayer F v w marked t h n))) ℚ
        (markedShiftBiLayer F v w marked t h n),
      ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
        (e i).val.val j) (lieTreeHeight (Fintype.card ι) H s) := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (Set.range (markedShiftGenerator F v w marked hw hv t h n))
  rw [markedShiftGenerator_span] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro i j
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz i
  rw [← hk]
  exact markedShiftGenerator_coordinate_height F b ω hF v w marked hw hv hH hc hgen t h n k j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedPureEvaluation
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
  (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (E : RationalFilteredNilmanifold (L ⧸ J) u e) (a : Fin t → ℚ)

noncomputable def markedPureEvaluation
    (g : realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t)) : E.RealGroup :=
  ⟨(markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ g.val.coord⟩

theorem markedPureEvaluation_inclusion
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] markedQuotientPolynomialAlgebra F v w marked t) (s + 1)
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot
        D.filtration.lowerCentralSeries_eq_bot (markedQuotientPolynomialAlgebra F v w marked t)))) :
    markedPureEvaluation F v w marked t D J hJ E a
      (realificationSubgroupHom (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (markedQuotientPolynomialAlgebra F v w marked t) g) =
      realificationMap
        (hnil := lie_subalgebra_lowerCentralSeries_eq_bot D.filtration.lowerCentralSeries_eq_bot
          (markedQuotientPolynomialAlgebra F v w marked t))
        (hM := E.filtration.lowerCentralSeries_eq_bot)
        (markedBaseEvaluationLie F v w marked t J hJ a) g := by
  apply NilpotentLieBCHGroup.ext
  exact markedBaseEvaluation_real_incl F v w marked t J hJ a g.coord

noncomputable def markedPureEvaluationHom :
    realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t) →* E.RealGroup :=
  monoidHomOfSurjectiveComposition
    (realificationSubgroupHom (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t))
    (realificationSubgroupHom_surjective (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t))
    (realificationMap
      (hnil := lie_subalgebra_lowerCentralSeries_eq_bot D.filtration.lowerCentralSeries_eq_bot
        (markedQuotientPolynomialAlgebra F v w marked t))
      (hM := E.filtration.lowerCentralSeries_eq_bot) (markedBaseEvaluationLie F v w marked t J hJ a))
    (markedPureEvaluation F v w marked t D J hJ E a)
    (markedPureEvaluation_inclusion F v w marked t D J hJ E a)

variable (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
  (⟨(markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)

include hmap in
theorem markedPureEvaluationHom_lattice :
    D.realLattice.comap (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t)).subtype ≤
        E.realLattice.comap (markedPureEvaluationHom F v w marked t D J hJ E a) := by
  intro g hg
  exact hmap g.val hg

noncomputable def markedPureSpaceMap :
    (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t) ⧸
        D.realLattice.comap (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (markedQuotientPolynomialAlgebra F v w marked t)).subtype) → E.Space :=
  cosetMap _ _ (markedPureEvaluationHom F v w marked t D J hJ E a)
    (markedPureEvaluationHom_lattice F v w marked t D J hJ E a hmap)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MarkedProjectionBounds
namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hw hv hH hc hgen in
theorem exists_markedShift_bounded_basis (hω : ∀ i, ω i ≤ s) (t : ℕ) :
    ∃ e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
        (markedShiftSubalgebra F v w marked t),
      ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
        (e i).val j) (lieTreeHeight (Fintype.card ι) H s) := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (Set.range (markedShiftGenerator F v w marked hw hv t 0 0))
  rw [markedShiftGenerator_span, markedShiftBiLayer_zero, finrank_top] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  let e := Basis.mk hzli (le_of_eq hzspan.symm)
  refine ⟨e, ?_⟩
  intro i j
  simp only [e, Basis.mk_apply]
  obtain ⟨k, hk⟩ := hz i
  rw [← hk]
  exact markedShiftGenerator_coordinate_height F b ω hF v w marked hw hv hH hc hgen t 0 0 k j

include hw hv hH hc hgen in
theorem exists_markedShiftLayer_coordinate_basis (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s)) (h n : ℕ) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∃ c : Basis (Fin (finrank ℚ (markedShiftBiLayer F v w marked t h n))) ℚ
        (markedShiftBiLayer F v w marked t h n),
      ∀ i j, RationalHeightLE (e.repr (c i).val j)
        ((a + 1) * (rationalSolveHeight d T * T) ^ a) := by
  classical
  dsimp only
  let _ : Fintype (NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω) :=
    NilpotentLieFiltration.adaptedBasisIndexFintype (fun _ : Fin t => 1) ω s (by simp) hω
  obtain ⟨c, hc'⟩ := exists_markedShiftLayer_bounded_basis F b ω hF v w marked hw hv hH hc hgen hω t h n
  refine ⟨c, ?_⟩
  intro i j
  have hb := embedding_basis_coordinate_height e (F.associatedDegree.polynomialShiftBasis b ω hF t)
    (markedShiftSubalgebra F v w marked t).incl.toLinearMap
    (fun _ _ h => Subtype.ext h) (hH.trans (lieTreeHeight_ge_input _ _ _))
    (fun j i => he i j) (c i).val (hc' i) j
  simpa only [Fintype.card_fin,
    ← finrank_eq_card_basis (F.associatedDegree.polynomialShiftBasis b ω hF t)] using hb

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hw hv hH hc hgen in
theorem exists_markedShiftQuotient_bounded_coordinates (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s)) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
    ∃ m : ℕ, m ≤ finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ∧
      ∃ q : ℕ, q ≤ d ∧ ∃ f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t),
        ∀ i j, RationalHeightLE
          (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i)
          (rationalKernelHeight m B) := by
  let T := lieTreeHeight (Fintype.card ι) H s
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  have hT : 1 ≤ T := hH.trans (lieTreeHeight_ge_input _ _ _)
  have hsolve : 0 < rationalSolveHeight d T := rationalSolveHeight_pos d hT
  have hB : 1 ≤ B := by
    have hTpos : 0 < T := Nat.zero_lt_of_lt hT
    exact Nat.one_le_iff_ne_zero.mpr (by dsimp [B]; positivity)
  have hex := exists_markedShiftLayer_coordinate_basis F b ω hF v w marked hw hv hH hc hgen hω t e he 2 0
  dsimp only at hex
  rw [markedShiftBiLayer_second] at hex
  obtain ⟨c, hc'⟩ := hex
  have hcoords : ∀ i j, RationalHeightLE (e.repr (c i).val j) B := hc'
  obtain ⟨m, hm, q, hq, f, hf⟩ := exists_bounded_submodule_quotient_basis e
    (markedShiftSecondIdeal F v w marked t).toSubmodule (fun i => (c i).val)
    (span_submodule_basis _ c) hB hcoords
  refine ⟨m, ?_, q, ?_, f, hf⟩
  · simpa only [Fintype.card_fin] using hm
  · simpa only [Fintype.card_fin] using hq

include hw hv hH hc hgen in
theorem exists_markedShiftQuotientLayer_bounded_basis (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s))
    {q Q : ℕ} (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
    (hf : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)
    (α : Fin 2 → ℕ) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
    ∃ c : Basis (Fin (finrank ℚ (markedShiftQuotientLayer F v w marked t α))) ℚ
        (markedShiftQuotientLayer F v w marked t α),
      ∀ i j, RationalHeightLE (f.repr (c i).val j) ((d + 1) * (B * Q) ^ d) := by
  dsimp only
  obtain ⟨c, hc'⟩ := exists_markedShiftLayer_coordinate_basis F b ω hF v w marked hw hv hH hc hgen
    hω t e he (α 0) (α 1)
  let π := (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
  have hspan : Submodule.span ℚ (Set.range (fun i => π (c i).val)) =
      markedShiftQuotientLayer F v w marked t α := by
    change Submodule.span ℚ (Set.range (π ∘ (fun i => (c i).val))) = _
    rw [Set.range_comp, ← Submodule.map_span, span_submodule_basis]
    rfl
  apply exists_bounded_submodule_basis_from_spanning f _ (fun i => π (c i).val) hspan
  intro i j
  have h := linearMap_coordinate_height e f π (fun i j => hf j i) (c i).val (hc' i) j
  simpa only [Fintype.card_fin] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MarkedDirectionCoordinates
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

omit [Fintype ι] in
theorem markedShiftDirection_ambient_height (i : Fin t)
    (j : NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (markedShiftDirection F v w marked t (RationalTorus.basis t i)).val j) 1 := by
  rcases j with z | j
  · rw [F.associatedDegree.polynomialShiftBasis_repr_inl]
    change RationalHeightLE (b.repr (coefficients (0 : VectorPolynomial (Fin t) ℚ L) z.val.1) z.val.2) 1
    simp only [map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl
  · rw [F.associatedDegree.polynomialShiftBasis_repr_inr]
    exact basis_repr_height_one (RationalTorus.basis t) i j

theorem markedShiftDirection_coordinate_height (hω : ∀ i, ω i ≤ s) {H : ℕ} (hH : 1 ≤ H)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) H) (i : Fin t) (j : Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) :
    RationalHeightLE (e.repr (markedShiftDirection F v w marked t (RationalTorus.basis t i)) j)
      ((finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t) + 1) *
        (rationalSolveHeight (finrank ℚ (markedShiftSubalgebra F v w marked t)) H * H) ^
          finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)) := by
  classical
  let _ : Fintype (NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω) :=
    NilpotentLieFiltration.adaptedBasisIndexFintype (fun _ : Fin t => 1) ω s (by simp) hω
  have hb := embedding_basis_coordinate_height e (F.associatedDegree.polynomialShiftBasis b ω hF t)
    (markedShiftSubalgebra F v w marked t).incl.toLinearMap
    (fun _ _ h => Subtype.ext h) hH (fun j i => he i j)
    (markedShiftDirection F v w marked t (RationalTorus.basis t i))
    (fun j => (markedShiftDirection_ambient_height F v w marked t b ω hF i j).mono hH) j
  simpa only [Fintype.card_fin,
    ← finrank_eq_card_basis (F.associatedDegree.polynomialShiftBasis b ω hF t)] using hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem realMarkedTranslate_quotient (h : Fin t → ℚ)
    (x : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
        ((markedShiftTranslate F v w marked hw hv t h).baseChange ℝ x) =
      (markedQuotientTranslate F v w marked hw hv t h).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realMarkedShiftEval_translate (h a : Fin t → ℚ)
    (x : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftEval F v w marked t a).baseChange ℝ
        ((markedShiftTranslate F v w marked hw hv t h).baseChange ℝ x) =
      (markedShiftEval F v w marked t (a + h)).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, markedShiftEval_translate]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentCoveredModel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct

noncomputable def restrictVertical {L I : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype I] [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
    (V : D.UnitVerticalObservable T I p) (S : Subgroup D.RealGroup) (hS : S ≤ T) :
    D.UnitVerticalObservable S I p where
  observable := V.observable
  unit := V.unit
  norm := V.norm
  lipBound := V.lipBound
  lip_bound := V.lip_bound
  lipschitz := V.lipschitz
  frequency := V.frequency
  height := V.height
  vertical i z hz := V.vertical i z (hS hz)
  integral z hz := V.integral z (hS hz)

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct Pointwise

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

noncomputable def NativeCyclicModel.smul {degree N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (F : NativeCyclicModel degree N p f) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    NativeCyclicModel degree N p (c • f) where
  L := F.L
  dim := F.dim
  model := F.model
  test := F.test.scaleComplex c
  norm := (F.test.scaleComplex_norm hc).trans F.norm
  complexity := F.test.scaleComplex_complexity hc F.complexity
  eval x := by
    change c * f x = c * F.test.evalCyclic N (fun _ => x)
    rw [F.eval x]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

structure NativeVerticalDerivativeData {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (B : NativeCommonDerivativeModels s N p f) where
  normalized : ∀ h, B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
    (B.test h).orbit = 1
  frequency : B.L →ₗ[ℚ] ℚ
  height : ∀ i, rationalLogHeight (frequency (B.model.basis i)) ≤ p
  vertical : ∀ h z, z ∈ B.model.filtration.realification.subgroup s → ∀ x,
    (B.test h).observable (z • x) =
      CircleFourier.character ((realifyFunctional frequency z.coord : ℝ) : CircleFourier.Circle) *
        (B.test h).observable x
  integral : ∀ z : B.model.RealGroup, z ∈ B.model.filtration.realification.subgroup s →
    z ∈ B.model.realLattice → ∃ n : ℤ, realifyFunctional frequency z.coord = n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MarkedDirectionLatticeScale
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

namespace RationalFilteredNilmanifold

variable {L V : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
  {s d t : ℕ} (E : RationalFilteredNilmanifold L s d) (e : Basis (Fin t) ℚ V)
  (φ : V →ₗ[ℚ] L)

theorem exists_direction_lattice_scale {H : ℕ}
    (hφ : ∀ i j, RationalHeightLE (E.basis.repr (φ (e i)) j) H) :
    ∃ m : ℕ, 0 < m ∧ m ≤ E.grid * H ^ (d * t) ∧
      ∀ x : V, IntegralVector (e.equivFun x) →
        (⟨(m : ℚ) • φ x⟩ : E.filtration.Group) ∈ E.lattice := by
  classical
  let A := LinearMap.toMatrix e E.basis φ
  let m := E.grid * matrixDenominator A
  have hA : ∀ j i, RationalHeightLE (A j i) H := by
    intro j i
    simpa only [A, LinearMap.toMatrix_apply] using hφ i j
  have hm : m ≤ E.grid * H ^ (d * t) := by
    exact Nat.mul_le_mul_left _ (by simpa only [Fintype.card_fin] using matrixDenominator_le A hA)
  refine ⟨m, Nat.mul_pos E.grid_pos (matrixDenominator_pos A), hm, ?_⟩
  intro x hx
  apply (bchSubgroupCoordinates_repr E.basis E.lattice _).mp
  apply E.inner_grid
  have he : A *ᵥ e.equivFun x = E.basis.equivFun (φ x) :=
    LinearMap.toMatrix_mulVec_repr e E.basis φ x
  have hint := integralVector_denominator_mulVec A (e.equivFun x) hx
  rw [he] at hint
  obtain ⟨z, hz⟩ := hint
  refine ⟨z, ?_⟩
  change E.basis.equivFun ((m : ℚ) • φ x) = _
  calc
    _ = (E.grid : ℚ) • ((matrixDenominator A : ℚ) • E.basis.equivFun (φ x)) := by
      simp only [m, Nat.cast_mul, map_smul, mul_smul]
    _ = _ := congrArg (fun v : Fin d → ℚ => (E.grid : ℚ) • v) (funext hz)

theorem exists_direction_lattice_scale_with_budget {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hgrid : (E.grid : ℝ) ≤ Real.exp p) (hH : (H : ℝ) ≤ Real.exp p)
    (hφ : ∀ i j, RationalHeightLE (E.basis.repr (φ (e i)) j) H) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∀ x : V, IntegralVector (e.equivFun x) →
        (⟨(m : ℚ) • φ x⟩ : E.filtration.Group) ∈ E.lattice := by
  obtain ⟨m, hm, hmb, hmem⟩ := E.exists_direction_lattice_scale e φ hφ
  exact ⟨m, hm, (Nat.cast_le.mpr hmb).trans
    (direction_lattice_scale_bound d t E.grid H hp hd ht hgrid hH), hmem⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

namespace VectorPolynomial

variable {σ L : Type*} [AddCommGroup L] [Module ℚ L]

theorem realMonomial_eval (α : σ →₀ ℕ) (x : ℝ ⊗[ℚ] L) (a : σ → ℚ) :
    (eval a).baseChange ℝ ((monomialLinearMap α).baseChange ℝ x) =
      (α.prod (fun i n => a i ^ n)) • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    change r ⊗ₜ[ℚ] eval a (monomial α x) = (α.prod (fun i n => a i ^ n)) • (r ⊗ₜ[ℚ] x)
    rw [eval_monomial, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem realAffinePolynomial_eval [Fintype σ] (x : ℝ ⊗[ℚ] L) (y : σ → ℝ ⊗[ℚ] L) (a : σ → ℚ) :
    (eval a).baseChange ℝ (realAffinePolynomial x y) = x + ∑ i, a i • y i := by
  classical
  simp only [realAffinePolynomial, map_add, map_sum, realMonomial_eval,
    Finsupp.prod_zero_index, one_smul, Finsupp.prod_single_index, pow_one, pow_zero]

end VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realAffinePolynomial_mem_marked [Fintype σ]
    (v : I → L) (w : I → ℕ) (marked : I → Bool) {d k l : ℕ}
    {x : ℝ ⊗[ℚ] L} {y : σ → ℝ ⊗[ℚ] L}
    (hx : x ∈ (markedLieSpan v w marked d k l).baseChange ℝ)
    (hy : ∀ i, y i ∈ (markedLieSpan v w marked d (k + 1) l).baseChange ℝ) :
    realAffinePolynomial x y ∈ (markedPolynomialLayer v w marked d k l).baseChange ℝ := by
  apply Submodule.add_mem
  · apply realMonomial_mem_markedPolynomialLayer v w marked d k l 0
    simpa only [map_zero, Nat.add_zero] using hx
  · apply Submodule.sum_mem
    intro i _
    apply realMonomial_mem_markedPolynomialLayer v w marked d k l (Finsupp.single i 1)
    simpa only [Finsupp.weight_single, one_smul] using hy i

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

theorem markedShiftLayerPolynomialMap_mem (t d k l : ℕ)
    (p : markedPolynomialLayer (σ := Fin t) v w marked d k l) :
    markedShiftLayerPolynomialMap F v w marked hw hv t d k l p ∈
      markedShiftBiLayer F v w marked t k d := by
  refine ⟨?_, fun _ => rfl⟩
  exact markedPolynomialLayer_antitone v w marked le_rfl le_rfl (Nat.zero_le l) p.property

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def realMarkedPolynomialLift (t d k l : ℕ) :
    (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] (markedShiftSubalgebra F v w marked t) :=
  ((markedShiftLayerPolynomialMap F v w marked hw hv t d k l).baseChange ℝ).comp
    (realificationSubmoduleEquiv (markedPolynomialLayer (σ := Fin t) v w marked d k l)).symm.toLinearMap

theorem realMarkedPolynomialLift_mem (t d k l : ℕ)
    (p : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) :
    realMarkedPolynomialLift F v w marked hw hv t d k l p ∈
      (markedShiftBiLayer F v w marked t k d).baseChange ℝ := by
  obtain ⟨z, rfl⟩ := (realificationSubmoduleEquiv _).surjective p
  change (markedShiftLayerPolynomialMap F v w marked hw hv t d k l).baseChange ℝ
    ((realificationSubmoduleEquiv _).symm (realificationSubmoduleEquiv _ z)) ∈ _
  rw [LinearEquiv.symm_apply_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      (markedShiftLayerPolynomialMap_mem F v w marked hw hv t d k l z)
  | add z z' hz hz' => simpa only [map_add] using Submodule.add_mem _ hz hz'

theorem realMarkedPolynomialLift_eval (t d k l : ℕ)
    (p : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) (a : Fin t → ℚ) :
    (markedShiftEval F v w marked t a).baseChange ℝ
      (realMarkedPolynomialLift F v w marked hw hv t d k l p) =
        (eval a).baseChange ℝ p.val := by
  obtain ⟨z, rfl⟩ := (realificationSubmoduleEquiv _).surjective p
  change (markedShiftEval F v w marked t a).baseChange ℝ
    ((markedShiftLayerPolynomialMap F v w marked hw hv t d k l).baseChange ℝ
      ((realificationSubmoduleEquiv _).symm (realificationSubmoduleEquiv _ z))) = _
  rw [LinearEquiv.symm_apply_apply]
  rw [realificationSubmoduleEquiv_coe]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a z => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

noncomputable def realMarkedQuotientCoefficient (t d k l : ℕ) :
    (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] (MarkedShiftQuotient F v w marked t) :=
  ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ).comp
    (realMarkedPolynomialLift F v w marked hw hv t d k l)

theorem realMarkedPolynomialLift_quotient_mem (t d k l : ℕ)
    (p : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) :
    realMarkedQuotientCoefficient F v w marked hw hv t d k l p ∈
        (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput k d) := by
  change _ ∈ ((markedShiftBiLayer F v w marked t k d).map
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap).baseChange ℝ
  rw [realification_map]
  exact ⟨_, realMarkedPolynomialLift_mem F v w marked hw hv t d k l p, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealMarkedAffineShift
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def realMarkedAffineShift (a : Fin t → ℝ) :
    (ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) →ₗ[ℝ]
      (ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :=
  LinearMap.id + ∑ i, a i •
    ((markedShiftTranslate F v w marked hw hv t (Pi.single i 1)).baseChange ℝ - LinearMap.id)

theorem realMarkedAffineShift_apply (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    realMarkedAffineShift F v w marked hw hv t a p =
      p + ∑ i, a i •
        ((markedShiftTranslate F v w marked hw hv t (Pi.single i 1)).baseChange ℝ p - p) := by
  simp only [realMarkedAffineShift, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply]

theorem realMarkedAffineShift_eval (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftEval F v w marked t 0).baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) =
      (markedShiftEval F v w marked t 0).baseChange ℝ p +
        ∑ i, a i • ((markedShiftEval F v w marked t (Pi.single i 1)).baseChange ℝ p -
          (markedShiftEval F v w marked t 0).baseChange ℝ p) := by
  rw [realMarkedAffineShift_apply, map_add, map_sum]
  apply congrArg ((markedShiftEval F v w marked t 0).baseChange ℝ p + ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_sub, realMarkedShiftEval_translate, zero_add]

theorem realMarkedAffineShift_eval_affine (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t)
    (x : ℝ ⊗[ℚ] L) (y : Fin t → ℝ ⊗[ℚ] L)
    (hp : ∀ b : Fin t → ℚ, (markedShiftEval F v w marked t b).baseChange ℝ p =
      x + ∑ i, (b i : ℝ) • y i) :
    (markedShiftEval F v w marked t 0).baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) = x + ∑ i, a i • y i := by
  have h0 : (markedShiftEval F v w marked t 0).baseChange ℝ p = x := by
    simpa only [Pi.zero_apply, Rat.cast_zero, zero_smul, Finset.sum_const_zero, add_zero] using hp 0
  have hi (i : Fin t) : (markedShiftEval F v w marked t (Pi.single i 1)).baseChange ℝ p = x + y i := by
    simpa [Pi.single_apply, apply_ite] using hp (Pi.single i 1)
  rw [realMarkedAffineShift_eval, h0]
  simp only [hi, add_sub_cancel_left]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem realMarkedShiftTranslate_phase (a : Fin t → ℚ)
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ
        ((markedShiftTranslate F v w marked hw hv t a).baseChange ℝ z) =
      (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c z => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realMarkedAffineShift_phase (a : Fin t → ℝ)
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a z) =
      (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ z := by
  rw [realMarkedAffineShift_apply F v w marked hw hv t a z]
  simp only [map_add, map_sum, map_smul, map_sub, realMarkedShiftTranslate_phase,
    sub_self, smul_zero, Finset.sum_const_zero, add_zero]

theorem realMarkedPolynomialLift_phase (d k l : ℕ) (hd : d ≠ 0)
    (z : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) :
    (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ
      (realMarkedPolynomialLift F v w marked hw hv t d k l z) = 0 := by
  have hker : markedShiftBiLayer F v w marked t k d ≤
      LinearMap.ker (markedShiftPhase F v w marked t).toLinearMap := by
    intro p hp
    exact hp.2 (Or.inl hd)
  have hz := Submodule.baseChange_mono ℝ hker (realMarkedPolynomialLift_mem F v w marked hw hv t d k l z)
  rwa [realification_ker, LinearMap.mem_ker] at hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PhaseBandCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem torusPhaseLinear_realLattice_integral {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
    (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))
    (γ : D.RealGroup) (hγ : γ ∈ D.realLattice) :
    ∃ a : Fin t → ℤ, torusPhaseLinear φ γ.coord = fun i => (a i : ℝ) := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨a, ha⟩ := hphase z hz
  refine ⟨a, funext fun i => ?_⟩
  change torusPhaseLinear φ ((1 : ℝ) ⊗ₜ[ℚ] z.coord) i = (a i : ℝ)
  rw [torusPhaseLinear_tmul, _root_.one_mul, ha i, Rat.cast_intCast]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t : ℕ}
  (D : RationalFilteredNilmanifold L s d) (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
  (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))

include hphase in
theorem torusPhaseLinear_eq_of_close (g h : D.RealGroup)
    (heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h)
    (hclose : dist (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord) < 1) :
    torusPhaseLinear φ g.coord = torusPhaseLinear φ h.coord := by
  obtain ⟨a, ha⟩ := torusPhaseLinear_realLattice_integral D φ hphase (g⁻¹ * h) (QuotientGroup.eq.mp heq)
  rw [torusPhaseLinear_mul, torusPhaseLinear_inv] at ha
  funext i
  have hai : -torusPhaseLinear φ g.coord i + torusPhaseLinear φ h.coord i = (a i : ℝ) := congrFun ha i
  have hi : |(a i : ℝ)| < 1 := by
    rw [← hai, neg_add_eq_sub, abs_sub_comm]
    exact (dist_le_pi_dist (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord) i).trans_lt hclose
  have hzero : a i = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hi)
  rw [hzero, Int.cast_zero] at hai
  linarith

include hphase in
theorem torusPhaseLinear_eq_in_band_of_near (g h z : D.RealGroup)
    (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
    (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4)
    (hz : (QuotientGroup.mk z : D.Space) = QuotientGroup.mk h)
    (hnear : dist (torusPhaseLinear φ z.coord) (torusPhaseLinear φ g.coord) < 1 / 4) :
    torusPhaseLinear φ z.coord = torusPhaseLinear φ h.coord := by
  apply torusPhaseLinear_eq_of_close D φ hphase z h hz
  have hgh : dist (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord) ≤ 1 / 2 := by
    have h := dist_le_norm_add_norm (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord)
    linarith
  have h := dist_triangle (torusPhaseLinear φ z.coord) (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord)
  linarith

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem torusPhaseLinear_group_lipschitz (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (φ (D.basis j) i) H) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    LipschitzWith (coordinateLipschitzBound t d H) (fun g : D.RealGroup => torusPhaseLinear φ g.coord) := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (RationalTorus.nilmanifold t).filtration.realification.lowerCentralSeries_eq_bot)
    ((RationalTorus.basis t).baseChange ℝ)
  have hf := lipschitz_realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot)
    D.basis (RationalTorus.basis t) φ H (fun i j => by
      change RationalHeightLE (φ (D.basis j) i) H
      exact hH i j)
  have hc := (RationalTorus.nilmanifold t).filtration.realification.stepOne_coordinates_lipschitz
    ((RationalTorus.basis t).baseChange ℝ)
  have h := hc.comp hf
  change LipschitzWith (1 * coordinateLipschitzBound (Fintype.card (Fin t)) (Fintype.card (Fin d)) H)
    (fun g : D.RealGroup => torusPhaseLinear φ g.coord) at h
  simpa only [one_mul, Fintype.card_fin] using h

theorem torusPhaseLinear_group_lipschitz_exp {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hcoords : ∀ i j, rationalLogHeight (φ (D.basis j) i) ≤ p) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), Real.exp_nonneg _⟩
      (fun g : D.RealGroup => torusPhaseLinear φ g.coord) := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  apply (torusPhaseLinear_group_lipschitz D φ ⌈Real.exp p⌉₊
    (fun i j => rationalHeightLE_ceil_exp (hcoords i j))).weaken
  have h := coordinateLipschitzBound_le_exp t d ⌈Real.exp p⌉₊
    (show 0 ≤ p + 1 by linarith) (ht.trans (by linarith : p ≤ p + 1))
    (hd.trans (by linarith : p ≤ p + 1)) (ceil_exp_le_exp_add_one hp)
  change (coordinateLipschitzBound t d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 2)
  simpa only [show p + 1 + 2 = p + 3 by ring] using h

include hphase in
theorem exists_nearby_phase_band_lift {K : ℝ≥0}
    (hK : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      LipschitzWith K (fun g : D.RealGroup => torusPhaseLinear φ g.coord))
    (g h : D.RealGroup)
    (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
    (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    letI := D.metricSpace
    let ρ := dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h)
    0 < ρ → (K : ℝ) * (2 * ρ) < 1 / 4 →
      ∃ z : D.RealGroup, (QuotientGroup.mk z : D.Space) = QuotientGroup.mk h ∧
        torusPhaseLinear φ z.coord = torusPhaseLinear φ h.coord ∧ dist z g < 2 * ρ := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  dsimp only
  intro hρ hnear
  let ρ := dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h)
  obtain ⟨z, hzg, hz⟩ := rightCosetMetricSpace_exists_lift D.realLattice D.realLattice_closed_discrete.1
    g (2 * ρ) (QuotientGroup.mk h) (by
      change dist (QuotientGroup.mk h : D.Space) (QuotientGroup.mk g) < 2 * ρ
      rw [dist_comm]
      change ρ < 2 * ρ
      linarith)
  refine ⟨z, hz, ?_, hzg⟩
  apply torusPhaseLinear_eq_in_band_of_near D φ hphase g h z hg hh hz
  exact ((hK.dist_le_mul z g).trans (mul_le_mul_of_nonneg_left hzg.le K.coe_nonneg)).trans_lt hnear

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem phase_band_quotient_dist_le {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t H : ℕ} (D : RationalFilteredNilmanifold L s d)
    (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
    (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (R K A : ℝ≥0) (hR : 1 ≤ R)
    (hK : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      LipschitzWith K (fun g : D.RealGroup => torusPhaseLinear φ g.coord))
    (hrep : ∀ g : D.RealGroup, ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4 →
      ∃ x : D.RealGroup, (QuotientGroup.mk x : D.Space) = QuotientGroup.mk g ∧
        torusPhaseLinear φ x.coord = torusPhaseLinear φ g.coord ∧
        ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ R)
    (u : D.RealGroup → ℂ) (hu : ∀ g, ‖u g‖ ≤ 1)
    (hsame : ∀ g h : D.RealGroup, ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4 →
      ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4 →
      (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h → u g = u h)
    (hbox : ∀ g h : D.RealGroup, ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ (R : ℝ) + 1 →
      ‖(D.basis.baseChange ℝ).equivFun h.coord‖ ≤ (R : ℝ) + 1 →
      dist (u g) (u h) ≤ A *
        dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord))
    (g h : D.RealGroup) (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
    (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4) :
    letI := D.metricSpace
    dist (u g) (u h) ≤ phaseBandQuotientConstant s d H R K A *
      dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h) := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  let C := bchLogMetricConstant s d H 1
  let B := phaseBandCoordinateConstant s d H R
  let S : ℝ := (K : ℝ) + C + B + 1
  let ρ := dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h)
  change dist (u g) (u h) ≤ (2 * (B : ℝ) * A + 16 * S) * ρ
  by_cases heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h
  · have huu := hsame g h hg hh heq
    have hρ : ρ = 0 := by simp only [ρ, heq, dist_self]
    simp only [huu, hρ, dist_self, mul_zero, le_refl]
  have hρ : 0 < ρ := dist_pos.mpr heq
  have hS : 0 ≤ S := by dsimp [S]; positivity
  by_cases hnear : S * ρ < 1 / 8
  · have hsmall (T : ℝ≥0) (hT : (T : ℝ) ≤ S) : (T : ℝ) * (2 * ρ) < 1 / 4 := by
      have ht := mul_le_mul_of_nonneg_right hT hρ.le
      nlinarith
    have hKS : (K : ℝ) ≤ S := by dsimp [S]; linarith [C.coe_nonneg, B.coe_nonneg]
    have hCS : (C : ℝ) ≤ S := by dsimp [S]; linarith [K.coe_nonneg, B.coe_nonneg]
    have hBS : (B : ℝ) ≤ S := by dsimp [S]; linarith [K.coe_nonneg, C.coe_nonneg]
    obtain ⟨x, hxq, hxp, hx⟩ := hrep g hg
    have hxphase : ‖torusPhaseLinear φ x.coord‖ ≤ 1 / 4 := by rw [hxp]; exact hg
    have hρx : dist (QuotientGroup.mk x : D.Space) (QuotientGroup.mk h) = ρ := by rw [hxq]
    obtain ⟨y, hyq, hyp, hyx⟩ := exists_nearby_phase_band_lift D φ hphase hK x h hxphase hh
      (by rw [hρx]; exact hρ) (by rw [hρx]; exact hsmall K hKS)
    rw [hρx] at hyx
    have hyphase : ‖torusPhaseLinear φ y.coord‖ ≤ 1 / 4 := by rw [hyp]; exact hh
    have hdxy : dist x y < 2 * ρ := by simpa only [dist_comm] using hyx
    have hCnear : (C : ℝ) * dist x y < 1 := by
      have ht := (mul_le_mul_of_nonneg_left hdxy.le C.coe_nonneg).trans_lt (hsmall C hCS)
      linarith
    have hcoords := dist_coordinates_le_of_near_box (D.basis.baseChange ℝ) (lieStructureConstants D.basis)
      (fun i j k => (realLieBasis_structure D.basis i j k).symm) hc R hR x y
      (fun i => by
        calc
          _ ≤ ‖(D.basis.baseChange ℝ).equivFun x.coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((D.basis.baseChange ℝ).equivFun x.coord) i
          _ ≤ R := hx)
      (by simpa only [Fintype.card_fin] using hCnear)
    have hraw : bchBoxCoordinateBound s d H R * (C : ℝ) ≤ B := by
      change bchBoxCoordinateBound s d H R * (C : ℝ) ≤
        (bchBoxCoordinateBound s d H R + 1) * (C : ℝ)
      nlinarith [C.coe_nonneg]
    have hxy : dist ((D.basis.baseChange ℝ).equivFun x.coord)
        ((D.basis.baseChange ℝ).equivFun y.coord) ≤ (B : ℝ) * dist x y := by
      apply (show _ ≤ bchBoxCoordinateBound s d H R * (C : ℝ) * dist x y by
        simpa only [Fintype.card_fin, basisHomeomorph_apply] using hcoords).trans
      exact mul_le_mul_of_nonneg_right hraw dist_nonneg
    have hxy' : dist ((D.basis.baseChange ℝ).equivFun x.coord)
        ((D.basis.baseChange ℝ).equivFun y.coord) ≤ (B : ℝ) * (2 * ρ) :=
      hxy.trans (mul_le_mul_of_nonneg_left hdxy.le B.coe_nonneg)
    have hybox : ‖(D.basis.baseChange ℝ).equivFun y.coord‖ ≤ (R : ℝ) + 1 := by
      have ht := norm_sub_norm_le ((D.basis.baseChange ℝ).equivFun y.coord)
        ((D.basis.baseChange ℝ).equivFun x.coord)
      rw [← dist_eq_norm, dist_comm] at ht
      have hclose := hxy'.trans_lt (hsmall B hBS)
      linarith
    have hux := hsame x g hxphase hg hxq
    have huy := hsame y h hyphase hh hyq
    calc
      dist (u g) (u h) = dist (u x) (u y) := by rw [hux, huy]
      _ ≤ A * dist ((D.basis.baseChange ℝ).equivFun x.coord)
          ((D.basis.baseChange ℝ).equivFun y.coord) := hbox x y (by linarith) hybox
      _ ≤ A * ((B : ℝ) * (2 * ρ)) := mul_le_mul_of_nonneg_left hxy' A.coe_nonneg
      _ ≤ (2 * (B : ℝ) * A + 16 * S) * ρ := by nlinarith [mul_nonneg hS hρ.le]
  · have hdist := (dist_le_norm_add_norm (u g) (u h)).trans (add_le_add (hu g) (hu h))
    have hf : 1 / 8 ≤ S * ρ := le_of_not_gt hnear
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * B) A.coe_nonneg) hρ.le]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedMarkedLattice
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

theorem exists_exact_source_lattice_cover {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
    (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hentries : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) :
    let Λ := D.lattice ⊓ E.lattice.comap (mapOfSteps
      (hL := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
    ∃ (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
      (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
      (N : ℝ) ≤ Real.exp ((p + 2) ^ 5) ∧
      (D.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + 2) ^ 5) := by
  classical
  let A := LinearMap.toMatrix D.basis E.basis φ.toLinearMap
  let N := D.grid * (E.grid * matrixDenominator A)
  let Λ := D.lattice ⊓ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
  have hN : 0 < N := Nat.mul_pos D.grid_pos (Nat.mul_pos E.grid_pos (matrixDenominator_pos A))
  have hDN : D.grid ∣ N := dvd_mul_right _ _
  have hEN : E.grid * matrixDenominator A ∣ N := dvd_mul_left _ _
  have hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ := by
    intro x hx
    change (⟨D.basis.equivFun.symm x⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨φ (D.basis.equivFun.symm x)⟩ : E.filtration.Group) ∈ E.lattice
    refine ⟨D.inner_grid (scaledIntegerGrid_subset_of_dvd hDN hx), ?_⟩
    apply (bchSubgroupCoordinates_repr E.basis E.lattice _).mp
    apply E.inner_grid
    apply linearMap_mem_scaledGrid D.basis E.basis φ.toLinearMap hEN
    simpa only [LinearEquiv.apply_symm_apply] using hx
  have hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N := by
    intro x hx
    exact denominatorGrid_subset_of_dvd hDN (D.outer_grid hx.1)
  have hA : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact ((rationalLogHeight_le_iff _ p).mp (hentries i j)).2.trans
      (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hNbound : (N : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
    have h := mul_le_mul hD.2.1 (mul_le_mul hE.2.1 hA (Nat.cast_nonneg _) (Real.exp_nonneg _))
      (by positivity) (Real.exp_nonneg _)
    have h' : (N : ℝ) ≤ Real.exp (p + (p + (p + 2) ^ 3)) := by
      simpa only [N, Nat.cast_mul, ← Real.exp_add] using h
    apply h'.trans (Real.exp_le_exp.mpr ?_)
    have hp3 : p ≤ (p + 2) ^ 3 := le_power_budget hp (by decide)
    calc
      p + (p + (p + 2) ^ 3) ≤ 3 * (p + 2) ^ 3 := by linarith
      _ ≤ (p + 2) ^ 2 * (p + 2) ^ 3 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = (p + 2) ^ 5 := by ring
  exact ⟨N, hN, hin, hout, hNbound,
    D.withLattice_geometry Λ N hN hin hout hD (le_power_budget hp (by decide)) hNbound⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}

noncomputable def withLattice (M : D.MultidegreeStructure bound)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N) :
    (D.withLattice Λ N hN hin hout).MultidegreeStructure bound where
  filtration := M.filtration
  ordinary := M.ordinary
  basis := M.basis

theorem withLattice_complexity (M : D.MultidegreeStructure bound)
    (Λ : Subgroup D.filtration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    {p P : ℝ} (hM : M.ComplexityLE p) (hpP : p ≤ P)
    (hD : (D.withLattice Λ N hN hin hout).GeometryComplexityLE P) :
    (M.withLattice Λ N hN hin hout).ComplexityLE P :=
  ⟨hD, fun a j k => (hM.2 a j k).trans hpP⟩

end RationalFilteredNilmanifold.MultidegreeStructure

theorem exists_marked_evaluation_lattice (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r t d e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
      (M : D.MultidegreeStructure (mixedCorrelationDegree s))
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      (E : RationalFilteredNilmanifold (L ⧸ J) u e) {p : ℝ},
      0 ≤ p → M.ComplexityLE p → E.GeometryComplexityLE p → (t : ℝ) ≤ p →
      (∀ i j, rationalLogHeight
        (E.basis.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤ p) →
      ∃ (B : ℕ) (Λ : Subgroup D.filtration.Group) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ)
        (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B),
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ ≤ D.lattice ∧
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧
        (M.withLattice Λ B hB hin hout).ComplexityLE ((p + C) ^ C) ∧
        (∀ z : D.filtration.Group, z ∈ Λ →
          (⟨markedBaseEvaluation F v w marked t J hJ 0 z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
        (∀ z : D.filtration.Group, z ∈ Λ →
          IntegralVector (markedQuotientPhase F v w marked t z.coord)) ∧
        ∀ z : D.RealGroup, z ∈ (D.withLattice Λ B hB hin hout).realLattice →
          (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈
            E.realLattice := by
  obtain ⟨C, hC, hcover⟩ := RationalFilteredNilmanifold.exists_native_linear_target_cover (s + 1)
  refine ⟨C, hC, ?_⟩
  intro I L _ _ r t d e u F v w marked D M J hJ E p hp hM hE ht hφ hψ
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
  have hpC : p ≤ (p + C) ^ C := by
    calc
      p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + C) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ C)
  obtain ⟨B, Λ, hB, hin, hout, hbound, hΛ, hcoords, hgeom, hmap, hphase⟩ :=
    hcover D E (markedBaseEvaluation F v w marked t J hJ 0)
      (markedQuotientPhase F v w marked t).toLinearMap hp hM.1 hE ht hφ hψ
  refine ⟨B, Λ, hB, hin, hout, hbound, hΛ, hcoords,
    M.withLattice_complexity Λ B hB hin hout hM hpC hgeom, hmap, hphase, ?_⟩
  exact (D.withLattice Λ B hB hin hout).linearMap_real_lattice E
    (markedBaseEvaluation F v w marked t J hJ 0) hmap

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d) (m : ℕ)

noncomputable def normalizedMarkedLattice : Subgroup D.filtration.Group :=
  D.lattice ⊓ (RationalTorus.nilmanifold t).lattice.comap
    (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
      (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot)
      (normalizedMarkedPhase F v w marked t m))

theorem normalizedMarkedLattice_le : normalizedMarkedLattice F v w marked t D m ≤ D.lattice :=
  inf_le_left

theorem normalizedMarkedLattice_integral (z : D.filtration.Group)
    (hz : z ∈ normalizedMarkedLattice F v w marked t D m) :
    IntegralVector (normalizedMarkedPhase F v w marked t m z.coord) := hz.2

theorem exists_normalizedMarkedLattice_model
    (M : D.MultidegreeStructure (mixedCorrelationDegree s)) {p : ℝ}
    (hp : 0 ≤ p) (hM : M.ComplexityLE p) (ht : (t : ℝ) ≤ p) (hm : 0 < m)
    (hmp : (m : ℝ) ≤ Real.exp p)
    (hcoords : ∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤ p) :
    ∃ (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis (normalizedMarkedLattice F v w marked t D m))
      (hout : bchSubgroupCoordinates D.basis (normalizedMarkedLattice F v w marked t D m) ⊆ denominatorGrid N),
      (N : ℝ) ≤ Real.exp ((2 * p + 3) ^ 5) ∧
      (M.withLattice (normalizedMarkedLattice F v w marked t D m) N hN hin hout).ComplexityLE
        ((2 * p + 3) ^ 5) := by
  have hpP : p ≤ 2 * p + 1 := by linarith
  have hP : 0 ≤ 2 * p + 1 := hp.trans hpP
  have hentries (i j) : rationalLogHeight ((RationalTorus.nilmanifold t).basis.repr
      (normalizedMarkedPhase F v w marked t m (D.basis j)) i) ≤ 2 * p + 1 := by
    change rationalLogHeight ((RationalTorus.basis t).repr
      (normalizedMarkedPhase F v w marked t m (D.basis j)) i) ≤ _
    rw [RationalTorus.basis_repr]
    exact normalizedMarkedPhase_height F v w marked t m hm hp hmp (D.basis j) i (hcoords i j)
  obtain ⟨N, hN, hin, hout, hNbound, hgeom⟩ := D.exists_exact_source_lattice_cover
    (RationalTorus.nilmanifold t) (normalizedMarkedPhase F v w marked t m) hP
    (hM.1.mono D hpP) (RationalTorus.nilmanifold_geometry t hP (ht.trans hpP)) hentries
  have heq : 2 * p + 1 + 2 = 2 * p + 3 := by ring
  rw [heq] at hNbound hgeom
  have hpQ : p ≤ (2 * p + 3) ^ 5 := hpP.trans (by
    simpa only [heq] using le_power_budget hP (by decide : 1 ≤ 5))
  exact ⟨N, hN, hin, hout, hNbound,
    M.withLattice_complexity (normalizedMarkedLattice F v w marked t D m)
      N hN hin hout hM hpQ hgeom⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

structure NativeUnitVerticalData {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (B : NativeCommonDerivativeModels s N p f) (V : NativeVerticalDerivativeData B) (q : ℝ) where
  tailDim : ℕ
  dimension : (tailDim + 1 : ℝ) ≤ Real.exp q
  observable : Fin (tailDim + 1) → B.model.Space → ℂ
  lipBound : ℝ≥0
  lip_bound : (lipBound : ℝ) ≤ Real.exp q
  unit : ∀ x, ∑ i, ‖observable i x‖ ^ 2 = 1
  norm : ∀ i x, ‖observable i x‖ ≤ 1
  lipschitz : letI := B.model.metricSpace; ∀ i, LipschitzWith lipBound (observable i)
  scalar : ∀ h x, observable 0 x = (B.test h).observable x / 2
  vertical : ∀ i z, z ∈ B.model.filtration.realification.subgroup s → ∀ x,
    observable i (z • x) =
      CircleFourier.character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle) *
        observable i x

namespace NativeUnitVerticalData

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} {V : NativeVerticalDerivativeData B}
  (U : NativeUnitVerticalData B V q)

noncomputable def test (i : Fin (U.tailDim + 1)) (h : ZMod N) :
    B.model.Niltest (fun _ : Unit => 1) where
  orbit := (B.test h).orbit
  observable := U.observable i
  normBound := 1
  lipBound := U.lipBound
  norm_le := U.norm i
  lipschitz := U.lipschitz i

end NativeUnitVerticalData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankIteration
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}

noncomputable def absorbRankZero (W : NativeCorrelationStructure (s + 1) 0 N p f) (hp : 0 ≤ p) :
    NativeMixedCorrelation (s + 1) N (productNiltestBudget (p + 4)) f := by
  have hq : 0 ≤ p + 4 := by linarith
  have hpq : p ≤ productNiltestBudget (p + 4) :=
    (show p ≤ p + 4 by linarith).trans (le_productNiltestBudget hq)
  refine {
    shifts := W.shifts
    nonempty := W.nonempty
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans W.density
    mixed := W.mixed.mono hpq
    correlation := ?_
  }
  intro h hh
  have hin : Nonempty (NativeVectorCorrelation s N p
      (fun ij : Fin W.mixed.outputDim × Fin W.family.outputDim => fun x =>
        nativeMixedResidual f W.mixed h ij.1 x *
          star ((W.family.lowerComponent ij.2 h).evalCyclic N (fun _ => x)))) := by
    have hc := W.correlation h hh
    change Nonempty (NativeVectorCorrelation s N p
      (fun (ij : Fin W.mixed.outputDim × Fin W.family.outputDim) x =>
        multiplicativeDerivative f h x * star (W.mixed.evalCyclic N ij.1 (correlationInput h x)) *
          star (W.family.evalCyclic N ij.2 h x))) at hc
    simpa only [nativeMixedResidual, NativeDegreeRankFamily.lowerComponent_evalCyclic] using hc
  obtain ⟨V⟩ := hin
  exact NativeVectorCorrelation.exists_absorb
    (W.family.model.dropTop W.family.rankZero_top_eq_bot)
    (fun j => W.family.lowerComponent j h) (nativeMixedResidual f W.mixed h)
    (by linarith : 2 ≤ p + 4) (fun j => W.family.lowerComponent_complexity hp j h)
    (V.mono (by linarith))

end Erdos3.NativeCorrelationStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

def NativeCrossRowDetection (s C : ℕ) : Prop :=
  ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
    ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
    ∀ f g : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
    Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      (f n * star (g (n + h))) * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
    Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) g

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

end Erdos3

end

end OAI
end


