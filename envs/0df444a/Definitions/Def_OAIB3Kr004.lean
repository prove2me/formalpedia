-- Prove2me | Definitions.Def_OAIB3Kr004
-- name    : OAIB3Kr004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T15:56:43.328168+00:00
-- url     : https://prove2.me/theorems/e85a1071-e024-47d1-9811-d375b710c972
-- title:
--   Definitions bundle OAIB3Kr004 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 206 declarations of OpenAI's Lean: 71 definitions, 7 inductive types or structures, 11 instances and 117 theorems. The definitions and types are `OAI.KirchbergRordam.GenericRW.FieldCalculus.Data`, `OAI.KirchbergRordam.GenericRW.FieldCalculus.Data.aux`, `OAI.KirchbergRordam.GenericRW.FreeCoordinates`, `OAI.KirchbergRordam.GenericRW.FullRankWeighted.instPartialOrder_solutions`, `OAI.KirchbergRordam.GenericRW.Fullness.IsFull`, `OAI.KirchbergRordam.GenericRW.Fullness.closedIdeal`, `OAI.KirchbergRordam.GenericRW.GroupedFactors.bicommutant`, `OAI.KirchbergRordam.GenericRW.GroupedFactors.commutantOf`, `OAI.KirchbergRordam.GenericRW.IrreducibleRepresentation`, `OAI.KirchbergRordam.GenericRW.PrimitiveSeparation.stateFace`, `OAI.KirchbergRordam.GenericRW.PureStates.IsPure`, `OAI.KirchbergRordam.GenericRW.PureStates.evaluationReal`, `OAI.KirchbergRordam.GenericRW.PureStates.normStates`, `OAI.KirchbergRordam.GenericRW.RWCut.f`, `OAI.KirchbergRordam.GenericRW.RWCut.j`, `OAI.KirchbergRordam.GenericRW.RealProduct.multiply`, `OAI.KirchbergRordam.GenericRW.Representations.coefficient`, `OAI.KirchbergRordam.GenericRW.Representations.gnsVector`, `OAI.KirchbergRordam.GenericRW.Representations.positiveCLM`, `OAI.KirchbergRordam.GenericRW.Representations.pureRepresentation`, `OAI.KirchbergRordam.GenericRW.Representations.representationCLM`, `OAI.KirchbergRordam.GenericRW.Representations.stateOfPure`, `OAI.KirchbergRordam.GenericRW.SeparableReduction.Term`, `OAI.KirchbergRordam.GenericRW.SeparableReduction.stage`, `OAI.KirchbergRordam.GenericRW.SeparableReduction.term`, `OAI.KirchbergRordam.GenericRW.SeparableReduction.termAlgebra`, `OAI.KirchbergRordam.GenericRW.Spatial.Hilbert`, `OAI.KirchbergRordam.GenericRW.Spatial.map`, `OAI.KirchbergRordam.GenericRW.axes`, `OAI.KirchbergRordam.GenericRW.freeVector`, `OAI.KirchbergRordam.GenericRW.kernelChart`, `OAI.KirchbergRordam.GenericRW.normalizedRow`, `OAI.KirchbergRordam.GenericRW.tensorBasis`, `OAI.KirchbergRordam.GenericRW.tensorMatrix`, `OAI.KirchbergRordam.GenericRW.tensorPivot`, `OAI.KirchbergRordam.GenericRW.weightedTensorMatrix`, `OAI.KirchbergRordam.Intertwining.limitHom`, `OAI.KirchbergRordam.IrreducibleRepresentation`, `OAI.KirchbergRordam.MaxTensor.CStarPack`, `OAI.KirchbergRordam.MinTensor.instRingTensorProductComplex_solutions` and 38 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CharacterCriterion_Absorption`, `CharacterCriterion_BalancedLimit`, `CharacterCriterion_CentralSequences`, `CharacterCriterion_DetectingSpaces`, `CharacterCriterion_FactorIndependence`, `CharacterCriterion_FieldCalculus`, `CharacterCriterion_FiniteDrop`, `CharacterCriterion_Fullness`, `CharacterCriterion_FunctionalCalculus`, `CharacterCriterion_Main`, `CharacterCriterion_MatrixPaths`, `CharacterCriterion_MinTensor`, `CharacterCriterion_PrimeSpectrum`, `CharacterCriterion_Reindexing`, `CharacterCriterion_RepresentationTheory`, `CharacterCriterion_Representations`, `CharacterCriterion_SeparableReduction`, `CharacterCriterion_SpatialTensor`, `CharacterCriterion_StandardPrime`, `CharacterCriterion_States`, `CharacterCriterion_SymmetryFlow`, `CharacterCriterion_TensorSections`, `CharacterCriterion_UltrapowerSaturation`.
--
--   **Imports.** It imports the published bundle `Def_CharacterCriterion`; the bundle `OAIB3Kr002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIB3Kr005`; the statement `OAI.KirchbergRordam.PrimeSquareUnitary.exists_half_flip_control`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr002

section
-- module Solutions.OAIB3_Krc.Compat
attribute [-instance] _root_.OAI.KirchbergRordam.NormUltrapower.quotientNormedRing _root_.OAI.KirchbergRordam.StarCompletion.completionNormedAlgebra _root_.OAI.KirchbergRordam.StarCompletion.completionStar _root_.OAI.KirchbergRordam.StarCompletion.completionStarRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FactorIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct


open scoped InnerProductSpace

namespace KirchbergRordam.GenericRW.GroupedFactors
open scoped Pointwise
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


def commutantOf (S : StarSubalgebra ℂ (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))) =
      (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))
    simp only [StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq, Set.union_self]
    exact Set.centralizer_centralizer_centralizer _

def bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) : VonNeumannAlgebra H :=
  (commutantOf S).commutant

end KirchbergRordam.GenericRW.GroupedFactors

namespace KirchbergRordam.GenericRW.RealProduct
open scoped TensorProduct
open Module
variable {A : Type*} [CStarAlgebra A] {n : ℕ}
variable {V : Fin n → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]

def multiply (f : ∀ i, V i →ₗ[ℝ] A) : (⨂[ℝ] i, V i) →ₗ[ℝ] A :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebraFin ℝ n A).compLinearMap f)

@[simp] lemma multiply_tprod (f : ∀ i, V i →ₗ[ℝ] A) (v : ∀ i, V i) :
    multiply f (⨂ₜ[ℝ] i, v i) = (List.ofFn fun i => f i (v i)).prod := by
  simp [multiply]

end KirchbergRordam.GenericRW.RealProduct
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DetectingSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace


open scoped BigOperators
open Set Module

namespace KirchbergRordam.GenericRW

section KernelCharts

variable {J K E : Type*} [Fintype J]


noncomputable def axes (e : J ↪ K) (y : J → ℝ) : K → ℝ := by
  classical
  exact ∑ j, Pi.single (e j) (y j)


abbrev FreeCoordinates (e : J ↪ K) := {k : K // k ∉ Set.range e}

noncomputable def freeVector (e : J ↪ K) (z : FreeCoordinates e → ℝ) : K → ℝ := by
  classical
  exact fun k => if h : k ∈ Set.range e then 0 else z ⟨k, h⟩

variable [Fintype K]

noncomputable instance instFintypeFreeCoordinates (e : J ↪ K) : Fintype (FreeCoordinates e) := Fintype.ofFinite _


noncomputable def kernelChart (e : J ↪ K) (M : E → Matrix J K ℝ)
    (q : E × (FreeCoordinates e → ℝ)) : K → ℝ :=
  freeVector e q.2 - axes e ((M q.1).mulVec (freeVector e q.2))

end KernelCharts

section TensorMatrices

open scoped Classical

variable {N M R : Type*} [Fintype N]


noncomputable def normalizedRow (s : Fin 2 ↪ M) (p : Fin 2 × M → ℝ) :
    Matrix (Fin 2) M ℝ :=
  fun j i => if i = s j then 1 else if i ∈ Set.range s then 0 else p (j, i)


def tensorPivot (s : N → Fin 2 ↪ M) (a : R) : (N → Fin 2) ↪ R × (N → M) where
  toFun j := (a, fun l => s l (j l))
  inj' := by
    intro j k h
    funext l
    exact (s l).injective (congrFun (congrArg Prod.snd h) l)


noncomputable def weightedTensorMatrix (s : N → Fin 2 ↪ M) (a : R)
    (p : (N × (Fin 2 × M) → ℝ) × (R → ℝ)) :
    Matrix (N → Fin 2) (R × (N → M)) ℝ :=
  fun j k => (if k.1 = a then 1 else p.2 k.1) *
    ∏ l, normalizedRow (s l) (fun ji => p.1 (l, ji)) (j l) (k.2 l)

variable [Fintype M] [Fintype R]


def tensorMatrix (P : N → Matrix (Fin 2) M ℝ) : Matrix (N → Fin 2) (N → M) ℝ :=
  fun j i => ∏ l, P l (j l) (i l)

end TensorMatrices


section TensorCoordinates

open scoped Classical
open PiTensorProduct
open scoped TensorProduct

variable {N M R : Type*} [Fintype N] [Fintype M] [Fintype R]


noncomputable def tensorBasis (N M : Type*) [Fintype N] [Fintype M] :
    Basis (N → M) ℝ (⨂[ℝ] _ : N, (M → ℝ)) :=
  Basis.piTensorProduct (fun _ : N => Pi.basisFun ℝ M)

end TensorCoordinates


open scoped TensorProduct

universe u v


end KirchbergRordam.GenericRW

universe uQuot


open Topology
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_States
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology


open NormedSpace
open scoped ComplexOrder
namespace KirchbergRordam.GenericRW
namespace States

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

lemma norm_rotation (a : A) (ha : IsSelfAdjoint a) (t : ℝ) :
    ‖exp (t • (Complex.I • a))‖ = 1 := by
  have he : exp (t • (Complex.I • a)) =
      (selfAdjoint.expUnitary (t • (⟨a, ha⟩ : selfAdjoint A)) : A) := by
    change exp (t • (Complex.I • a)) = exp (Complex.I • t • a)
    rw [smul_comm]
  rw [he, CStarRing.norm_coe_unitary]

lemma eval_selfAdjoint_im_zero (φ : A →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) (h1 : φ 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) : (φ a).im = 0 := by
  let l : A →L[ℝ] ℝ := Complex.reCLM.comp (φ.restrictScalars ℝ)
  have hd : HasDerivAt (fun t : ℝ => l (exp (t • (Complex.I • a))))
      (-(φ a).im) 0 := by
    have hh := l.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_exp_smul_const (Complex.I • a) (0 : ℝ))
    convert hh using 1 <;> first | rfl | simp [l, map_smul, Complex.mul_re]
  have hmax : IsLocalMax (fun t : ℝ => l (exp (t • (Complex.I • a)))) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change (φ (exp (t • (Complex.I • a)))).re ≤ (φ (exp ((0 : ℝ) • (Complex.I • a)))).re
    simp only [zero_smul, exp_zero, h1, Complex.one_re]
    exact (Complex.re_le_norm _).trans <|
      (φ.le_opNorm _).trans <| by rw [norm_rotation a ha t, mul_one]; exact hφ
  exact neg_eq_zero.mp (hmax.hasDerivAt_eq_zero hd)

variable [PartialOrder A] [StarOrderedRing A]

lemma eval_nonneg (φ : A →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) (h1 : φ 1 = 1)
    (a : A) (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hi := eval_selfAdjoint_im_zero φ hφ h1 a (IsSelfAdjoint.of_nonneg ha)
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, hi.symm⟩
  by_cases hz : a = 0
  · simp [hz]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr hz
  let b := ‖a‖⁻¹ • a
  have hb : 0 ≤ b := smul_nonneg (inv_nonneg.mpr hn.le) ha
  have hbn : ‖b‖ ≤ 1 := by
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hb1 : b ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg b hb).mp hbn
  have hn1 : ‖1 - b‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (sub_nonneg.mpr hb1)).mpr (sub_le_self _ hb)
  have hh : (φ (1 - b)).re ≤ 1 :=
    (Complex.re_le_norm _).trans <| (φ.le_opNorm _).trans <|
      (mul_le_mul_of_nonneg_left hn1 (norm_nonneg φ)).trans (by simpa using hφ)
  rw [map_sub, h1, Complex.sub_re, Complex.one_re] at hh
  have hbr : (φ b).re = ‖a‖⁻¹ * (φ a).re := by
    dsimp [b]
    change ((φ.restrictScalars ℝ) (‖a‖⁻¹ • a)).re = _
    rw [map_smul]
    simp
  rw [hbr] at hh
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp (by linarith : 0 ≤ ‖a‖⁻¹ * (φ a).re)


end States
end KirchbergRordam.GenericRW


open scoped ComplexOrder
namespace KirchbergRordam.GenericRW
namespace PureStates
variable (A : Type*) [CStarAlgebra A]

def normStates : Set (WeakDual ℂ A) := {φ | ‖φ.toStrongDual‖ ≤ 1 ∧ φ 1 = 1}

def evaluationReal : WeakDual ℂ A →ₗ[ℝ] (A → ℂ) where
  toFun φ := φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance locallyConvexReal : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  LocallyConvexSpace.induced (evaluationReal A)

variable [Nontrivial A]


def IsPure (φ : A →L[ℂ] ℂ) : Prop :=
  (StrongDual.toWeakDual φ) ∈ (normStates A).extremePoints ℝ

variable {A}

omit [Nontrivial A] in
lemma IsPure.norm_le_one {φ : A →L[ℂ] ℂ} (hp : IsPure A φ) : ‖φ‖ ≤ 1 := hp.1.1
omit [Nontrivial A] in
lemma IsPure.map_one {φ : A →L[ℂ] ℂ} (hp : IsPure A φ) : φ 1 = 1 := hp.1.2

omit [Nontrivial A] in
lemma IsPure.extreme {φ ψ χ : A →L[ℂ] ℂ} (hp : IsPure A φ)
    (hψ : ‖ψ‖ ≤ 1) (hψ1 : ψ 1 = 1) (hχ : ‖χ‖ ≤ 1) (hχ1 : χ 1 = 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (he : φ = t • ψ + (1 - t) • χ) : ψ = φ := by
  apply StrongDual.toWeakDual.injective
  apply hp.2 (show (StrongDual.toWeakDual ψ) ∈ normStates A from ⟨hψ, hψ1⟩)
    (show (StrongDual.toWeakDual χ) ∈ normStates A from ⟨hχ, hχ1⟩)
  exact ⟨t, 1 - t, ht, sub_pos.mpr ht1, by ring, by
    change t • ψ + (1 - t) • χ = φ
    exact he.symm⟩

end PureStates
end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Representations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder


open scoped InnerProductSpace
namespace KirchbergRordam.GenericRW
namespace Representations
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

def gnsVector (a : A) : f.GNS := (f.toPreGNS a : f.GNS)

@[simp] lemma gnsVector_inner (a b : A) :
    ⟪gnsVector f a, gnsVector f b⟫_ℂ = f (star a * b) := by
  simp [gnsVector, PositiveLinearMap.preGNS_inner_def]

@[simp] lemma gnsVector_apply (a b : A) :
    f.gnsStarAlgHom a (gnsVector f b) = gnsVector f (a * b) := by
  simp [gnsVector, PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.leftMulMapPreGNS]

lemma positive_bound (a : A) : ‖f a‖ ≤ (f 1).re * ‖a‖ := by
  let ξ := gnsVector f 1
  have hi : f a = ⟪ξ, f.gnsStarAlgHom a ξ⟫_ℂ := by
    dsimp [ξ]
    rw [gnsVector_apply, gnsVector_inner]
    simp
  have hn : ‖ξ‖ ^ 2 = (f 1).re := by
    calc
      _ = (⟪ξ, ξ⟫_ℂ).re := (inner_self_eq_norm_sq (𝕜 := ℂ) ξ).symm
      _ = (f 1).re := by dsimp [ξ]; rw [gnsVector_inner]; simp
  calc
    ‖f a‖ = ‖⟪ξ, f.gnsStarAlgHom a ξ⟫_ℂ‖ := congrArg norm hi
    _ ≤ ‖ξ‖ * ‖f.gnsStarAlgHom a ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖a‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left
      ((f.gnsStarAlgHom a).le_opNorm ξ |>.trans <| mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom a) (norm_nonneg ξ)) (norm_nonneg ξ)
    _ = (f 1).re * ‖a‖ := by rw [← hn]; ring

def positiveCLM : A →L[ℂ] ℂ :=
  f.toLinearMap.mkContinuous (f 1).re (positive_bound f)

@[simp] lemma positiveCLM_apply (a : A) : positiveCLM f a = f a := rfl

lemma positiveCLM_norm : ‖positiveCLM f‖ ≤ (f 1).re := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact (Complex.nonneg_iff.mp (f.map_nonneg zero_le_one)).1
  · exact positive_bound f

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

def representationCLM : A →L[ℂ] (H →L[ℂ] H) :=
  π.toAlgHom.toLinearMap.mkContinuous 1 fun a => by
    simpa using NonUnitalStarAlgHom.norm_apply_le π a

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma representationCLM_apply (a : A) : representationCLM π a = π a := rfl

def coefficient (T : H →L[ℂ] H) : A →L[ℂ] ℂ where
  toFun a := ⟪ξ, T (π a ξ)⟫_ℂ
  map_add' a b := by simp
  map_smul' z a := by simp
  cont := (continuous_const.inner <| T.continuous.comp <|
    ((representationCLM π).continuous.clm_apply continuous_const))

@[simp] lemma coefficient_apply (T : H →L[ℂ] H) (a : A) :
    coefficient π ξ T a = ⟪ξ, T (π a ξ)⟫_ℂ := rfl

lemma coefficient_nonneg (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (hc : ∀ a, Commute T (π a)) (a : A) (ha : 0 ≤ a) :
    0 ≤ coefficient π ξ T a := by
  let b := CFC.sqrt a
  have hb : IsSelfAdjoint (π b) := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).map π
  have hab : a = b * b := (CFC.sqrt_mul_sqrt_self a ha).symm
  have ht := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hT
  have he : coefficient π ξ T a = ⟪π b ξ, T (π b ξ)⟫_ℂ := by
    rw [coefficient_apply, hab, map_mul]
    have hh := congrArg (fun S : H →L[ℂ] H => S (π b ξ)) (hc b).eq
    change ⟪ξ, T (π b (π b ξ))⟫_ℂ = _
    change T (π b (π b ξ)) = π b (T (π b ξ)) at hh
    rw [hh]
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun S : H →L[ℂ] H => ⟪S ξ, T (π b ξ)⟫_ℂ) hb.star_eq
  rw [he]
  exact ht.inner_nonneg_right _

lemma coefficient_norm (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (hc : ∀ a, Commute T (π a)) :
    ‖coefficient π ξ T‖ ≤ (⟪ξ, T ξ⟫_ℂ).re := by
  let g : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (coefficient π ξ T).toLinearMap
    (coefficient_nonneg π ξ T hT hc)
  have he : positiveCLM g = coefficient π ξ T := by ext; rfl
  have hn := positiveCLM_norm g
  rw [he] at hn
  change ‖coefficient π ξ T‖ ≤ (coefficient π ξ T 1).re at hn
  simpa only [coefficient_apply, map_one, one_apply_eq_self] using hn

end Representations
end KirchbergRordam.GenericRW
namespace KirchbergRordam.GenericRW.PureStates
variable {A : Type*} [CStarAlgebra A]

lemma IsPure.split (φ g h : A →L[ℂ] ℂ) (hp : IsPure A φ)
    (hn : ‖g‖ ≤ (g 1).re) (hm : ‖h‖ ≤ (h 1).re)
    (hg : 0 ≤ g 1) (hh : 0 ≤ h 1) (he : g + h = φ) :
    g = (g 1).re • φ := by
  let t := (g 1).re
  let s := (h 1).re
  have hg1 : g 1 = (t : ℂ) := by
    apply Complex.ext <;> simp [t, (Complex.nonneg_iff.mp hg).2.symm]
  have hh1 : h 1 = (s : ℂ) := by
    apply Complex.ext <;> simp [s, (Complex.nonneg_iff.mp hh).2.symm]
  have ht : 0 ≤ t := (Complex.nonneg_iff.mp hg).1
  have hs : 0 ≤ s := (Complex.nonneg_iff.mp hh).1
  have hts : t + s = 1 := by
    have he1 := congrArg (fun f : A →L[ℂ] ℂ => (f 1).re) he
    simpa only [add_apply, Complex.add_re, hp.map_one, Complex.one_re] using he1
  by_cases ht0 : t = 0
  · have hg0 : g = 0 := norm_eq_zero.mp (le_antisymm (hn.trans_eq ht0) (norm_nonneg _))
    change g = t • φ
    rw [ht0, hg0]
    ext a
    simp only [smul_apply, zero_apply]
    exact (zero_smul ℝ (φ a)).symm
  by_cases hs0 : s = 0
  · have hh0 : h = 0 := norm_eq_zero.mp (le_antisymm (hm.trans_eq hs0) (norm_nonneg _))
    have ht1 : t = 1 := by linarith
    change g = t • φ
    simpa [ht1, hh0] using he
  have htn : ‖t⁻¹ • g‖ ≤ 1 := calc
    _ = t⁻¹ * ‖g‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht)]
    _ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ht)
    _ = 1 := inv_mul_cancel₀ ht0
  have hsn : ‖s⁻¹ • h‖ ≤ 1 := calc
    _ = s⁻¹ * ‖h‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hs)]
    _ ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hs)
    _ = 1 := inv_mul_cancel₀ hs0
  have hgn : (t⁻¹ • g) 1 = 1 := by
    simp only [smul_apply, hg1, Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast ht0)
  have hhn : (s⁻¹ • h) 1 = 1 := by
    simp only [smul_apply, hh1, Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast hs0)
  have hf := hp.extreme htn hgn hsn hhn t (lt_of_le_of_ne ht (Ne.symm ht0))
    (by linarith [lt_of_le_of_ne hs (Ne.symm hs0)]) (by
      rw [show 1 - t = s by linarith, smul_smul, smul_smul,
        mul_inv_cancel₀ ht0, mul_inv_cancel₀ hs0, one_smul, one_smul]
      exact he.symm)
  have heq := congrArg (fun f : A →L[ℂ] ℂ => t • f) hf
  simpa only [smul_smul, mul_inv_cancel₀ ht0, one_smul] using heq

end KirchbergRordam.GenericRW.PureStates

namespace KirchbergRordam.GenericRW.Representations
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

lemma coefficient_commutant_injective (hd : DenseRange (fun a => π a ξ))
    (T S : H →L[ℂ] H) (hT : ∀ a, Commute T (π a)) (hS : ∀ a, Commute S (π a))
    (he : coefficient π ξ T = coefficient π ξ S) : T = S := by
  have hξ : T ξ = S ξ := by
    apply ext_inner_left ℂ
    intro y
    refine hd.induction_on (p := fun y => ⟪y, T ξ⟫_ℂ = ⟪y, S ξ⟫_ℂ) y
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    have he' := congrArg (fun f : A →L[ℂ] ℂ => f (star a)) he
    have ha (U : H →L[ℂ] H) (hU : ∀ a, Commute U (π a)) :
        coefficient π ξ U (star a) = ⟪π a ξ, U ξ⟫_ℂ := by
      rw [coefficient_apply]
      have hc := congrArg (fun V : H →L[ℂ] H => V ξ) (hU (star a)).eq
      change U (π (star a) ξ) = π (star a) (U ξ) at hc
      rw [hc, map_star]
      exact ContinuousLinearMap.adjoint_inner_right (π a) ξ (U ξ)
    simpa only [ha T hT, ha S hS] using he'
  apply DFunLike.coe_injective
  apply hd.equalizer T.continuous S.continuous
  funext a
  change T (π a ξ) = S (π a ξ)
  have htc := congrArg (fun U : H →L[ℂ] H => U ξ) (hT a).eq
  have hsc := congrArg (fun U : H →L[ℂ] H => U ξ) (hS a).eq
  change T (π a ξ) = π a (T ξ) at htc
  change S (π a ξ) = π a (S ξ) at hsc
  rw [htc, hsc, hξ]

lemma positive_contraction_scalar (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ)
    (hφ : coefficient π ξ 1 = φ) (hd : DenseRange (fun a => π a ξ))
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (hT1 : T ≤ 1) (hc : ∀ a, Commute T (π a)) :
    ∃ t : ℝ, T = t • 1 := by
  let g := coefficient π ξ T
  let h := coefficient π ξ (1 - T)
  have hTc : ∀ a, Commute (1 - T) (π a) := fun a => (Commute.one_left _).sub_left (hc a)
  have hsum : g + h = φ := by
    rw [← hφ]
    ext a
    simp [g, h, coefficient]
  have hgn : ‖g‖ ≤ (g 1).re := by
    simpa only [g, coefficient_apply, map_one, one_apply_eq_self] using coefficient_norm π ξ T hT hc
  have hhn : ‖h‖ ≤ (h 1).re := by
    simpa only [h, coefficient_apply, map_one, one_apply_eq_self] using
      coefficient_norm π ξ (1 - T) (sub_nonneg.mpr hT1) hTc
  have he := hp.split φ g h hgn hhn (coefficient_nonneg π ξ T hT hc 1 zero_le_one)
    (coefficient_nonneg π ξ (1 - T) (sub_nonneg.mpr hT1) hTc 1 zero_le_one) hsum
  refine ⟨(g 1).re, coefficient_commutant_injective π ξ hd T ((g 1).re • 1) hc
    (fun a => (Commute.one_left _).smul_left _) ?_⟩
  change g = coefficient π ξ ((g 1).re • 1)
  calc
    g = (g 1).re • φ := he
    _ = coefficient π ξ ((g 1).re • 1) := by
      conv_lhs => rw [← hφ]
      ext a
      simp [coefficient]

end KirchbergRordam.GenericRW.Representations
namespace KirchbergRordam.GenericRW.Representations
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
variable (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ)
    (hφ : coefficient π ξ 1 = φ) (hd : DenseRange (fun a => π a ξ))

include hp hφ hd

lemma positive_scalar (T : H →L[ℂ] H) (hT : 0 ≤ T) (hc : ∀ a, Commute T (π a)) :
    ∃ t : ℝ, T = t • 1 := by
  by_cases hz : T = 0
  · exact ⟨0, by simp [hz]⟩
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr hz
  have hS : 0 ≤ ‖T‖⁻¹ • T := smul_nonneg (inv_nonneg.mpr hn.le) hT
  have hS1 : ‖T‖⁻¹ • T ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hS).mp <| by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  obtain ⟨t, ht⟩ := positive_contraction_scalar π ξ φ hp hφ hd _ hS hS1
    (fun a => (hc a).smul_left _)
  refine ⟨‖T‖ * t, ?_⟩
  have he := congrArg (fun U : H →L[ℂ] H => ‖T‖ • U) ht
  simpa only [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] using he

lemma selfAdjoint_scalar (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hc : ∀ a, Commute T (π a)) : ∃ t : ℝ, T = t • 1 := by
  have hn := hT.neg.le_algebraMap_norm_self
  rw [norm_neg, Algebra.algebraMap_eq_smul_one] at hn
  have hpT : 0 ≤ T + ‖T‖ • (1 : H →L[ℂ] H) := neg_le_iff_add_nonneg'.mp hn
  obtain ⟨t, ht⟩ := positive_scalar π ξ φ hp hφ hd _ hpT
    (fun a => (hc a).add_left ((Commute.one_left _).smul_left _))
  refine ⟨t - ‖T‖, ?_⟩
  rw [sub_smul]
  exact eq_sub_iff_add_eq.mpr ht


theorem pure_cyclic_scalar_commutant (T : H →L[ℂ] H)
    (hc : ∀ a, Commute T (π a)) : ∃ z : ℂ, T = z • 1 := by
  have hcs (a : A) : Commute (star T) (π a) := by
    exact (show Commute T (star (π a)) by simpa only [map_star] using hc (star a)).star_left
  have hcr (a : A) : Commute (realPart T : H →L[ℂ] H) (π a) := by
    rw [realPart_apply_coe]
    exact ((hc a).add_left (hcs a)).smul_left _
  have hci (a : A) : Commute (imaginaryPart T : H →L[ℂ] H) (π a) := by
    rw [imaginaryPart_apply_coe]
    exact (((hc a).sub_left (hcs a)).smul_left _).smul_left _
  obtain ⟨r, hr⟩ := selfAdjoint_scalar π ξ φ hp hφ hd _ (realPart T).property hcr
  obtain ⟨s, hs⟩ := selfAdjoint_scalar π ξ φ hp hφ hd _ (imaginaryPart T).property hci
  refine ⟨(r : ℂ) + Complex.I * (s : ℂ), ?_⟩
  calc
    T = (realPart T : H →L[ℂ] H) + Complex.I • (imaginaryPart T : H →L[ℂ] H) :=
      (realPart_add_I_smul_imaginaryPart T).symm
    _ = ((r : ℂ) + Complex.I * (s : ℂ)) • 1 := by
      rw [hr, hs, add_smul, mul_smul]
      simp only [Complex.coe_smul]

end KirchbergRordam.GenericRW.Representations
namespace KirchbergRordam.GenericRW
namespace Representations
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma gns_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsVector f 1)) := by
  have hd : DenseRange (gnsVector f) := by
    intro x
    apply closure_mono (t := Set.range (gnsVector f)) _ (UniformSpace.Completion.denseRange_coe x)
    rintro _ ⟨a, rfl⟩
    exact ⟨f.ofPreGNS a, by simp [gnsVector]⟩
  simpa only [gnsVector_apply, mul_one] using hd


variable [Nontrivial A]

def stateOfPure (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ φ.toLinearMap (States.eval_nonneg φ hp.norm_le_one hp.map_one)

@[simp] lemma stateOfPure_apply (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) (a : A) :
    stateOfPure φ hp a = φ a := rfl

lemma pure_gns_coefficient (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) :
    coefficient (stateOfPure φ hp).gnsStarAlgHom (gnsVector (stateOfPure φ hp) 1) 1 = φ := by
  ext a
  rw [coefficient_apply, one_apply_eq_self, gnsVector_apply, gnsVector_inner]
  simp

lemma pure_gns_nontrivial (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) :
    Nontrivial (stateOfPure φ hp).GNS := by
  apply nontrivial_of_ne (gnsVector (stateOfPure φ hp) 1) 0
  intro he
  have hh := gnsVector_inner (stateOfPure φ hp) 1 1
  rw [he] at hh
  simp [hp.map_one] at hh

end Representations

universe u

structure IrreducibleRepresentation (A : Type u) [CStarAlgebra A] where
  space : Type u
  [normed : NormedAddCommGroup space]
  [inner : InnerProductSpace ℂ space]
  [complete : CompleteSpace space]
  [nontrivial : Nontrivial space]
  representation : A →⋆ₐ[ℂ] (space →L[ℂ] space)
  scalar_commutant : ∀ T : space →L[ℂ] space,
    (∀ a, Commute T (representation a)) → ∃ z : ℂ, T = z • 1

attribute [instance] IrreducibleRepresentation.normed IrreducibleRepresentation.inner
  IrreducibleRepresentation.complete IrreducibleRepresentation.nontrivial

namespace Representations
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

def pureRepresentation (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) :
    IrreducibleRepresentation A where
  space := (stateOfPure φ hp).GNS
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  nontrivial := pure_gns_nontrivial φ hp
  representation := (stateOfPure φ hp).gnsStarAlgHom
  scalar_commutant := pure_cyclic_scalar_commutant _ _ φ hp (pure_gns_coefficient φ hp)
    (gns_cyclic _)

end Representations


end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Fullness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace


namespace KirchbergRordam.GenericRW
namespace PrimitiveSeparation
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (I : Ideal A) [I.IsTwoSided] [IsClosed (I : Set A)]


def stateFace : Set (WeakDual ℂ A) := PureStates.normStates A ∩ {φ | ∀ a ∈ I, φ a = 0}

end PrimitiveSeparation
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.Fullness
variable {A : Type*} [CStarAlgebra A]


def closedIdeal (I : TwoSidedIdeal A) : Ideal A := I.asIdeal.topologicalClosure

instance closedIdeal_twoSided (I : TwoSidedIdeal A) : (closedIdeal I).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    exact (show Set.MapsTo (fun x : A => x * b) (I : Set A) (I : Set A) from
      fun x hx => I.mul_mem_right x b hx).closure (continuous_mul_const b) ha

instance closedIdeal_isClosed (I : TwoSidedIdeal A) : IsClosed (closedIdeal I : Set A) :=
  isClosed_closure


def IsFull (a : A) : Prop := TwoSidedIdeal.span {a} = ⊤

end KirchbergRordam.GenericRW.Fullness
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SpatialTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace


open scoped TensorProduct InnerProductSpace
open UniformSpace
namespace KirchbergRordam.GenericRW.Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev Hilbert (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] := Completion (H ⊗[ℂ] K)

def map (T : H →L[ℂ] H) (S : K →L[ℂ] K) : Hilbert H K →L[ℂ] Hilbert H K :=
  (TensorProduct.mapL T S).completion

@[simp] lemma map_coe (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    map T S (x : Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
  simp [map]

@[ext] lemma ext {T S : Hilbert H K →L[ℂ] Hilbert H K}
    (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq T.continuous S.continuous
  | ih x => exact h x

lemma map_add_left (T U : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (T + U) S = map T S + map U S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_add_left, ← Completion.coe_add]

lemma map_add_right (T : H →L[ℂ] H) (S U : K →L[ℂ] K) :
    map T (S + U) = map T S + map T U := by
  apply ext
  intro x
  simp [TensorProduct.mapL_add_right, ← Completion.coe_add]

lemma map_smul_left (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (z • T) S = z • map T S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_smul_left, ← Completion.coe_smul]

lemma map_smul_right (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map T (z • S) = z • map T S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_smul_right, ← Completion.coe_smul]

lemma map_mul (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
    map (T * U) (S * V) = map T S * map U V := by
  apply ext
  intro x
  simp only [mul_apply_eq_comp, map_coe, TensorProduct.mapL_mul]

@[simp] lemma map_one : map (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  apply ext
  intro x
  simp [show (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H from rfl,
    show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl]

end KirchbergRordam.GenericRW.Spatial

namespace KirchbergRordam.GenericRW
namespace Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Nontrivial H] [Nontrivial K]
instance instNontrivialHilbert : Nontrivial (Hilbert H K) :=
  (UniformSpace.Completion.coe_injective (H ⊗[ℂ] K)).nontrivial
end Spatial
end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FieldCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GenericRW.FieldCalculus
open scoped BigOperators
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [CStarAlgebra A]


structure Data (X ι A : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Fintype ι] [DecidableEq ι] [CStarAlgebra A] where
  p : C(X,ℂ)
  selfAdjoint_p : IsSelfAdjoint p
  eval : C(X,ℂ) →⋆ₐ[ℂ] A
  x : ι → ι → A
  star_x : ∀ i j, star (x i j) = x j i
  mul_x : ∀ i j k l, x i j*x k l = if j=k then eval p*x i l else 0
  commute_eval : ∀ i j f, Commute (x i j) (eval f)
  bound : ∀ i j f, ‖x i j*eval f‖ ≤ ‖p*f‖

namespace Data
variable (D : Data X ι A)

def aux (i j : ι) : C(X,ℂ) →ₗ[ℂ] A where
  toFun f := D.x i j*D.eval f
  map_add' _ _ := by simp [mul_add]
  map_smul' _ _ := by simp

end Data
end KirchbergRordam.GenericRW.FieldCalculus
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FunctionalCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GenericRW.RWCut
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

def j (t : ℝ) : ℝ := (max t (1/2))⁻¹
def f (t : ℝ) : ℝ := j t*t
end KirchbergRordam.GenericRW.RWCut

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FiniteDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GenericRW.FullRankWeighted
open scoped BigOperators
open Fullness
universe u
variable {P : Type u} [CStarAlgebra P]
local instance instPartialOrder_solutions : PartialOrder P := CStarAlgebra.spectralOrder _
local instance instStarOrderedRing_solutions : StarOrderedRing P := CStarAlgebra.spectralOrderedRing _

end KirchbergRordam.GenericRW.FullRankWeighted

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Reindexing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction

open Filter Topology

namespace KirchbergRordam.NormUltrapower
open Filter Topology TopologicalSpace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

inductive ReindexTest (S : Type*)
  | add (x y : S) | mul (x y : S) | adjoint (x : S)
  | zero | one | norm (x : S) | central (x : S) (j : ℕ)
  | commute (x : S) (j : ℕ) | imag
  deriving Countable


end KirchbergRordam.NormUltrapower
namespace KirchbergRordam.RationalDense
open Set Topology TopologicalSpace
variable {A : Type*} [CStarAlgebra A]
local instance instAlgebraRat_solutions : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ ℂ)


def stage (s : Set A) : ℕ → Set A
  | 0 => s ∪ Set.range (algebraMap ℚ A)
  | n+1 => stage s n ∪ (fun p : A×A=>p.1+p.2) '' (stage s n ×ˢ stage s n) ∪
      (fun p : A×A=>p.1*p.2) '' (stage s n ×ˢ stage s n) ∪ star '' stage s n
lemma stage_step (s : Set A) (n : ℕ) : stage s n ⊆ stage s (n+1) :=
  fun _ hx => Or.inl (Or.inl (Or.inl hx))
lemma stage_mono (s : Set A) : Monotone (stage s) := monotone_nat_of_le_succ (stage_step s)
def termAlgebra (s : Set A) : StarSubalgebra ℚ A where
  carrier := ⋃ n, stage s n
  zero_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨0,map_zero _⟩⟩
  one_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨1,map_one _⟩⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩))⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩)⟩
  algebraMap_mem' z := mem_iUnion.mpr ⟨0,Or.inr ⟨z,rfl⟩⟩
  star_mem' := by
    intro a ha
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨n+1,Or.inr ⟨a,hn,rfl⟩⟩

end KirchbergRordam.RationalDense
open Topology
namespace KirchbergRordam.RationalDense
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
local instance instAlgebraRat_solutions_1 (C : Type*) [CStarAlgebra C] : Algebra ℚ C :=
  Algebra.compHom C (algebraMap ℚ ℂ)


end KirchbergRordam.RationalDense

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SeparableReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


namespace KirchbergRordam.GenericRW.SeparableReduction
section
open Set Topology TopologicalSpace
variable {A : Type*} [CStarAlgebra A]


def stage (s : Set A) : ℕ → Set A
  | 0 => s ∪ Set.range (algebraMap ℂ A)
  | n+1 => stage s n ∪ (fun p : A×A=>p.1+p.2) '' (stage s n ×ˢ stage s n) ∪
      (fun p : A×A=>p.1*p.2) '' (stage s n ×ˢ stage s n) ∪ star '' stage s n
lemma stage_step (s : Set A) (n : ℕ) : stage s n ⊆ stage s (n+1) :=
  fun _ hx => Or.inl (Or.inl (Or.inl hx))
lemma stage_mono (s : Set A) : Monotone (stage s) := monotone_nat_of_le_succ (stage_step s)
def termAlgebra (s : Set A) : StarSubalgebra ℂ A where
  carrier := ⋃ n, stage s n
  zero_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨0,map_zero _⟩⟩
  one_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨1,map_one _⟩⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩))⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩)⟩
  algebraMap_mem' z := mem_iUnion.mpr ⟨0,Or.inr ⟨z,rfl⟩⟩
  star_mem' := by
    intro a ha
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨n+1,Or.inr ⟨a,hn,rfl⟩⟩
end

open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
abbrev Term (A : Type*) := A×A×A×A
def term {R : Type*} [Ring R] (t : Term R) : R := t.1*(t.2.1*t.2.2.1-t.2.2.1*t.2.1)*t.2.2.2
end KirchbergRordam.GenericRW.SeparableReduction

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_CentralSequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


namespace KirchbergRordam.NormUltrapower
open Filter Topology TopologicalSpace
open scoped CStarAlgebra
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

inductive CollapseTest (S : Type*)
  | add (x y : S) | mul (x y : S) | adjoint (x : S)
  | zero | one | imag | value (x : S)
  deriving Countable

namespace CollapseTest
variable {S : Type*} [Ring S] [StarRing S]

def eval {B : Type*} [CStarAlgebra B] (j : S) (f : S → B) : CollapseTest S → B
  | .add x y => f (x+y)-(f x+f y)
  | .mul x y => f (x*y)-f x*f y
  | .adjoint x => f (star x)-star (f x)
  | .zero => f 0
  | .one => f 1-1
  | .imag => f j-algebraMap ℂ B Complex.I
  | .value x => f x

end CollapseTest


end KirchbergRordam.NormUltrapower

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MatrixPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra


open scoped CStarAlgebra ComplexOrder
namespace KirchbergRordam.UnitaryPaths

variable {A : Type*} [CStarAlgebra A]


@[fun_prop] lemma phase_continuous : Continuous phase := by unfold phase; fun_prop
@[simp] lemma phase_zero : phase 0 = 1 := by simp [phase]
@[simp] lemma phase_one : phase 1 = -1 := by simp [phase, Complex.exp_pi_mul_I]


end KirchbergRordam.UnitaryPaths

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


namespace KirchbergRordam

open scoped Matrix Kronecker ComplexOrder


def matrixUnit {n : ℕ} (i j : Fin n) : CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single i j 1)

@[simp]
theorem matrixUnit_mul {n : ℕ} (i j k : Fin n) :
    matrixUnit i j * matrixUnit j k = matrixUnit i k := by
  unfold matrixUnit
  rw [← map_mul]
  simp only [Matrix.single_mul_single_same, mul_one]

end KirchbergRordam


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_RepresentationTheory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


open NormedSpace
open scoped ComplexOrder
namespace KirchbergRordam
namespace States

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

lemma norm_rotation (a : A) (ha : IsSelfAdjoint a) (t : ℝ) :
    ‖exp (t • (Complex.I • a))‖ = 1 := by
  have he : exp (t • (Complex.I • a)) =
      (selfAdjoint.expUnitary (t • (⟨a, ha⟩ : selfAdjoint A)) : A) := by
    change exp (t • (Complex.I • a)) = exp (Complex.I • t • a)
    rw [smul_comm]
  rw [he, CStarRing.norm_coe_unitary]

lemma eval_selfAdjoint_im_zero (φ : A →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) (h1 : φ 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) : (φ a).im = 0 := by
  let l : A →L[ℝ] ℝ := Complex.reCLM.comp (φ.restrictScalars ℝ)
  have hd : HasDerivAt (fun t : ℝ => l (exp (t • (Complex.I • a))))
      (-(φ a).im) 0 := by
    have hh := l.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_exp_smul_const (Complex.I • a) (0 : ℝ))
    convert hh using 1 <;> first | rfl | simp [l, map_smul, Complex.mul_re]
  have hmax : IsLocalMax (fun t : ℝ => l (exp (t • (Complex.I • a)))) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change (φ (exp (t • (Complex.I • a)))).re ≤ (φ (exp ((0 : ℝ) • (Complex.I • a)))).re
    simp only [zero_smul, exp_zero, h1, Complex.one_re]
    exact (Complex.re_le_norm _).trans <|
      (φ.le_opNorm _).trans <| by rw [norm_rotation a ha t, mul_one]; exact hφ
  exact neg_eq_zero.mp (hmax.hasDerivAt_eq_zero hd)

variable [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]

lemma eval_nonneg (φ : A →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) (h1 : φ 1 = 1)
    (a : A) (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hi := eval_selfAdjoint_im_zero φ hφ h1 a (IsSelfAdjoint.of_nonneg ha)
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, hi.symm⟩
  by_cases hz : a = 0
  · simp [hz]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr hz
  let b := ‖a‖⁻¹ • a
  have hb : 0 ≤ b := smul_nonneg (inv_nonneg.mpr hn.le) ha
  have hbn : ‖b‖ ≤ 1 := by
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hb1 : b ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg b hb).mp hbn
  have hn1 : ‖1 - b‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (sub_nonneg.mpr hb1)).mpr (sub_le_self _ hb)
  have hh : (φ (1 - b)).re ≤ 1 :=
    (Complex.re_le_norm _).trans <| (φ.le_opNorm _).trans <|
      (mul_le_mul_of_nonneg_left hn1 (norm_nonneg φ)).trans (by simpa using hφ)
  rw [map_sub, h1, Complex.sub_re, Complex.one_re] at hh
  have hbr : (φ b).re = ‖a‖⁻¹ * (φ a).re := by
    dsimp [b]
    change ((φ.restrictScalars ℝ) (‖a‖⁻¹ • a)).re = _
    rw [map_smul]
    simp
  rw [hbr] at hh
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp (by linarith : 0 ≤ ‖a‖⁻¹ * (φ a).re)


end States
end KirchbergRordam


open scoped ComplexOrder
namespace KirchbergRordam
namespace PureStates
variable (A : Type*) [CStarAlgebra A]

def normStates : Set (WeakDual ℂ A) := {φ | ‖φ.toStrongDual‖ ≤ 1 ∧ φ 1 = 1}

def evaluationReal : WeakDual ℂ A →ₗ[ℝ] (A → ℂ) where
  toFun φ := φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance locallyConvexReal : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  LocallyConvexSpace.induced (evaluationReal A)

variable [Nontrivial A]


def IsPure (φ : A →L[ℂ] ℂ) : Prop :=
  (StrongDual.toWeakDual φ) ∈ (normStates A).extremePoints ℝ

variable {A}

omit [Nontrivial A] in
lemma IsPure.norm_le_one {φ : A →L[ℂ] ℂ} (hp : IsPure A φ) : ‖φ‖ ≤ 1 := hp.1.1
omit [Nontrivial A] in
lemma IsPure.map_one {φ : A →L[ℂ] ℂ} (hp : IsPure A φ) : φ 1 = 1 := hp.1.2

omit [Nontrivial A] in
lemma IsPure.extreme {φ ψ χ : A →L[ℂ] ℂ} (hp : IsPure A φ)
    (hψ : ‖ψ‖ ≤ 1) (hψ1 : ψ 1 = 1) (hχ : ‖χ‖ ≤ 1) (hχ1 : χ 1 = 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (he : φ = t • ψ + (1 - t) • χ) : ψ = φ := by
  apply StrongDual.toWeakDual.injective
  apply hp.2 (show (StrongDual.toWeakDual ψ) ∈ normStates A from ⟨hψ, hψ1⟩)
    (show (StrongDual.toWeakDual χ) ∈ normStates A from ⟨hχ, hχ1⟩)
  exact ⟨t, 1 - t, ht, sub_pos.mpr ht1, by ring, by
    change t • ψ + (1 - t) • χ = φ
    exact he.symm⟩

end PureStates
end KirchbergRordam

open scoped InnerProductSpace
namespace KirchbergRordam
namespace Representations
variable {A : Type*} [CStarAlgebra A] [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

def gnsVector (a : A) : f.GNS := (f.toPreGNS a : f.GNS)

@[simp] lemma gnsVector_inner (a b : A) :
    ⟪gnsVector f a, gnsVector f b⟫_ℂ = f (star a * b) := by
  simp [gnsVector, PositiveLinearMap.preGNS_inner_def]

@[simp] lemma gnsVector_apply (a b : A) :
    f.gnsStarAlgHom a (gnsVector f b) = gnsVector f (a * b) := by
  simp [gnsVector, PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.leftMulMapPreGNS]

lemma positive_bound (a : A) : ‖f a‖ ≤ (f 1).re * ‖a‖ := by
  let ξ := gnsVector f 1
  have hi : f a = ⟪ξ, f.gnsStarAlgHom a ξ⟫_ℂ := by
    dsimp [ξ]
    rw [gnsVector_apply, gnsVector_inner]
    simp
  have hn : ‖ξ‖ ^ 2 = (f 1).re := by
    calc
      _ = (⟪ξ, ξ⟫_ℂ).re := (inner_self_eq_norm_sq (𝕜 := ℂ) ξ).symm
      _ = (f 1).re := by dsimp [ξ]; rw [gnsVector_inner]; simp
  calc
    ‖f a‖ = ‖⟪ξ, f.gnsStarAlgHom a ξ⟫_ℂ‖ := congrArg norm hi
    _ ≤ ‖ξ‖ * ‖f.gnsStarAlgHom a ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖a‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left
      ((f.gnsStarAlgHom a).le_opNorm ξ |>.trans <| mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom a) (norm_nonneg ξ)) (norm_nonneg ξ)
    _ = (f 1).re * ‖a‖ := by rw [← hn]; ring

def positiveCLM : A →L[ℂ] ℂ :=
  f.toLinearMap.mkContinuous (f 1).re (positive_bound f)

@[simp] lemma positiveCLM_apply (a : A) : positiveCLM f a = f a := rfl

lemma positiveCLM_norm : ‖positiveCLM f‖ ≤ (f 1).re := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact (Complex.nonneg_iff.mp (f.map_nonneg zero_le_one)).1
  · exact positive_bound f

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

def representationCLM : A →L[ℂ] (H →L[ℂ] H) :=
  π.toAlgHom.toLinearMap.mkContinuous 1 fun a => by
    simpa using NonUnitalStarAlgHom.norm_apply_le π a

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma representationCLM_apply (a : A) : representationCLM π a = π a := rfl

def coefficient (T : H →L[ℂ] H) : A →L[ℂ] ℂ where
  toFun a := ⟪ξ, T (π a ξ)⟫_ℂ
  map_add' a b := by simp
  map_smul' z a := by simp
  cont := (continuous_const.inner <| T.continuous.comp <|
    ((representationCLM π).continuous.clm_apply continuous_const))

omit instPartialOrderA instStarOrderedRingA in
@[simp] lemma coefficient_apply.{contextLevel1, contextLevel2}
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {H : Type contextLevel2}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (π : A →⋆ₐ[ℂ] H →L[ℂ] H)
    (ξ : H)
    (T : H →L[ℂ] H) (a : A) :
    coefficient π ξ T a = ⟪ξ, T (π a ξ)⟫_ℂ := rfl

lemma coefficient_nonneg (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (hc : ∀ a, Commute T (π a)) (a : A) (ha : 0 ≤ a) :
    0 ≤ coefficient π ξ T a := by
  let b := CFC.sqrt a
  have hb : IsSelfAdjoint (π b) := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).map π
  have hab : a = b * b := (CFC.sqrt_mul_sqrt_self a ha).symm
  have ht := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hT
  have he : coefficient π ξ T a = ⟪π b ξ, T (π b ξ)⟫_ℂ := by
    rw [coefficient_apply, hab, map_mul]
    have hh := congrArg (fun S : H →L[ℂ] H => S (π b ξ)) (hc b).eq
    change ⟪ξ, T (π b (π b ξ))⟫_ℂ = _
    change T (π b (π b ξ)) = π b (T (π b ξ)) at hh
    rw [hh]
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun S : H →L[ℂ] H => ⟪S ξ, T (π b ξ)⟫_ℂ) hb.star_eq
  rw [he]
  exact ht.inner_nonneg_right _

lemma coefficient_norm (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (hc : ∀ a, Commute T (π a)) :
    ‖coefficient π ξ T‖ ≤ (⟪ξ, T ξ⟫_ℂ).re := by
  let g : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (coefficient π ξ T).toLinearMap
    (coefficient_nonneg π ξ T hT hc)
  have he : positiveCLM g = coefficient π ξ T := by ext; rfl
  have hn := positiveCLM_norm g
  rw [he] at hn
  change ‖coefficient π ξ T‖ ≤ (coefficient π ξ T 1).re at hn
  simpa only [coefficient_apply, map_one, one_apply_eq_self] using hn

end Representations
end KirchbergRordam
namespace KirchbergRordam.PureStates
variable {A : Type*} [CStarAlgebra A]

lemma IsPure.split (φ g h : A →L[ℂ] ℂ) (hp : IsPure A φ)
    (hn : ‖g‖ ≤ (g 1).re) (hm : ‖h‖ ≤ (h 1).re)
    (hg : 0 ≤ g 1) (hh : 0 ≤ h 1) (he : g + h = φ) :
    g = (g 1).re • φ := by
  let t := (g 1).re
  let s := (h 1).re
  have hg1 : g 1 = (t : ℂ) := by
    apply Complex.ext <;> simp [t, (Complex.nonneg_iff.mp hg).2.symm]
  have hh1 : h 1 = (s : ℂ) := by
    apply Complex.ext <;> simp [s, (Complex.nonneg_iff.mp hh).2.symm]
  have ht : 0 ≤ t := (Complex.nonneg_iff.mp hg).1
  have hs : 0 ≤ s := (Complex.nonneg_iff.mp hh).1
  have hts : t + s = 1 := by
    have he1 := congrArg (fun f : A →L[ℂ] ℂ => (f 1).re) he
    simpa only [_root_.add_apply, Complex.add_re, hp.map_one, Complex.one_re] using he1
  by_cases ht0 : t = 0
  · have hg0 : g = 0 := norm_eq_zero.mp (le_antisymm (hn.trans_eq ht0) (norm_nonneg _))
    change g = t • φ
    rw [ht0, hg0]
    ext a
    simp only [_root_.smul_apply, zero_apply]
    exact (zero_smul ℝ (φ a)).symm
  by_cases hs0 : s = 0
  · have hh0 : h = 0 := norm_eq_zero.mp (le_antisymm (hm.trans_eq hs0) (norm_nonneg _))
    have ht1 : t = 1 := by linarith
    change g = t • φ
    simpa [ht1, hh0] using he
  have htn : ‖t⁻¹ • g‖ ≤ 1 := calc
    _ = t⁻¹ * ‖g‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht)]
    _ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ht)
    _ = 1 := inv_mul_cancel₀ ht0
  have hsn : ‖s⁻¹ • h‖ ≤ 1 := calc
    _ = s⁻¹ * ‖h‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hs)]
    _ ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hs)
    _ = 1 := inv_mul_cancel₀ hs0
  have hgn : (t⁻¹ • g) 1 = 1 := by
    simp only [_root_.smul_apply, hg1, Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast ht0)
  have hhn : (s⁻¹ • h) 1 = 1 := by
    simp only [_root_.smul_apply, hh1, Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast hs0)
  have hf := hp.extreme htn hgn hsn hhn t (lt_of_le_of_ne ht (Ne.symm ht0))
    (by linarith [lt_of_le_of_ne hs (Ne.symm hs0)]) (by
      rw [show 1 - t = s by linarith, smul_smul, smul_smul,
        mul_inv_cancel₀ ht0, mul_inv_cancel₀ hs0, one_smul, one_smul]
      exact he.symm)
  have heq := congrArg (fun f : A →L[ℂ] ℂ => t • f) hf
  simpa only [smul_smul, mul_inv_cancel₀ ht0, one_smul] using heq

end KirchbergRordam.PureStates

namespace KirchbergRordam.Representations
variable {A : Type*} [CStarAlgebra A] [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

lemma coefficient_commutant_injective (hd : DenseRange (fun a => π a ξ))
    (T S : H →L[ℂ] H) (hT : ∀ a, Commute T (π a)) (hS : ∀ a, Commute S (π a))
    (he : coefficient π ξ T = coefficient π ξ S) : T = S := by
  have hξ : T ξ = S ξ := by
    apply ext_inner_left ℂ
    intro y
    refine hd.induction_on (p := fun y => ⟪y, T ξ⟫_ℂ = ⟪y, S ξ⟫_ℂ) y
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    have he' := congrArg (fun f : A →L[ℂ] ℂ => f (star a)) he
    have ha (U : H →L[ℂ] H) (hU : ∀ a, Commute U (π a)) :
        coefficient π ξ U (star a) = ⟪π a ξ, U ξ⟫_ℂ := by
      rw [coefficient_apply]
      have hc := congrArg (fun V : H →L[ℂ] H => V ξ) (hU (star a)).eq
      change U (π (star a) ξ) = π (star a) (U ξ) at hc
      rw [hc, map_star]
      exact ContinuousLinearMap.adjoint_inner_right (π a) ξ (U ξ)
    simpa only [ha T hT, ha S hS] using he'
  apply DFunLike.coe_injective
  apply hd.equalizer T.continuous S.continuous
  funext a
  change T (π a ξ) = S (π a ξ)
  have htc := congrArg (fun U : H →L[ℂ] H => U ξ) (hT a).eq
  have hsc := congrArg (fun U : H →L[ℂ] H => U ξ) (hS a).eq
  change T (π a ξ) = π a (T ξ) at htc
  change S (π a ξ) = π a (S ξ) at hsc
  rw [htc, hsc, hξ]

lemma positive_contraction_scalar (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ)
    (hφ : coefficient π ξ 1 = φ) (hd : DenseRange (fun a => π a ξ))
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (hT1 : T ≤ 1) (hc : ∀ a, Commute T (π a)) :
    ∃ t : ℝ, T = t • 1 := by
  let g := coefficient π ξ T
  let h := coefficient π ξ (1 - T)
  have hTc : ∀ a, Commute (1 - T) (π a) := fun a => (Commute.one_left _).sub_left (hc a)
  have hsum : g + h = φ := by
    rw [← hφ]
    ext a
    simp [g, h, coefficient]
  have hgn : ‖g‖ ≤ (g 1).re := by
    simpa only [g, coefficient_apply, map_one, one_apply_eq_self] using coefficient_norm π ξ T hT hc
  have hhn : ‖h‖ ≤ (h 1).re := by
    simpa only [h, coefficient_apply, map_one, one_apply_eq_self] using
      coefficient_norm π ξ (1 - T) (sub_nonneg.mpr hT1) hTc
  have he := hp.split φ g h hgn hhn (coefficient_nonneg π ξ T hT hc 1 zero_le_one)
    (coefficient_nonneg π ξ (1 - T) (sub_nonneg.mpr hT1) hTc 1 zero_le_one) hsum
  refine ⟨(g 1).re, coefficient_commutant_injective π ξ hd T ((g 1).re • 1) hc
    (fun a => (Commute.one_left _).smul_left _) ?_⟩
  change g = coefficient π ξ ((g 1).re • 1)
  calc
    g = (g 1).re • φ := he
    _ = coefficient π ξ ((g 1).re • 1) := by
      conv_lhs => rw [← hφ]
      ext a
      simp [coefficient]

end KirchbergRordam.Representations
namespace KirchbergRordam.Representations
variable {A : Type*} [CStarAlgebra A] [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
variable (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ)
    (hφ : coefficient π ξ 1 = φ) (hd : DenseRange (fun a => π a ξ))

include hp hφ hd

lemma positive_scalar (T : H →L[ℂ] H) (hT : 0 ≤ T) (hc : ∀ a, Commute T (π a)) :
    ∃ t : ℝ, T = t • 1 := by
  by_cases hz : T = 0
  · exact ⟨0, by simp [hz]⟩
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr hz
  have hS : 0 ≤ ‖T‖⁻¹ • T := smul_nonneg (inv_nonneg.mpr hn.le) hT
  have hS1 : ‖T‖⁻¹ • T ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hS).mp <| by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  obtain ⟨t, ht⟩ := positive_contraction_scalar π ξ φ hp hφ hd _ hS hS1
    (fun a => (hc a).smul_left _)
  refine ⟨‖T‖ * t, ?_⟩
  have he := congrArg (fun U : H →L[ℂ] H => ‖T‖ • U) ht
  simpa only [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] using he

lemma selfAdjoint_scalar (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hc : ∀ a, Commute T (π a)) : ∃ t : ℝ, T = t • 1 := by
  have hn := hT.neg.le_algebraMap_norm_self
  rw [norm_neg, Algebra.algebraMap_eq_smul_one] at hn
  have hpT : 0 ≤ T + ‖T‖ • (1 : H →L[ℂ] H) := neg_le_iff_add_nonneg'.mp hn
  obtain ⟨t, ht⟩ := positive_scalar π ξ φ hp hφ hd _ hpT
    (fun a => (hc a).add_left ((Commute.one_left _).smul_left _))
  refine ⟨t - ‖T‖, ?_⟩
  rw [sub_smul]
  exact eq_sub_iff_add_eq.mpr ht


theorem pure_cyclic_scalar_commutant (T : H →L[ℂ] H)
    (hc : ∀ a, Commute T (π a)) : ∃ z : ℂ, T = z • 1 := by
  have hcs (a : A) : Commute (star T) (π a) := by
    exact (show Commute T (star (π a)) by simpa only [map_star] using hc (star a)).star_left
  have hcr (a : A) : Commute (realPart T : H →L[ℂ] H) (π a) := by
    rw [realPart_apply_coe]
    exact ((hc a).add_left (hcs a)).smul_left _
  have hci (a : A) : Commute (imaginaryPart T : H →L[ℂ] H) (π a) := by
    rw [imaginaryPart_apply_coe]
    exact (((hc a).sub_left (hcs a)).smul_left _).smul_left _
  obtain ⟨r, hr⟩ := selfAdjoint_scalar π ξ φ hp hφ hd _ (realPart T).property hcr
  obtain ⟨s, hs⟩ := selfAdjoint_scalar π ξ φ hp hφ hd _ (imaginaryPart T).property hci
  refine ⟨(r : ℂ) + Complex.I * (s : ℂ), ?_⟩
  calc
    T = (realPart T : H →L[ℂ] H) + Complex.I • (imaginaryPart T : H →L[ℂ] H) :=
      (realPart_add_I_smul_imaginaryPart T).symm
    _ = ((r : ℂ) + Complex.I * (s : ℂ)) • 1 := by
      rw [hr, hs, add_smul, mul_smul]
      simp only [Complex.coe_smul]

end KirchbergRordam.Representations
namespace KirchbergRordam
namespace Representations
variable {A : Type*} [CStarAlgebra A] [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A]

lemma gns_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsVector f 1)) := by
  have hd : DenseRange (gnsVector f) := by
    intro x
    apply closure_mono (t := Set.range (gnsVector f)) _ (UniformSpace.Completion.denseRange_coe x)
    rintro _ ⟨a, rfl⟩
    exact ⟨f.ofPreGNS a, by simp [gnsVector]⟩
  simpa only [gnsVector_apply, mul_one] using hd


variable [Nontrivial A]

def stateOfPure (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ φ.toLinearMap (States.eval_nonneg φ hp.norm_le_one hp.map_one)

@[simp] lemma stateOfPure_apply (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) (a : A) :
    stateOfPure φ hp a = φ a := rfl

lemma pure_gns_coefficient (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) :
    coefficient (stateOfPure φ hp).gnsStarAlgHom (gnsVector (stateOfPure φ hp) 1) 1 = φ := by
  ext a
  rw [coefficient_apply, one_apply_eq_self, gnsVector_apply, gnsVector_inner]
  simp

lemma pure_gns_nontrivial (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) :
    Nontrivial (stateOfPure φ hp).GNS := by
  apply nontrivial_of_ne (gnsVector (stateOfPure φ hp) 1) 0
  intro he
  have hh := gnsVector_inner (stateOfPure φ hp) 1 1
  rw [he] at hh
  simp [hp.map_one] at hh

end Representations

universe u

structure IrreducibleRepresentation (A : Type u) [CStarAlgebra A] where
  space : Type u
  [normed : NormedAddCommGroup space]
  [inner : InnerProductSpace ℂ space]
  [complete : CompleteSpace space]
  [nontrivial : Nontrivial space]
  representation : A →⋆ₐ[ℂ] (space →L[ℂ] space)
  scalar_commutant : ∀ T : space →L[ℂ] space,
    (∀ a, Commute T (representation a)) → ∃ z : ℂ, T = z • 1

attribute [instance] IrreducibleRepresentation.normed IrreducibleRepresentation.inner
  IrreducibleRepresentation.complete IrreducibleRepresentation.nontrivial

namespace Representations
variable {A : Type u} [CStarAlgebra A] [instPartialOrderA : PartialOrder A] [instStarOrderedRingA : StarOrderedRing A] [Nontrivial A]

def pureRepresentation (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ) :
    IrreducibleRepresentation A where
  space := (stateOfPure φ hp).GNS
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  nontrivial := pure_gns_nontrivial φ hp
  representation := (stateOfPure φ hp).gnsStarAlgHom
  scalar_commutant := pure_cyclic_scalar_commutant _ _ φ hp (pure_gns_coefficient φ hp)
    (gns_cyclic _)

end Representations


end KirchbergRordam

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam
namespace MaxTensor

variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


variable {A B}

variable {C : Type*} [CStarAlgebra C]


open scoped CStarAlgebra


universe u


structure CStarPack where
  carrier : Type u
  inst : CStarAlgebra carrier

attribute [instance] CStarPack.inst
instance instCoeSortCStarPackType : CoeSort CStarPack (Type u) := ⟨CStarPack.carrier⟩


end MaxTensor
end KirchbergRordam
namespace KirchbergRordam.StarRangeFactor
variable {A B C : Type*} [Ring A] [Ring B] [Ring C]
  [StarRing A] [StarRing B] [StarRing C]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
  [instStarModuleℂA : StarModule ℂ A] [instStarModuleℂB : StarModule ℂ B] [StarModule ℂ C]

def descend (f : A →⋆ₐ[ℂ] C) (g : A →⋆ₐ[ℂ] B)
    (hk : ∀ a, f a=0 → g a=0) : f.range →⋆ₐ[ℂ] B := by
  classical
  let r : f.range → A := fun y => y.property.choose
  have hr (y : f.range) : f (r y)=y.val := y.property.choose_spec
  have he (a : A) (y : f.range) (h : f a=y.val) : g a=g (r y) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hk
    rw [map_sub,h,hr,sub_self]
  exact {
    toFun := fun y => g (r y)
    map_zero' := (he 0 0 (map_zero f)).symm.trans (map_zero g)
    map_one' := (he 1 1 (map_one f)).symm.trans (map_one g)
    map_add' := fun x y => (he (r x+r y) (x+y) (by rw [map_add,hr,hr]; rfl)).symm.trans (map_add g _ _)
    map_mul' := fun x y => (he (r x*r y) (x*y) (by rw [map_mul,hr,hr]; rfl)).symm.trans (map_mul g _ _)
    commutes' := fun z => (he (algebraMap ℂ A z) (algebraMap ℂ f.range z) (f.commutes z)).symm.trans (g.commutes z)
    map_star' := fun x => (he (star (r x)) (star x) (by rw [map_star,hr]; rfl)).symm.trans (map_star g _) }

omit instStarModuleℂA instStarModuleℂB in
@[simp] lemma descend_apply.{contextLevel1, contextLevel2, contextLevel3}
    {A : Type contextLevel1}
    {B : Type contextLevel2}
    {C : Type contextLevel3}
    [Ring A]
    [Ring B]
    [Ring C]
    [StarRing A]
    [StarRing B]
    [StarRing C]
    [Algebra ℂ A]
    [Algebra ℂ B]
    [Algebra ℂ C]
    [StarModule ℂ A]
    [StarModule ℂ B]
    [StarModule ℂ C]
    (f : A →⋆ₐ[ℂ] C) (g : A →⋆ₐ[ℂ] B)
    (hk : ∀ a, f a=0 → g a=0) (a : A) :
    descend f g hk ⟨f a,⟨a,rfl⟩⟩=g a := by
  dsimp [descend]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hk
  rw [map_sub]
  exact sub_eq_zero.mpr (Exists.choose_spec (show ∃ x, f x=f a from ⟨a,rfl⟩))
end KirchbergRordam.StarRangeFactor

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_TensorSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor
lemma continuous_starHom {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) : Continuous f := map_continuous f

end KirchbergRordam.PrimeTensorSections
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SymmetryFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

open scoped CStarAlgebra ComplexOrder
namespace KirchbergRordam.SymmetryFlow

variable {A : Type*} [CStarAlgebra A]

def phase (t : ℝ) : ℂ := Complex.exp ((t * Real.pi) * Complex.I)

@[fun_prop] lemma phase_continuous : Continuous phase := by unfold phase; fun_prop
@[simp] lemma phase_zero : phase 0 = 1 := by simp [phase]
@[simp] lemma phase_one : phase 1 = -1 := by simp [phase, Complex.exp_pi_mul_I]
lemma phase_unitary (t : ℝ) : star (phase t) * phase t = 1 := by
  have hn : ‖phase t‖ = 1 := by
    simpa [phase, Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I (t * Real.pi)
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hn]
  norm_num

def involutionValue (U : A) (t : ℝ) : A :=
  ((1 + phase t) / 2) • (1:A) + ((1 - phase t) / 2) • U

lemma involutionValue_continuous (U : A) : Continuous (involutionValue U) := by
  unfold involutionValue
  fun_prop

lemma involutionValue_unitary (U : A) (hs : star U = U) (hm : U * U = 1)
    (t : ℝ) : involutionValue U t ∈ unitary A := by
  have hz := phase_unitary t
  have h1 : (star ((1:ℂ)+phase t)/2)*((1+phase t)/2)+
      (star ((1:ℂ)-phase t)/2)*((1-phase t)/2)=1 := by
    simp only [star_add,star_sub,star_one]
    calc
      _ = (1+star (phase t)*phase t)/2 := by ring
      _ = 1 := by rw [hz]; norm_num
  have h2 : (star ((1:ℂ)+phase t)/2)*((1-phase t)/2)+
      (star ((1:ℂ)-phase t)/2)*((1+phase t)/2)=0 := by
    simp only [star_add,star_sub,star_one]
    calc
      _ = (1-star (phase t)*phase t)/2 := by ring
      _ = 0 := by rw [hz]; norm_num
  have h : star (involutionValue U t) * involutionValue U t = 1 := by
    simp only [involutionValue, star_add, star_smul, star_one, hs, star_div₀,
      star_ofNat, star_sub, smul_add, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul, one_mul, mul_one, hm]
    calc
      _ = (((1+star (phase t))/2)*((1+phase t)/2)+
            ((1-star (phase t))/2)*((1-phase t)/2)) • (1:A) +
          (((1+star (phase t))/2)*((1-phase t)/2)+
            ((1-star (phase t))/2)*((1+phase t)/2)) • U := by
              rw [add_smul, add_smul]; module
      _ = 1 := by
        simp only [star_add, star_sub, star_one] at h1 h2
        rw [h1, h2, one_smul, zero_smul, add_zero]
  refine ⟨h, ?_⟩
  have hc : Commute (involutionValue U t) (star (involutionValue U t)) := by
    unfold involutionValue
    simp only [star_add, star_smul, star_one, hs]
    exact ((Commute.one_left _).smul_left _).add_left
      ((((Commute.one_right U).smul_right _).add_right
        ((Commute.refl U).smul_right _)).smul_left _)
  exact hc.eq.trans h


def flow (U : unitary A) (hs : star (U:A)=U) (t : ℝ) : unitary A :=
  ⟨involutionValue (U:A) t,
    involutionValue_unitary (U:A) hs (by simpa only [hs] using Unitary.coe_star_mul_self U) t⟩
@[simp] lemma coe_flow (U : unitary A) (hs) (t : ℝ) :
    (flow U hs t : A) = involutionValue (U:A) t := rfl
@[simp] lemma flow_zero (U : unitary A) (hs) : flow U hs 0=1 := by
  apply Subtype.ext
  simp [involutionValue]
@[simp] lemma flow_one (U : unitary A) (hs) : flow U hs 1=U := by
  apply Subtype.ext
  simp [involutionValue]
@[fun_prop] lemma flow_continuous (U : unitary A) (hs) : Continuous (flow U hs) :=
  (involutionValue_continuous _).subtype_mk _
lemma phase_add (s t : ℝ) : phase (s+t)=phase s*phase t := by
  unfold phase
  rw [Complex.ofReal_add, add_mul, add_mul, Complex.exp_add]
lemma flow_add (U : unitary A) (hs) (s t : ℝ) :
    flow U hs (s+t)=flow U hs s*flow U hs t := by
  apply Subtype.ext
  have hm : (U:A)*(U:A)=1 := by simpa only [hs] using Unitary.coe_star_mul_self U
  change involutionValue (U:A) (s+t)=involutionValue (U:A) s*involutionValue (U:A) t
  simp only [involutionValue,phase_add,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    one_mul,mul_one,hm]
  have h1 : (1+phase s*phase t)/2 = (1+phase s)/2*((1+phase t)/2)+
      (1-phase s)/2*((1-phase t)/2) := by ring
  have h2 : (1-phase s*phase t)/2 = (1+phase s)/2*((1-phase t)/2)+
      (1-phase s)/2*((1+phase t)/2) := by ring
  rw [h1,h2,add_smul,add_smul]
  module
end KirchbergRordam.SymmetryFlow


namespace KirchbergRordam.UnitaryConjugacySquare
open Filter Topology
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

@[simp] lemma flow_zero (V : Flow A) : V 0=1 := V.zero
lemma flow_add (V : Flow A) (s t : ℝ) : V (s+t)=V s*V t := V.add s t
@[fun_prop] lemma flow_continuous (V : Flow A) : Continuous V := V.continuous_toFun

def symmetry (u : unitary A) (hu : star (u:A)=u) : Flow A where
  toFun := SymmetryFlow.flow u hu
  continuous_toFun := SymmetryFlow.flow_continuous u hu
  zero := SymmetryFlow.flow_zero u hu
  add := SymmetryFlow.flow_add u hu

abbrev Square := unitInterval × unitInterval

def radius (x : Square) : ℝ := (x.1:ℝ)+(x.2:ℝ)-(x.1:ℝ)*(x.2:ℝ)
def ratio (x : Square) : ℝ := (x.2:ℝ)/radius x
@[fun_prop] lemma radius_continuous : Continuous radius := by unfold radius; fun_prop
lemma radius_nonneg (x : Square) : 0 ≤ radius x := by
  rcases x.1.property with ⟨h10,h11⟩
  rcases x.2.property with ⟨h20,h21⟩
  unfold radius
  nlinarith
lemma fst_le_radius (x : Square) : (x.1:ℝ) ≤ radius x := by
  rcases x.1.property with ⟨h10,h11⟩
  rcases x.2.property with ⟨h20,h21⟩
  unfold radius
  nlinarith
lemma snd_le_radius (x : Square) : (x.2:ℝ) ≤ radius x := by
  rcases x.1.property with ⟨h10,h11⟩
  rcases x.2.property with ⟨h20,h21⟩
  unfold radius
  nlinarith
lemma radius_eq_zero_iff (x : Square) : radius x=0 ↔ x=(0,0) := by
  constructor
  · intro h
    have h1 := fst_le_radius x; have h2 := snd_le_radius x
    rw [h] at h1 h2
    apply Prod.ext <;> apply Subtype.ext
    · exact le_antisymm h1 x.1.property.1
    · exact le_antisymm h2 x.2.property.1
  · rintro rfl
    simp [radius]
lemma ratio_nonneg (x : Square) : 0 ≤ ratio x :=
  div_nonneg x.2.property.1 (radius_nonneg x)
lemma ratio_le_one (x : Square) : ratio x ≤ 1 := by
  by_cases h : radius x=0
  · simp [ratio,h]
  · exact (div_le_one₀ ((radius_nonneg x).lt_of_ne' h)).mpr (snd_le_radius x)
lemma scaled_ratio_nonneg (x : Square) : 0 ≤ (x.1:ℝ)*ratio x :=
  mul_nonneg x.1.property.1 (ratio_nonneg x)
lemma scaled_ratio_le (x : Square) : (x.1:ℝ)*ratio x ≤ (x.1:ℝ) := by
  simpa using mul_le_mul_of_nonneg_left (ratio_le_one x) x.1.property.1
lemma scaled_ratio_tendsto : Tendsto (fun x : Square => (x.1:ℝ)*ratio x)
    (𝓝 (0,0)) (𝓝 0) := by
  apply squeeze_zero scaled_ratio_nonneg scaled_ratio_le
  exact (continuous_subtype_val.comp continuous_fst).continuousAt


def square (V : Flow A) (U : ℝ → unitary A) (x : Square) : unitary A :=
  V (ratio x)*U (radius x)*V (-((1-(x.1:ℝ))*ratio x))

lemma square_origin (V : Flow A) (U : ℝ → unitary A) (hU : U 0=1) :
    square V U (0,0)=1 := by simp [square,ratio,radius,hU]

lemma square_error (V : Flow A) (U : ℝ → unitary A) (x : Square) :
    ‖(square V U x:A)-1‖ ≤
      ‖(U (radius x):A)-1‖+‖(V ((x.1:ℝ)*ratio x):A)-1‖ := by
  let a := ratio x
  let c := -((1-(x.1:ℝ))*ratio x)
  have he : a+c=(x.1:ℝ)*ratio x := by dsimp [a,c]; ring
  have hv : (V a:A)*(V c:A)=V ((x.1:ℝ)*ratio x) := by
    rw [← (unitary A).coe_mul,← flow_add,he]
  have hd : (square V U x:A)-1 =
      (V a:A)*((U (radius x):A)-1)*(V c:A)+((V a:A)*(V c:A)-1) := by
    change (V a:A)*(U (radius x):A)*(V c:A)-1=_
    noncomm_ring
  rw [hd]
  calc
    _ ≤ ‖(V a:A)*((U (radius x):A)-1)*(V c:A)‖+
        ‖(V a:A)*(V c:A)-1‖ := norm_add_le _ _
    _ = _ := by rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,hv]

lemma square_continuous (V : Flow A) (U : ℝ → unitary A)
    (hU : Continuous U) (hzero : U 0=1) : Continuous (square V U) := by
  apply continuous_induced_rng.mpr
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x=(0,0)
  · subst x
    have hr : Tendsto (fun x : Square => ‖(U (radius x):A)-1‖) (𝓝 (0,0)) (𝓝 0) := by
      have h := ((continuous_subtype_val.comp hU).comp radius_continuous).continuousAt (x:=(0,0))
      have h' := (h.sub (tendsto_const_nhds (x := (1:A)))).norm
      simpa [radius,hzero] using h'.tendsto
    have hv : Tendsto (fun x : Square => ‖(V ((x.1:ℝ)*ratio x):A)-1‖)
        (𝓝 (0,0)) (𝓝 0) := by
      have h := ((continuous_subtype_val.comp V.continuous_toFun).continuousAt (x:=0)).tendsto.comp scaled_ratio_tendsto
      have h' := (h.sub (tendsto_const_nhds (x := (1:A)))).norm
      simpa using h'
    have hnorm := squeeze_zero (fun x : Square => norm_nonneg ((square V U x:A)-1))
      (square_error V U) (by simpa using hr.add hv)
    change Tendsto (fun x : Square => (square V U x:A)) (𝓝 (0,0)) (𝓝 (square V U (0,0):A))
    rw [show (square V U (0,0):A)=1 by rw [square_origin V U hzero]; rfl]
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  · have hr : ContinuousAt ratio x := by
      unfold ratio
      exact (continuous_subtype_val.comp continuous_snd).continuousAt.div
        radius_continuous.continuousAt (fun h => hx ((radius_eq_zero_iff x).mp h))
    have hc : ContinuousAt (fun y : Square => -((1-(y.1:ℝ))*ratio y)) x :=
      ((continuousAt_const.sub (continuous_subtype_val.comp continuous_fst).continuousAt).mul hr).neg
    apply continuous_subtype_val.continuousAt.comp
    exact ((V.continuous_toFun.continuousAt.comp hr).mul
      (hU.continuousAt.comp radius_continuous.continuousAt)).mul
      (V.continuous_toFun.continuousAt.comp hc)

end KirchbergRordam.UnitaryConjugacySquare


namespace KirchbergRordam.SymmetryConjugacyDiagram
open UnitaryConjugacySquare
variable {A : Type*} [CStarAlgebra A]

structure Data (A : Type*) [CStarAlgebra A] where
  H : unitary A
  K : unitary A
  hH : star (H:A)=H
  hK : star (K:A)=K
  commute : Commute H K
  L : unitInterval → unitary A
  continuous_L : Continuous L
  L_zero : L 0=1

namespace Data
variable (D : Data A)
def Hp : Flow A := symmetry D.H D.hH
def Kp : Flow A := symmetry D.K D.hK
def U (r : ℝ) : unitary A := star (D.L 1)*D.Hp r*D.L 1
def R (t : unitInterval) : unitary A := D.H*D.K*D.L t*star (D.H*D.K)
def W (x : Square) : unitary A :=
  D.R x.2*D.H*square D.Kp D.U x*star (D.L x.1)

@[simp] lemma Hp_one : D.Hp 1=D.H := SymmetryFlow.flow_one D.H D.hH
@[simp] lemma Kp_one : D.Kp 1=D.K := SymmetryFlow.flow_one D.K D.hK
@[simp] lemma H_star : star D.H=D.H := Subtype.ext D.hH
@[simp] lemma K_star : star D.K=D.K := Subtype.ext D.hK
@[simp] lemma U_zero : D.U 0=1 := by simp [U]
@[simp] lemma R_zero : D.R 0=1 := by
  simpa only [R,D.L_zero,mul_one,Unitary.star_eq_inv] using mul_inv_cancel (D.H*D.K)
@[fun_prop] lemma U_continuous : Continuous D.U := by unfold U; fun_prop
@[fun_prop] lemma R_continuous : Continuous D.R := by
  unfold R
  exact (continuous_const.mul D.continuous_L).mul continuous_const
@[fun_prop] lemma W_continuous : Continuous D.W := by
  unfold W
  exact (((D.R_continuous.comp continuous_snd).mul continuous_const).mul
    (square_continuous D.Kp D.U D.U_continuous D.U_zero)).mul
      (D.continuous_L.comp continuous_fst).star

end Data
end KirchbergRordam.SymmetryConjugacyDiagram


namespace KirchbergRordam.UnitaryDisplacement
variable {A : Type*} [CStarAlgebra A]
abbrev conj (u : unitary A) : A ≃⋆ₐ[ℂ] A := Unitary.conjStarAlgAut ℂ A u
def displacement (u : unitary A) (a : A) : ℝ := ‖conj u a-a‖

end KirchbergRordam.UnitaryDisplacement


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_UltrapowerSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam
open Filter
open scoped Topology CStarAlgebra
namespace Intertwining
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def limitHom (φ : ℕ → A →⋆ₐ[ℂ] B)
    (hφ : ∀ a, CauchySeq (fun n => φ n a)) : A →⋆ₐ[ℂ] B where
  toFun a := limUnder atTop (fun n => φ n a)
  map_zero' := by
    apply tendsto_nhds_unique (hφ 0).tendsto_limUnder
    simpa only [map_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : B)) atTop (𝓝 0))
  map_one' := by
    apply tendsto_nhds_unique (hφ 1).tendsto_limUnder
    simpa only [map_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : B)) atTop (𝓝 1))
  map_add' a b := by
    apply tendsto_nhds_unique (hφ (a+b)).tendsto_limUnder
    simpa only [map_add] using ((hφ a).tendsto_limUnder.add (hφ b).tendsto_limUnder)
  map_mul' a b := by
    apply tendsto_nhds_unique (hφ (a*b)).tendsto_limUnder
    simpa only [map_mul] using ((hφ a).tendsto_limUnder.mul (hφ b).tendsto_limUnder)
  commutes' z := by
    apply tendsto_nhds_unique (hφ (algebraMap ℂ A z)).tendsto_limUnder
    have he : (fun n => φ n (algebraMap ℂ A z)) =
        (fun _ : ℕ => algebraMap ℂ B z) := funext (fun n => (φ n).commutes z)
    rw [he]
    exact tendsto_const_nhds
  map_star' a := by
    apply tendsto_nhds_unique (hφ (star a)).tendsto_limUnder
    simpa only [map_star] using (hφ a).tendsto_limUnder.star
end Intertwining


end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Absorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.SeparableReduction
open Set Topology TopologicalSpace
variable {A : Type*} [CStarAlgebra A]


def stage (s : Set A) : ℕ → Set A
  | 0 => s ∪ Set.range (algebraMap ℂ A)
  | n+1 => stage s n ∪ (fun p : A×A=>p.1+p.2) '' (stage s n ×ˢ stage s n) ∪
      (fun p : A×A=>p.1*p.2) '' (stage s n ×ˢ stage s n) ∪ star '' stage s n
lemma stage_step (s : Set A) (n : ℕ) : stage s n ⊆ stage s (n+1) :=
  fun _ hx => Or.inl (Or.inl (Or.inl hx))
lemma stage_mono (s : Set A) : Monotone (stage s) := monotone_nat_of_le_succ (stage_step s)
def termAlgebra (s : Set A) : StarSubalgebra ℂ A where
  carrier := ⋃ n, stage s n
  zero_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨0,map_zero _⟩⟩
  one_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨1,map_one _⟩⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩))⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩)⟩
  algebraMap_mem' z := mem_iUnion.mpr ⟨0,Or.inr ⟨z,rfl⟩⟩
  star_mem' := by
    intro a ha
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨n+1,Or.inr ⟨a,hn,rfl⟩⟩
end KirchbergRordam.SeparableReduction

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MinTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
section
open scoped CStarAlgebra ComplexOrder

open scoped TensorProduct InnerProductSpace
open UniformSpace
namespace KirchbergRordam.Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]


@[simp] lemma map_coe (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    map T S (x : Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
  simp [map]

@[ext] lemma ext {T S : Hilbert H K →L[ℂ] Hilbert H K}
    (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq T.continuous S.continuous
  | ih x => exact h x

@[simp] lemma map_one : map (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  apply ext
  intro x
  simp [show (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H from rfl,
    show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl]

end KirchbergRordam.Spatial

end
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u


attribute [instance] RepresentationPair.normH RepresentationPair.innerH
  RepresentationPair.completeH RepresentationPair.normK RepresentationPair.innerK
  RepresentationPair.completeK


end KirchbergRordam.MinTensor
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
local instance instRingTensorProductComplex_solutions : Ring (A ⊗[ℂ] B) :=
  _root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)

end KirchbergRordam.MinTensor

namespace KirchbergRordam.MinTensor
open scoped TensorProduct CStarAlgebra
universe u
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]

variable {A B}
instance instStarModuleComplexRaw : StarModule ℂ (Raw A B) := TensorProduct.instStarModule

def rawEquiv : (A ⊗[ℂ] B) ≃⋆ₐ[ℂ] Raw A B :=
  StarAlgEquiv.refl ℂ (A ⊗[ℂ] B)


instance instNormedAlgebraComplexRaw : NormedAlgebra ℂ (Raw A B) where
  norm_smul_le z x := (map_smul_eq_mul seminorm z x).le
@[simp] lemma norm_raw (x : Raw A B) : ‖x‖ = seminorm x := rfl


end KirchbergRordam.MinTensor
namespace KirchbergRordam
namespace Spatial
open scoped TensorProduct
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Nontrivial H] [Nontrivial K]
instance instNontrivialHilbert : Nontrivial (Hilbert H K) :=
  (UniformSpace.Completion.coe_injective (H ⊗[ℂ] K)).nontrivial
end Spatial
end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_StandardPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.StandardPrimeMultiplicity


@[simp] lemma size_zero : size 0=2 := rfl
@[simp] lemma size_succ (n : ℕ) : size (n+1)=next (size n) := rfl
end KirchbergRordam.StandardPrimeMultiplicity
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KirchbergRordam

lemma nonzero_character_one {A : Type*} [CStarAlgebra A]
    (χ : A →⋆ₙₐ[ℂ] ℂ) (hχ : χ≠0) : χ 1=1 := by
  have hn : χ 1≠0 := by
    intro h
    apply hχ
    ext a
    change χ a=0
    calc
      χ a = χ (1*a) := by rw [one_mul]
      _ = χ 1*χ a := map_mul χ _ _
      _ = 0 := by rw [h,zero_mul]
  apply mul_left_cancel₀ hn
  rw [←map_mul χ,one_mul,mul_one]
def unitalCharacter {A : Type*} [CStarAlgebra A]
    (χ : A →⋆ₙₐ[ℂ] ℂ) (hχ : χ≠0) : A →⋆ₐ[ℂ] ℂ where
  toFun := χ
  map_zero' := map_zero χ
  map_one' := nonzero_character_one χ hχ
  map_add' := map_add χ
  map_mul' := map_mul χ
  commutes' z := by
    change χ (algebraMap ℂ A z)=z
    rw [Algebra.algebraMap_eq_smul_one,map_smul,nonzero_character_one χ hχ,
      smul_eq_mul,mul_one]
  map_star' := map_star χ


attribute [local instance 1100] StarCompletion.completionStar

end KirchbergRordam
end

end OAI
end


