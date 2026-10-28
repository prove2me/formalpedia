-- Prove2me | Definitions.Def_OAIQ2Rw001
-- name    : OAIQ2Rw001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T22:06:52.662529+00:00
-- url     : https://prove2.me/theorems/81e6a929-9f2e-4a3b-92ac-79cc0301dd7c
-- title:
--   Definitions bundle OAIQ2Rw001 of the split of OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContinuousCircleWeight.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 215 declarations of OpenAI's Lean: 88 definitions, 2 inductive types or structures, 9 instances and 116 theorems. The definitions and types are `OAI.CircleSampling.BlockPartition`, `OAI.CircleSampling.BlockPartition.equiv`, `OAI.CircleSampling.BlockPartition.number`, `OAI.CircleSampling.BlockPartition.position`, `OAI.CircleSampling.finiteAverage`, `OAI.CircleSampling.finiteGraphAverage`, `OAI.CircleSampling.fractionalCube`, `OAI.CircleSampling.hybridChoice`, `OAI.CircleSampling.instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert`, `OAI.CircleSampling.instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert_2`, `OAI.CircleSampling.phaseRange`, `OAI.CircleSampling.weightedGraph`, `OAI.CircleSampling.weightedMeasure`, `OAI.CircleTransport.Op`, `OAI.CircleTransport.fractionMap`, `OAI.CircleTransport.transportedRange`, `OAI.ContinuousCircleWeight.CircleFiberL2`, `OAI.ContinuousCircleWeight.CircleFiberOperator`, `OAI.ContinuousCircleWeight.FiberHilbert`, `OAI.ContinuousCircleWeight.FiberOperator`, `OAI.ContinuousCircleWeight.LocallyFiniteOff`, `OAI.ContinuousCircleWeight.RealBorel`, `OAI.ContinuousCircleWeight.RealBorel.add`, `OAI.ContinuousCircleWeight.RealBorel.const`, `OAI.ContinuousCircleWeight.RealBorel.mul`, `OAI.ContinuousCircleWeight.RealBorel.ofContinuous`, `OAI.ContinuousCircleWeight.RealBorel.shift`, `OAI.ContinuousCircleWeight.RegularHilbert`, `OAI.ContinuousCircleWeight.RegularOperator`, `OAI.ContinuousCircleWeight.Sampling.fejerFrequency`, `OAI.ContinuousCircleWeight.VectorL2`, `OAI.ContinuousCircleWeight.borelWeightedField`, `OAI.ContinuousCircleWeight.boundedPi`, `OAI.ContinuousCircleWeight.boundedPiField`, `OAI.ContinuousCircleWeight.cappedDiagonal`, `OAI.ContinuousCircleWeight.cappedPairRelation`, `OAI.ContinuousCircleWeight.cappedRatio`, `OAI.ContinuousCircleWeight.circleFiberBasis`, `OAI.ContinuousCircleWeight.circleJ`, `OAI.ContinuousCircleWeight.cocycleRatioDiagonal` and 50 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `RotationWeights_ActualDigits`, `RotationWeights_BorelTransport`, `RotationWeights_BorelWeights`, `RotationWeights_ContinuousWeight`, `RotationWeights_Covariance`, `RotationWeights_Decomposable`, `RotationWeights_Discrepancy`, `RotationWeights_FiberActions`, `RotationWeights_Fibers`, `RotationWeights_FieldExtraction`, `RotationWeights_FiniteSampling`, `RotationWeights_FourierSampling`, `RotationWeights_FunctionalCalculus`, `RotationWeights_GraphTransfer`, `RotationWeights_LaurentCoefficients`, `RotationWeights_NestedAngles`, `RotationWeights_OrbitBounds`, `RotationWeights_ProjectionFields`, `RotationWeights_ProjectionIdentity`, `RotationWeights_RationalGraphs`, `RotationWeights_Regular`, `RotationWeights_ReturnSamples`, `RotationWeights_SamplingStage`, `RotationWeights_TensorBasis`, `RotationWeights_Thresholds`, `RotationWeights_TracialAction`, `RotationWeights_Transport`, `RotationWeights_TrialBounds`, `RotationWeights_WeakSampling`.
--
--   **Imports.** It imports the published bundle `Def_ContinuousCircleWeight`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ2Rw002`; the statement `OAI.ContinuousCircleWeight.borel_weight_transport`; the proof of `OAI.ContinuousCircleWeight.borel_weight_transport`.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_ContinuousCircleWeight

section
-- module Solutions.OAIQ2_Rot.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
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
-- module Solutions.OAIQ2_Rot.RotationWeights_Regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
namespace ContinuousCircleWeight

def lpPermute {ι : Type uι} (e : Equiv.Perm ι) :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun f := ⟨fun i => f (e.symm i), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  invFun f := ⟨fun i => f (e i), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' f g := by ext i; rfl
  map_smul' c f := by ext i; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun i => ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

@[simp] theorem lpPermute_apply {ι : Type uι} (e : Equiv.Perm ι)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) : lpPermute e f i = f (e.symm i) := rfl

@[simp] theorem lpPermute_one {ι : Type uι} : lpPermute (1 : Equiv.Perm ι) = 1 := by
  ext f i
  rfl

@[simp] theorem lpPermute_mul {ι : Type uι} (e d : Equiv.Perm ι) :
    lpPermute (e * d) = lpPermute e * lpPermute d := by
  ext f i
  rfl

def lpPhase {ι : Type uι} (u : ι → unitary ℂ) :
    lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun f := ⟨fun i => (u i : ℂ) * f i, by
    apply memℓp_gen
    simpa only [norm_mul, CStarRing.norm_coe_unitary, one_mul] using
      (lp.memℓp f).summable (by norm_num)⟩
  invFun f := ⟨fun i => (↑(u i)⁻¹ : ℂ) * f i, by
    apply memℓp_gen
    simpa only [norm_mul, CStarRing.norm_coe_unitary, one_mul] using
      (lp.memℓp f).summable (by norm_num)⟩
  left_inv f := by ext i; simp [← mul_assoc, ← Submonoid.coe_mul]
  right_inv f := by ext i; simp [← mul_assoc, ← Submonoid.coe_mul]
  map_add' f g := by ext i; exact mul_add _ _ _
  map_smul' c f := by ext i; exact mul_left_comm _ _ _
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    change (∑' i, ‖(u i : ℂ) * f i‖ ^ _) = _
    simp only [norm_mul, CStarRing.norm_coe_unitary, one_mul]

@[simp] theorem lpPhase_apply {ι : Type uι} (u : ι → unitary ℂ)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) : lpPhase u f i = (u i : ℂ) * f i := rfl

def rotationScalar (θ : ℝ) : unitary ℂ :=
  ⟨Complex.exp (2 * Real.pi * θ * Complex.I), by
    have hn : ‖Complex.exp (2 * Real.pi * θ * Complex.I)‖ = 1 := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
        Complex.norm_exp_ofReal_mul_I (2 * Real.pi * θ)
    have hs := Complex.sq_norm (Complex.exp (2 * Real.pi * θ * Complex.I))
    rw [hn, one_pow] at hs
    rw [Unitary.mem_iff]
    constructor
    · rw [mul_comm]
      simp only [RCLike.star_def, Complex.mul_conj, ← hs, Complex.ofReal_one]
    · simp only [RCLike.star_def, Complex.mul_conj, ← hs, Complex.ofReal_one]⟩

abbrev RegularHilbert := lp (fun _ : ℤ × ℤ => ℂ) 2
abbrev RegularOperator := RegularHilbert →L[ℂ] RegularHilbert

def regularShift (m : ℤ) : RegularHilbert ≃ₗᵢ[ℂ] RegularHilbert :=
  lpPermute (Equiv.addLeft (m, 0))

@[simp] theorem regularShift_apply (m : ℤ) (f : RegularHilbert) (a b : ℤ) :
    regularShift m f (a,b) = f (a - m,b) := by
  change f (-m + a, 0 + b) = _
  apply congrArg f
  ext <;> dsimp <;> omega

def regularMagnetic (u : unitary ℂ) (n : ℤ) : RegularHilbert ≃ₗᵢ[ℂ] RegularHilbert :=
  lpPhase (fun i : ℤ × ℤ => u ^ (n * i.1)) * lpPermute (Equiv.addLeft (0,n))

@[simp] theorem regularMagnetic_apply (u : unitary ℂ) (n : ℤ)
    (f : RegularHilbert) (a b : ℤ) :
    regularMagnetic u n f (a,b) = (↑(u ^ (n * a)) : ℂ) * f (a,b-n) := by
  change _ * f (0 + a, -n + b) = _
  rw [zero_add, show -n + b = b - n by omega]

@[simp] theorem regularShift_zero : regularShift 0 = 1 := by
  ext f ⟨a,b⟩
  simp

@[simp] theorem regularShift_add (m n : ℤ) :
    regularShift (m+n) = regularShift m * regularShift n := by
  ext f ⟨a,b⟩
  change regularShift (m+n) f (a,b) = regularShift m (regularShift n f) (a,b)
  simp only [regularShift_apply]
  apply congrArg f
  ext <;> dsimp; omega

@[simp] theorem regularMagnetic_zero (u : unitary ℂ) : regularMagnetic u 0 = 1 := by
  ext f ⟨a,b⟩
  simp

@[simp] theorem regularMagnetic_add (u : unitary ℂ) (m n : ℤ) :
    regularMagnetic u (m+n) = regularMagnetic u m * regularMagnetic u n := by
  ext f ⟨a,b⟩
  change regularMagnetic u (m+n) f (a,b) = regularMagnetic u m (regularMagnetic u n f) (a,b)
  simp only [regularMagnetic_apply, add_mul, zpow_add, Submonoid.coe_mul, mul_assoc]
  rw [show b - (m+n) = b-m-n by omega]

def regularShiftHom : Multiplicative ℤ →* (RegularHilbert ≃ₗᵢ[ℂ] RegularHilbert) where
  toFun m := regularShift m.toAdd
  map_one' := regularShift_zero
  map_mul' m n := regularShift_add m.toAdd n.toAdd

def regularMagneticHom (u : unitary ℂ) :
    Multiplicative ℤ →* (RegularHilbert ≃ₗᵢ[ℂ] RegularHilbert) where
  toFun n := regularMagnetic u n.toAdd
  map_one' := regularMagnetic_zero u
  map_mul' m n := regularMagnetic_add u m.toAdd n.toAdd

@[simp] theorem regularShift_zpow (m : ℤ) : regularShift 1 ^ m = regularShift m := by
  symm
  simpa only [regularShiftHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_zpow,
    toAdd_ofAdd, zsmul_eq_mul, Int.cast_id, mul_one] using
    map_zpow regularShiftHom (Multiplicative.ofAdd 1) m

@[simp] theorem regularMagnetic_zpow (u : unitary ℂ) (n : ℤ) :
    regularMagnetic u 1 ^ n = regularMagnetic u n := by
  symm
  simpa only [regularMagneticHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_zpow,
    toAdd_ofAdd, zsmul_eq_mul, Int.cast_id, mul_one] using
    map_zpow (regularMagneticHom u) (Multiplicative.ofAdd 1) n

def regularU : unitary RegularOperator :=
  Unitary.linearIsometryEquiv.symm (regularShift 1)

def regularV (u : unitary ℂ) : unitary RegularOperator :=
  Unitary.linearIsometryEquiv.symm (regularMagnetic u 1)

@[simp] theorem regularU_zpow_apply (m : ℤ) (f : RegularHilbert) (a b : ℤ) :
    ((regularU ^ m : unitary RegularOperator) : RegularOperator) f (a,b) = f (a-m,b) := by
  rw [regularU, ← map_zpow, regularShift_zpow]
  exact regularShift_apply m f a b

@[simp] theorem regularV_zpow_apply (u : unitary ℂ) (n : ℤ)
    (f : RegularHilbert) (a b : ℤ) :
    ((regularV u ^ n : unitary RegularOperator) : RegularOperator) f (a,b) =
      (↑(u ^ (n*a)) : ℂ) * f (a,b-n) := by
  rw [regularV, ← map_zpow, regularMagnetic_zpow]
  exact regularMagnetic_apply u n f a b

@[simp] theorem regularU_apply (f : RegularHilbert) (a b : ℤ) :
    (regularU : RegularOperator) f (a,b) = f (a-1,b) := by
  exact regularShift_apply 1 f a b

@[simp] theorem regularV_apply (u : unitary ℂ) (f : RegularHilbert) (a b : ℤ) :
    (regularV u : RegularOperator) f (a,b) = (↑(u ^ a) : ℂ) * f (a,b-1) := by
  change regularMagnetic u 1 f (a,b) = _
  simpa only [one_mul] using regularMagnetic_apply u 1 f a b

def regularVacuum : RegularHilbert := lp.single 2 (0,0) 1

end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Fibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators

namespace ContinuousCircleWeight
abbrev FiberHilbert := lp (fun _ : ℤ => ℂ) 2
abbrev FiberOperator := FiberHilbert →L[ℂ] FiberHilbert

def lpDiagonal {ι : Type uι} (a : ι → ℂ) (B : ℝ≥0) (ha : ∀ i, ‖a i‖ ≤ B) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun i => a i * f i, by
        apply (((lp.memℓp f).norm).const_mul (B : ℝ)).mono
        intro i
        change ‖a i * f i‖ ≤ (B : ℝ) * ‖f i‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)⟩
      map_add' := by intro f g; ext i; exact mul_add _ _ _
      map_smul' := by intro c f; ext i; exact mul_left_comm _ _ _ }
    B (by
      intro f
      calc
        _ ≤ ‖(B : ℂ) • f‖ := lp.norm_mono (by norm_num) (by
          intro i
          change ‖a i * f i‖ ≤ ‖((B : ℝ) : ℂ) * f i‖
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          simpa using mul_le_mul_of_nonneg_right (ha i) (norm_nonneg (f i))
)
        _ = (B : ℝ) * ‖f‖ := by
          rw [norm_smul]
          simp)

@[simp] theorem lpDiagonal_apply {ι : Type uι} (a : ι → ℂ) (B : ℝ≥0)
    (ha : ∀ i, ‖a i‖ ≤ B) (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    lpDiagonal a B ha f i = a i * f i := rfl

def fiberShift (n : ℤ) : FiberHilbert ≃ₗᵢ[ℂ] FiberHilbert :=
  lpPermute (Equiv.addLeft n)

@[simp] theorem fiberShift_apply (n : ℤ) (f : FiberHilbert) (k : ℤ) :
    fiberShift n f k = f (k-n) := by
  change f (-n+k) = _
  apply congrArg f; omega

@[simp] theorem fiberShift_add (m n : ℤ) :
    fiberShift (m+n) = fiberShift m * fiberShift n := by
  ext f k
  change fiberShift (m+n) f k = fiberShift m (fiberShift n f) k
  simp only [fiberShift_apply]
  apply congrArg f; omega

def fiberWeightedShift (w : ℤ → ℂ) (hw : ∀ k, ‖w k‖ ≤ 1) : FiberOperator :=
  (fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap * lpDiagonal w 1 hw

@[simp] theorem fiberWeightedShift_apply (w : ℤ → ℂ) (hw : ∀ k, ‖w k‖ ≤ 1)
    (f : FiberHilbert) (k : ℤ) :
    fiberWeightedShift w hw f k = w (k-1) * f (k-1) := by
  change fiberShift 1 (lpDiagonal w 1 hw f) k = _
  rw [fiberShift_apply]
  rfl

def fiberCocycleShift (F : ℤ → ℝ) (hF : ∀ k, 0 < F k) (hmono : Antitone F) :
    FiberOperator :=
  fiberWeightedShift (fun k => ((F (k+1) / F k : ℝ) : ℂ)) (by
    intro k
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (hF _) (hF _))]
    exact (div_le_one (hF k)).mpr (hmono (by omega)))

@[simp] theorem fiberCocycleShift_apply (F : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hmono : Antitone F) (f : FiberHilbert) (k : ℤ) :
    fiberCocycleShift F hF hmono f k = (F k / F (k-1) : ℝ) * f (k-1) := by
  simp [fiberCocycleShift]

def cocycleRatioDiagonal (F G : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hG : ∀ k, 0 < G k) (horder : ∀ k, G k ≤ F k) : FiberOperator :=
  lpDiagonal (fun k => ((G k / F k : ℝ) : ℂ)) 1 (by
    intro k
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (hG _) (hF _))]
    exact (div_le_one (hF k)).mpr (horder k))

@[simp] theorem cocycleRatioDiagonal_apply (F G : ℤ → ℝ) (hF : ∀ k, 0 < F k)
    (hG : ∀ k, 0 < G k) (horder : ∀ k, G k ≤ F k) (v : FiberHilbert) (k : ℤ) :
    cocycleRatioDiagonal F G hF hG horder v k = (G k / F k : ℝ) * v k := rfl

end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TensorBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uE uι uκ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators

open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def pureL2 (f : Lp ℂ 2 μ) (u : E) : Lp E 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℂ u).compLp f

lemma pureL2_coe (f : Lp ℂ 2 μ) (u : E) :
    pureL2 μ f u =ᵐ[μ] fun x ↦ f x • u :=
  (ContinuousLinearMap.toSpanSingleton ℂ u).coeFn_compLp f

lemma pureL2_inner (f g : Lp ℂ 2 μ) (u v : E) :
    inner ℂ (pureL2 μ f u) (pureL2 μ g v) = inner ℂ f g * inner ℂ u v := by
  rw [L2.inner_def, L2.inner_def, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [pureL2_coe μ f u,pureL2_coe μ g v] with x h1 h2
  rw [h1,h2,inner_smul_left,inner_smul_right]
  simp only [RCLike.inner_apply, mul_assoc, mul_comm (g x)]

def coordinateL2 (u : E) : Lp E 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (innerSL ℂ u).compLpL 2 μ

lemma coordinateL2_coe (u : E) (g : Lp E 2 μ) :
    coordinateL2 μ u g =ᵐ[μ] fun x ↦ inner ℂ u (g x) :=
  (innerSL ℂ u).coeFn_compLpL g

lemma pureL2_inner_coordinate (f : Lp ℂ 2 μ) (u : E) (g : Lp E 2 μ) :
    inner ℂ (pureL2 μ f u) g = inner ℂ f (coordinateL2 μ u g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pureL2_coe μ f u,coordinateL2_coe μ u g] with x h1 h2
  rw [h1,h2,inner_smul_left]
  simp only [RCLike.inner_apply,mul_comm]

variable {ι : Type uι} {κ : Type uκ}

lemma hilbertBasis_ext (b : HilbertBasis ι ℂ E) {u v : E}
    (h : ∀ i, inner ℂ (b i) u = inner ℂ (b i) v) : u=v := by
  apply b.repr.injective
  ext i
  simpa only [b.repr_apply_apply] using h i

lemma orthonormal_pureL2 (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ (Lp ℂ 2 μ)) :
    Orthonormal ℂ (fun z : ι × κ ↦ pureL2 μ (c z.2) (b z.1)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [pureL2_inner,orthonormal_iff_ite.mp c.orthonormal,
    orthonormal_iff_ite.mp b.orthonormal]
  by_cases h1 : i.1=j.1 <;> by_cases h2 : i.2=j.2 <;> simp [h1,h2,Prod.ext_iff]

lemma pureL2_orthogonal_eq_bot [Countable ι] (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ (Lp ℂ 2 μ)) :
    (span ℂ (range (fun z : ι × κ ↦ pureL2 μ (c z.2) (b z.1))))ᗮ = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  have hcoord (a : ι) : coordinateL2 μ (b a) f = 0 := by
    apply hilbertBasis_ext c
    intro n
    rw [inner_zero_right,← pureL2_inner_coordinate]
    exact (mem_orthogonal _ _).mp hf _ (subset_span ⟨(a,n),rfl⟩)
  have hh : ∀ᵐ x ∂μ, ∀ a : ι, inner ℂ (b a) (f x) = 0 := by
    apply ae_all_iff.mpr
    intro a
    filter_upwards [coordinateL2_coe μ (b a) f,Lp.coeFn_zero ℂ 2 μ] with x h1 h2
    rw [hcoord a,h2] at h1
    exact h1.symm
  have he : f=0 := by
    apply Lp.ext
    filter_upwards [hh,Lp.coeFn_zero E 2 μ] with x hx hz
    rw [hz]
    apply hilbertBasis_ext b
    intro a
    simpa only [Pi.zero_apply,inner_zero_right] using hx a
  simp only [he,zero_mem]

variable [CompleteSpace E]

def tensorL2Basis [Countable ι] (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ (Lp ℂ 2 μ)) : HilbertBasis (ι×κ) ℂ (Lp E 2 μ) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_pureL2 μ b c) (pureL2_orthogonal_eq_bot μ b c)

@[simp] lemma tensorL2Basis_apply [Countable ι] (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ (Lp ℂ 2 μ)) (z : ι×κ) :
    tensorL2Basis μ b c z = pureL2 μ (c z.2) (b z.1) := by
  simp only [tensorL2Basis,HilbertBasis.coe_mkOfOrthogonalEqBot]
end

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma aestronglyMeasurable_field_simple (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ) (s : SimpleFunc X E) :
    AEStronglyMeasurable (fun x ↦ T x (s x)) μ := by
  classical
  have he : (fun x ↦ T x (s x)) =
      ∑ a ∈ s.range, (s ⁻¹' {a}).indicator (fun x ↦ T x a) := by
    funext x
    simp [Set.indicator, s.mem_range_self]
  rw [he]
  exact s.range.aestronglyMeasurable_sum fun a _ ↦ (hT a).indicator (s.measurableSet_fiber a)

lemma aestronglyMeasurable_field_apply (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (f : X → E) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x ↦ T x (f x)) μ := by
  let f₀ := hf.mk f
  have hf₀ : StronglyMeasurable f₀ := hf.stronglyMeasurable_mk
  have hm : AEStronglyMeasurable (fun x ↦ T x (f₀ x)) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ aestronglyMeasurable_field_simple μ T hT (hf₀.approx n))
    exact Eventually.of_forall fun x ↦ ((T x).continuous.tendsto (f₀ x)).comp
      (hf₀.tendsto_approx x)
  apply hm.congr
  exact hf.ae_eq_mk.symm.mono fun x hx ↦ congrArg (T x) hx

lemma bounded_field_memL2 (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (f : Lp E 2 μ) :
    MemLp (fun x ↦ T x (f x)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := C)
    (aestronglyMeasurable_field_apply μ T hT f (Lp.aestronglyMeasurable f))
  filter_upwards [hC] with x hx
  exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def fieldMulL2 (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (bounded_field_memL2 μ T hT C hC f).toLp (fun x ↦ T x (f x))
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(bounded_field_memL2 μ T hT C hC (f+g)).coeFn_toLp,
          (bounded_field_memL2 μ T hT C hC f).coeFn_toLp,
          (bounded_field_memL2 μ T hT C hC g).coeFn_toLp,
          Lp.coeFn_add f g, Lp.coeFn_add ((bounded_field_memL2 μ T hT C hC f).toLp _)
            ((bounded_field_memL2 μ T hT C hC g).toLp _)] with x h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at h4 h5
        rw [h1,h5,h2,h3,h4,map_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(bounded_field_memL2 μ T hT C hC (c•f)).coeFn_toLp,
          (bounded_field_memL2 μ T hT C hC f).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((bounded_field_memL2 μ T hT C hC f).toLp _)] with x h1 h2 h3 h4
        simp only [Pi.smul_apply] at h3 h4
        simp only [RingHom.id_apply]
        rw [h1,h4,h2,h3,map_smul] }
    C (by
      intro f
      change ‖(bounded_field_memL2 μ T hT C hC f).toLp _‖ ≤ C*‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(bounded_field_memL2 μ T hT C hC f).coeFn_toLp,hC] with x hx hc
      rw [hx]
      exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _)))

lemma fieldMulL2_coe (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (f : Lp E 2 μ) :
    fieldMulL2 μ T hT C hC f =ᵐ[μ] fun x ↦ T x (f x) :=
  (bounded_field_memL2 μ T hT C hC f).coeFn_toLp


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FiberActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section
lemma continuous_bounded_lp_field {X : Type uX} [TopologicalSpace X]
    (A : X → FiberOperator) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖A x‖ ≤ C)
    (hc : ∀ k : ℤ, Continuous (fun x ↦ A x (lp.single 2 k 1)))
    (u : FiberHilbert) : Continuous (fun x ↦ A x u) := by
  classical
  let v : Finset ℤ → FiberHilbert := fun s ↦ ∑ k ∈ s, lp.single 2 k (u k)
  have hv : Tendsto v atTop (𝓝 u) := lp.hasSum_single (by norm_num) u
  have hunif : TendstoUniformly (fun s x ↦ A x (v s)) (fun x ↦ A x u) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hε' : 0 < ε/(C+1) := div_pos hε (by linarith)
    filter_upwards [Metric.tendsto_nhds.mp hv _ hε'] with s hs x
    rw [dist_eq_norm, ← map_sub]
    have ht := (A x).le_opNorm (u-v s)
    have hn : ‖u-v s‖ < ε/(C+1) := by simpa [dist_eq_norm, norm_sub_rev] using hs
    calc
      _ ≤ C * ‖u-v s‖ := ht.trans (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))
      _ ≤ (C+1) * ‖u-v s‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C+1) * (ε/(C+1)) := mul_lt_mul_of_pos_left hn (by linarith)
      _ = ε := mul_div_cancel₀ _ (by linarith)
  apply hunif.continuous
  apply Filter.Eventually.frequently
  exact Filter.Eventually.of_forall fun s ↦ by
    simp only [v, map_sum]
    apply continuous_finsetSum
    intro k _
    have he : lp.single (E := fun _ : ℤ ↦ ℂ) 2 k (u k) = (u k) • lp.single 2 k (1 : ℂ) := by
      simpa using (lp.single_smul (E := fun _ : ℤ ↦ ℂ) 2 k (u k) (1 : ℂ))
    simp only [he, map_smul]
    exact (hc k).const_smul (u k)

lemma lpDiagonal_norm_le {a : ℤ → ℂ} (B : ℝ≥0) (ha : ∀ k, ‖a k‖ ≤ B) :
    ‖lpDiagonal a B ha‖ ≤ B := by
  refine (lpDiagonal a B ha).opNorm_le_bound B.coe_nonneg ?_
  intro u
  calc
    _ ≤ ‖(B : ℂ) • u‖ := lp.norm_mono (by norm_num) (by
      intro k
      simp only [lpDiagonal_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg B.coe_nonneg]
      exact mul_le_mul_of_nonneg_right (ha k) (norm_nonneg _))
    _ = (B : ℝ) * ‖u‖ := by rw [norm_smul]; simp

abbrev CircleFiberL2 := Lp FiberHilbert 2 (AddCircle.haarAddCircle (T := (1:ℝ)))
abbrev CircleFiberOperator := CircleFiberL2 →L[ℂ] CircleFiberL2
def fiberBasis : HilbertBasis ℤ ℂ FiberHilbert :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ FiberHilbert)
@[simp] lemma fiberBasis_apply (a : ℤ) : fiberBasis a = lp.single 2 a 1 := by
  simpa [fiberBasis] using (fiberBasis.repr_self a)

def circleFiberBasis : HilbertBasis (ℤ×ℤ) ℂ CircleFiberL2 :=
  tensorL2Basis AddCircle.haarAddCircle fiberBasis fourierBasis

def continuousPiField (θ : CircleX) (g : C(CircleX,ℂ)) (x : CircleX) : FiberOperator :=
  lpDiagonal (fun k ↦ g (x+k•θ)) ⟨‖g‖,norm_nonneg g⟩
    (fun k ↦ ContinuousMap.norm_coe_le_norm g (x+k•θ))

@[simp] lemma continuousPiField_apply (θ : CircleX) (g : C(CircleX,ℂ))
    (x : CircleX) (v : FiberHilbert) (k : ℤ) :
    continuousPiField θ g x v k = g (x+k•θ)*v k := rfl

lemma continuousPiField_bound (θ : CircleX) (g : C(CircleX,ℂ)) (x : CircleX) :
    ‖continuousPiField θ g x‖ ≤ ‖g‖ := by
  exact lpDiagonal_norm_le ⟨‖g‖,norm_nonneg g⟩ _

lemma continuousPiField_continuous (θ : CircleX) (g : C(CircleX,ℂ)) (v : FiberHilbert) :
    Continuous (fun x ↦ continuousPiField θ g x v) := by
  apply continuous_bounded_lp_field _ (norm_nonneg g) (continuousPiField_bound θ g) _ v
  intro k
  have he : (fun x ↦ continuousPiField θ g x (lp.single 2 k 1)) =
      (fun x ↦ g (x+k•θ) • lp.single 2 k 1) := by
    funext x
    ext j
    simp only [continuousPiField_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    by_cases h : j=k
    · subst j; rfl
    · simp [lp.single_apply,Pi.single_eq_of_ne h]
  rw [he]
  exact (g.continuous.comp (continuous_id.add continuous_const)).smul continuous_const

def continuousPi (θ : CircleX) (g : C(CircleX,ℂ)) : CircleFiberOperator :=
  fieldMulL2 AddCircle.haarAddCircle (continuousPiField θ g)
    (fun v ↦ (continuousPiField_continuous θ g v).aestronglyMeasurable)
    ‖g‖ (Eventually.of_forall (continuousPiField_bound θ g))

lemma continuousPi_coe (θ : CircleX) (g : C(CircleX,ℂ)) (f : CircleFiberL2) :
    continuousPi θ g f =ᵐ[AddCircle.haarAddCircle] fun x ↦ continuousPiField θ g x (f x) :=
  fieldMulL2_coe _ _ _ _ _ _

lemma continuousPi_add (θ : CircleX) (g h : C(CircleX,ℂ)) :
    continuousPi θ (g+h) = continuousPi θ g + continuousPi θ h := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ (g+h) f,continuousPi_coe θ g f,
    continuousPi_coe θ h f,Lp.coeFn_add (continuousPi θ g f) (continuousPi θ h f)] with x h1 h2 h3 h4
  change (continuousPi θ (g+h) f) x = ((continuousPi θ g f)+(continuousPi θ h f)) x
  rw [h1,h4]
  simp only [Pi.add_apply,h2,h3]
  ext k
  simp only [continuousPiField_apply,ContinuousMap.add_apply,lp.coeFn_add,Pi.add_apply,add_mul]

lemma continuousPi_mul (θ : CircleX) (g h : C(CircleX,ℂ)) :
    continuousPi θ (g*h) = continuousPi θ g * continuousPi θ h := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ (g*h) f,continuousPi_coe θ h f,
    continuousPi_coe θ g (continuousPi θ h f)] with x h1 h2 h3
  change (continuousPi θ (g*h) f) x = (continuousPi θ g (continuousPi θ h f)) x
  rw [h1,h3,h2]
  ext k
  simp only [continuousPiField_apply,ContinuousMap.mul_apply,mul_assoc]

lemma continuousPi_one (θ : CircleX) : continuousPi θ 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ 1 f] with x hx
  rw [hx]
  ext k
  simp only [continuousPiField_apply,ContinuousMap.one_apply,one_mul]
  rfl

lemma continuousPi_zero (θ : CircleX) : continuousPi θ 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ 0 f,Lp.coeFn_zero FiberHilbert 2 AddCircle.haarAddCircle] with x hx hz
  change (continuousPi θ 0 f) x = (0 : CircleFiberL2) x
  rw [hx,hz]
  ext k
  simp only [continuousPiField_apply,ContinuousMap.zero_apply,zero_mul,Pi.zero_apply,lp.coeFn_zero]

lemma continuousPi_smul (θ : CircleX) (g : C(CircleX,ℂ)) (c : ℂ) :
    continuousPi θ (c•g) = c•continuousPi θ g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ (c•g) f,continuousPi_coe θ g f,
    Lp.coeFn_smul c (continuousPi θ g f)] with x h1 h2 h3
  change (continuousPi θ (c•g) f) x = (c•continuousPi θ g f) x
  rw [h1,h3]
  simp only [Pi.smul_apply,h2]
  ext k
  simp only [continuousPiField_apply,ContinuousMap.smul_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,mul_assoc]

lemma continuousPiField_inner_star (θ : CircleX) (g : C(CircleX,ℂ)) (x : CircleX)
    (u v : FiberHilbert) :
    inner ℂ (continuousPiField θ (star g) x u) v = inner ℂ u (continuousPiField θ g x v) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp only [continuousPiField_apply,RCLike.inner_apply,ContinuousMap.star_apply,map_mul,
    starRingEnd_apply,star_star]
  ring

lemma continuousPi_star (θ : CircleX) (g : C(CircleX,ℂ)) :
    continuousPi θ (star g) = star (continuousPi θ g) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro h
  change inner ℂ (continuousPi θ (star g) f) h =
    inner ℂ ((continuousPi θ g).adjoint f) h
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousPi_coe θ (star g) f,continuousPi_coe θ g h] with x h1 h2
  rw [h1,h2]
  exact continuousPiField_inner_star θ g x (f x) (h x)

def continuousPiHom (θ : CircleX) : C(CircleX,ℂ) →⋆ₐ[ℂ] CircleFiberOperator where
  toFun := continuousPi θ
  map_zero' := continuousPi_zero θ
  map_one' := continuousPi_one θ
  map_add' := continuousPi_add θ
  map_mul' := continuousPi_mul θ
  commutes' := by
    intro c
    simp only [Algebra.algebraMap_eq_smul_one,continuousPi_smul,continuousPi_one]
  map_star' := continuousPi_star θ

end


def fiberShiftL2 (n : ℤ) : CircleFiberOperator :=
  (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 AddCircle.haarAddCircle



end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FunctionalCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uι uE uA

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section
open Set Filter
open scoped Topology

lemma lp_diagonal_stronglyMeasurable {X : Type uX} [MeasurableSpace X]
    (d : X → ℤ → ℂ) (C : ℝ≥0) (hd : ∀ x k, ‖d x k‖≤C)
    (hm : ∀ k, Measurable (fun x => d x k)) (u : FiberHilbert) :
    StronglyMeasurable (fun x => lpDiagonal (d x) C (hd x) u) := by
  let v : Finset ℤ → FiberHilbert := fun s => ∑ k∈s,lp.single 2 k (u k)
  have hv : Tendsto v atTop (𝓝 u) := lp.hasSum_single (by norm_num) u
  apply stronglyMeasurable_of_tendsto atTop (f:=fun s x => lpDiagonal (d x) C (hd x) (v s))
  · intro s
    have he : (fun x => lpDiagonal (d x) C (hd x) (v s)) =
        (fun x => ∑ k∈s,(d x k*u k) • lp.single 2 k 1) := by
      funext x
      simp only [v,map_sum]
      apply Finset.sum_congr rfl
      intro k _
      ext j
      by_cases hj : j=k
      · subst j; simp [lpDiagonal,lp.single_apply]
      · simp [lpDiagonal,lp.single_apply,hj]
    rw [he]
    convert Finset.stronglyMeasurable_sum s (fun k _ => ((hm k).mul_const (u k)).stronglyMeasurable.smul_const (lp.single 2 k 1 : FiberHilbert)) using 1
    ext x; simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact ((lpDiagonal (d x) C (hd x)).continuous.tendsto u).comp hv

def boundedPiField (θ : CircleX) (g : CircleX → ℂ) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C)
    (x : CircleX) : FiberOperator := lpDiagonal (fun k => g (x+k•θ)) C (fun _k => hg _)
@[simp] lemma boundedPiField_apply (θ : CircleX) (g : CircleX → ℂ) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C)
    (x : CircleX) (u : FiberHilbert) (k : ℤ) : boundedPiField θ g C hg x u k=g (x+k•θ)*u k := rfl
lemma boundedPiField_bound (θ : CircleX) (g : CircleX → ℂ) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) (x : CircleX) :
    ‖boundedPiField θ g C hg x‖ ≤ C := lpDiagonal_norm_le _ _
lemma boundedPiField_measurable (θ : CircleX) (g : CircleX → ℂ) (hm : Measurable g)
    (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) (u : FiberHilbert) :
    StronglyMeasurable (fun x => boundedPiField θ g C hg x u) :=
  lp_diagonal_stronglyMeasurable _ C (fun _x _k => hg _) (fun _k => hm.comp (measurable_id.add_const _)) u

def boundedPi (θ : CircleX) (g : CircleX → ℂ) (hm : Measurable g)
    (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) : CircleFiberOperator :=
  fieldMulL2 AddCircle.haarAddCircle (boundedPiField θ g C hg)
    (fun u => (boundedPiField_measurable θ g hm C hg u).aestronglyMeasurable)
    C (Eventually.of_forall (boundedPiField_bound θ g C hg))
lemma boundedPi_coe (θ : CircleX) (g : CircleX → ℂ) (hm : Measurable g)
    (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) (u : CircleFiberL2) :
    boundedPi θ g hm C hg u =ᵐ[AddCircle.haarAddCircle] fun x => boundedPiField θ g C hg x (u x) :=
  fieldMulL2_coe _ _ _ _ _ _
end

section
open Set Metric

def complexCircleMap (f : C(CircleX,ℝ)) : C(CircleX,ℂ) :=
  ⟨fun x ↦ (f x : ℂ),Complex.continuous_ofReal.comp f.continuous⟩

end

open Set Filter
open scoped Topology

lemma boundedPi_congr (θ : CircleX) (g h : CircleX → ℂ) (hgm : Measurable g) (hhm : Measurable h)
    (C D : ℝ≥0) (hg : ∀ x,‖g x‖≤C) (hh : ∀ x,‖h x‖≤D)
    (he : g=ᵐ[AddCircle.haarAddCircle] h) : boundedPi θ g hgm C hg=boundedPi θ h hhm D hh := by
  have he' : ∀ᵐ x ∂AddCircle.haarAddCircle,∀ k : ℤ,g (x+k•θ)=h (x+k•θ) := by
    rw [ae_all_iff]
    intro k
    exact (measurePreserving_add_right AddCircle.haarAddCircle (k•θ)).quasiMeasurePreserving.ae
      (p:=fun x : CircleX => g x=h x) he
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [boundedPi_coe θ g hgm C hg u,boundedPi_coe θ h hhm D hh u,he'] with x h1 h2 hx
  rw [h1,h2]
  ext k
  simp only [boundedPiField_apply,hx]


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_BorelWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

namespace ContinuousCircleWeight

section
open Set Filter
open scoped Topology

structure RealBorel where
  f : CircleX → ℝ
  measurable : Measurable f
  bound : ℝ≥0
  norm_le : ∀ x,‖f x‖≤bound
instance instCoeFunRealBorelForallCircleXReal : CoeFun RealBorel (fun _ => CircleX → ℝ) := ⟨RealBorel.f⟩
namespace RealBorel
def const (c : ℝ) : RealBorel := ⟨fun _ => c,measurable_const,⟨|c|,abs_nonneg _⟩,by intro x; exact le_refl _⟩
def add (g h : RealBorel) : RealBorel :=
  ⟨fun x => g x+h x,g.measurable.add h.measurable,g.bound+h.bound,
    fun x => (norm_add_le _ _).trans (add_le_add (g.norm_le x) (h.norm_le x))⟩
def mul (g h : RealBorel) : RealBorel :=
  ⟨fun x => g x*h x,g.measurable.mul h.measurable,g.bound*h.bound,
    fun x => (norm_mul _ _).le.trans (mul_le_mul (g.norm_le x) (h.norm_le x) (norm_nonneg _) g.bound.property)⟩
def shift (θ : CircleX) (g : RealBorel) : RealBorel :=
  ⟨fun x => g (x+θ),g.measurable.comp (measurable_id.add_const θ),g.bound,fun x => g.norm_le (x+θ)⟩
def ofContinuous (g : C(CircleX,ℝ)) : RealBorel :=
  ⟨g,g.continuous.measurable,⟨‖g‖,norm_nonneg _⟩,g.norm_coe_le_norm⟩
end RealBorel

def realPi (θ : CircleX) (g : RealBorel) : CircleFiberOperator :=
  boundedPi θ (fun x => (g x:ℂ)) (Complex.measurable_ofReal.comp g.measurable) g.bound
    (fun x => by simpa using g.norm_le x)
def realPiField (θ : CircleX) (g : RealBorel) (x : CircleX) : FiberOperator :=
  boundedPiField θ (fun x => (g x:ℂ)) g.bound (fun x => by simpa using g.norm_le x) x
@[simp] lemma realPiField_apply (θ : CircleX) (g : RealBorel) (x : CircleX) (u : FiberHilbert) (k : ℤ) :
    realPiField θ g x u k=(g (x+k•θ):ℂ)*u k := rfl
lemma realPi_coe (θ : CircleX) (g : RealBorel) (u : CircleFiberL2) :
    realPi θ g u =ᵐ[AddCircle.haarAddCircle] fun x => realPiField θ g x (u x) :=
  boundedPi_coe _ _ _ _ _ _
lemma realPi_congr (θ : CircleX) (g h : RealBorel) (he : (fun x => g x)=ᵐ[AddCircle.haarAddCircle] (fun x => h x)) :
    realPi θ g=realPi θ h :=
  boundedPi_congr θ _ _ _ _ _ _ _ _ (he.mono (fun _x hx => congrArg Complex.ofReal hx))
lemma realPi_mul (θ : CircleX) (g h : RealBorel) : realPi θ (g.mul h)=realPi θ g*realPi θ h := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [realPi_coe θ (g.mul h) u,realPi_coe θ h u,realPi_coe θ g (realPi θ h u)] with x h1 h2 h3
  change (realPi θ (g.mul h) u) x=(realPi θ g (realPi θ h u)) x
  rw [h1,h3,h2]
  ext k
  simp only [realPiField_apply,RealBorel.mul,Complex.ofReal_mul,mul_assoc]
lemma realPiField_symmetric (θ : CircleX) (g : RealBorel) (x : CircleX)
    (u v : FiberHilbert) : inner ℂ (realPiField θ g x u) v=inner ℂ u (realPiField θ g x v) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp only [realPiField_apply,RCLike.inner_apply,map_mul,Complex.conj_ofReal]
  ring
lemma realPi_selfAdjoint (θ : CircleX) (g : RealBorel) : IsSelfAdjoint (realPi θ g) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realPi_coe θ g u,realPi_coe θ g v] with x hu hv
  change inner ℂ ((realPi θ g u) x) (v x)=inner ℂ (u x) ((realPi θ g v) x)
  rw [hu,hv]
  exact realPiField_symmetric θ g x (u x) (v x)
end

open Set Filter
open scoped Topology

def realCutoff (g : RealBorel) (n : ℕ) : RealBorel where
  f x := if (1:ℝ)/(n+1) ≤ g x then 1 else 0
  measurable := Measurable.ite (measurableSet_le measurable_const g.measurable) measurable_const measurable_const
  bound := 1
  norm_le x := by split_ifs <;> norm_num

def realCutoffInv (g : RealBorel) (n : ℕ) : RealBorel where
  f x := if (1:ℝ)/(n+1) ≤ g x then (g x)⁻¹ else 0
  measurable := Measurable.ite (measurableSet_le measurable_const g.measurable) g.measurable.inv measurable_const
  bound := n+1
  norm_le x := by
    split_ifs with h
    · have hn : (0:ℝ)<n+1 := by positivity
      have hg : 0<g x := (one_div_pos.mpr hn).trans_le h
      rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hg)]
      have hh := one_div_le_one_div_of_le (one_div_pos.mpr hn) h
      simpa using hh
    · simp only [norm_zero,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]; positivity

lemma realCutoff_proj (θ : CircleX) (g : RealBorel) (n : ℕ) :
    IsStarProjection (realPi θ (realCutoff g n)) := by
  refine ⟨?_,realPi_selfAdjoint θ _⟩
  change realPi θ _*realPi θ _=realPi θ _
  rw [←realPi_mul]
  apply realPi_congr
  exact Eventually.of_forall (fun x => by change (if _ then (1:ℝ) else 0)*(if _ then 1 else 0)=(if _ then 1 else 0); split_ifs <;> norm_num)

def realCutoffRange (θ : CircleX) (g : RealBorel) (n : ℕ) : Submodule ℂ CircleFiberL2 :=
  (realPi θ (realCutoff g n)).range
instance realCutoffRange_complete (θ : CircleX) (g : RealBorel) (n : ℕ) : CompleteSpace (realCutoffRange θ g n) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range (realCutoff_proj θ g n).isIdempotentElem).completeSpace_coe
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TracialAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uA

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section

def rightTranslate (u : unitary ℂ) (m n : ℤ) : RegularHilbert ≃ₗᵢ[ℂ] RegularHilbert :=
  lpPhase (fun i : ℤ × ℤ ↦ u ^ (m*(i.2-n))) * lpPermute (Equiv.addLeft (m,n))

def rightOperator (u : unitary ℂ) (m n : ℤ) : RegularOperator :=
  (rightTranslate u m n).toLinearIsometry.toContinuousLinearMap

def regularAlgebra (u : unitary ℂ) : Set RegularOperator :=
  Set.centralizer (Set.centralizer ({(regularU : RegularOperator),(regularV u : RegularOperator)} : Set RegularOperator))

end

open Set

def fiberConjugacy : RegularOperator ≃⋆ₐ[ℂ] CircleFiberOperator :=
  circleFiberBasis.repr.symm.conjStarAlgEquiv

def regularCommutant (θ : ℝ) : StarSubalgebra ℂ RegularOperator :=
  StarSubalgebra.centralizer ℂ ({(regularU:RegularOperator),(regularV (rotationScalar θ):RegularOperator)} : Set RegularOperator)
def fiberCommutant (θ : ℝ) : StarSubalgebra ℂ CircleFiberOperator :=
  (regularCommutant θ).map fiberConjugacy.toStarAlgHom

def fiberVacuum : CircleFiberL2 := circleFiberBasis.repr.symm regularVacuum


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FieldExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
section
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
abbrev VectorL2 := Lp E 2 μ

def indicatorV2 (s : Set X) (hs : MeasurableSet s) : VectorL2 (E := E) μ →L[ℂ] VectorL2 (E := E) μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).indicator hs).toLp (s.indicator f)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [((Lp.memLp (f+g)).indicator hs).coeFn_toLp,
          ((Lp.memLp f).indicator hs).coeFn_toLp, ((Lp.memLp g).indicator hs).coeFn_toLp,
          Lp.coeFn_add f g, Lp.coeFn_add (((Lp.memLp f).indicator hs).toLp _)
            (((Lp.memLp g).indicator hs).toLp _)] with x h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at h4 h5
        rw [h1,h5,h2,h3]
        by_cases hx : x∈s
        · simp only [indicator_of_mem hx, h4]
        · simp only [indicator_of_notMem hx, add_zero]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [((Lp.memLp (c•f)).indicator hs).coeFn_toLp,
          ((Lp.memLp f).indicator hs).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (((Lp.memLp f).indicator hs).toLp _)] with x h1 h2 h3 h4
        simp only [Pi.smul_apply] at h3 h4
        simp only [RingHom.id_apply]
        rw [h1,h4,h2]
        by_cases hx : x∈s
        · simp only [indicator_of_mem hx, h3]
        · simp only [indicator_of_notMem hx, smul_zero] }
    1 (by
      intro f
      change ‖((Lp.memLp f).indicator hs).toLp (s.indicator f)‖ ≤ 1*‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [((Lp.memLp f).indicator hs).coeFn_toLp] with x hx
      rw [hx, one_mul]
      by_cases hxs : x∈s
      · simp only [indicator_of_mem hxs, le_refl]
      · simp only [indicator_of_notMem hxs, norm_zero, norm_nonneg])

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
local instance rationalNormedSpace : NormedSpace ℚ E := NormedSpace.restrictScalars ℚ ℂ E
local instance rationalTower : IsScalarTower ℚ ℂ E := IsScalarTower.restrictScalars ℚ ℂ E

def complexOfRat (T : E →L[ℚ] E) (hI : ∀ v, T (Complex.I • v) = Complex.I • T v) : E →L[ℂ] E where
  toFun := T
  map_add' := T.map_add
  map_smul' := by
    intro c v
    have hr : ∀ a : ℝ, T ((a : ℂ) • v) = (a : ℂ) • T v := by
      intro a
      refine (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).induction_on a ?_ ?_
      · exact isClosed_eq (by fun_prop) (by fun_prop)
      · intro q
        simp only [Complex.ofReal_ratCast, Rat.cast_smul_eq_qsmul ℂ q]
        exact T.map_smul q v
    have hrI : T ((c.im : ℂ) • (Complex.I • v)) = (c.im : ℂ) • T (Complex.I • v) := by
      refine (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).induction_on c.im ?_ ?_
      · exact isClosed_eq (by fun_prop) (by fun_prop)
      · intro q
        simp only [Complex.ofReal_ratCast, Rat.cast_smul_eq_qsmul ℂ q]
        exact T.map_smul q (Complex.I • v)
    rw [← Complex.re_add_im c, add_smul, map_add, mul_smul, hr, hrI, hI]
    simp only [RingHom.id_apply, add_smul, mul_smul]
  cont := T.continuous

def rationalCore (v : ℕ → E) : Submodule ℚ E :=
  Submodule.span ℚ (range v ∪ range (fun n ↦ Complex.I • v n))

instance rationalCore_countable (v : ℕ → E) : Countable (rationalCore v) := by
  unfold rationalCore
  have heq : range v ∪ range (fun n ↦ Complex.I • v n) =
      range (Sum.elim v (fun n ↦ Complex.I • v n)) := by
    ext x
    simp
  rw [heq]
  infer_instance



end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Decomposable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def shiftedL2 (σ : X → X) (hσ : MeasurePreserving σ μ μ) (S : E →L[ℂ] E) :
    Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (S.compLpL 2 μ).comp (Lp.compMeasurePreservingₗᵢ ℂ σ hσ).toContinuousLinearMap



end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uA uB uE uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section

def circleJ (θ : CircleX) (n : ℤ) : CircleFiberOperator :=
  shiftedL2 AddCircle.haarAddCircle (fun x ↦ x+n•θ)
    (measurePreserving_add_right AddCircle.haarAddCircle (n•θ))
    (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap

end

open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace

open MeasureTheory Filter Set


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ProjectionFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set

open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexInnerProductSpace
local instance instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert : MeasurableSpace FiberHilbert := borel FiberHilbert

def borelWeightedField (θ : CircleX) (g : RealBorel) (x : CircleX) : FiberOperator :=
  (fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap * realPiField θ g x


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleTransport

universe uH

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
section
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Op := H →L[ℂ] H

def transportedRange (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H) : Submodule ℂ H :=
  ((P.comap D.subtype).map A).topologicalClosure

instance instCompleteSpaceSubtypeMemSubmoduleComplexTransportedRange (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H) : CompleteSpace (transportedRange D P A) :=
  inferInstanceAs (CompleteSpace ((P.comap D.subtype).map A).topologicalClosure)

end
open ContinuousLinearMap
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fractionMap (b c : Op (H:=H)) (hb : Function.Injective b) :
    LinearMap.range b.toLinearMap →ₗ[ℂ] H :=
  c.toLinearMap.comp (LinearEquiv.ofInjective b.toLinearMap hb).symm.toLinearMap

omit [CompleteSpace H] in
lemma fraction_domain_map (b T L : Op (H:=H)) (h : T*b=b*L) :
    ∀ x∈LinearMap.range b.toLinearMap,T x∈LinearMap.range b.toLinearMap := by
  rintro x ⟨y,rfl⟩
  exact ⟨L y,(DFunLike.congr_fun h y).symm⟩


end CircleTransport

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_BorelTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace

open Filter Set
open scoped Topology

def fractionB (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x) : RealBorel where
  f x := (1+a x)⁻¹
  measurable := (measurable_const.add ha).inv
  bound := 1
  norm_le x := by
    have h : (1:ℝ)≤1+a x := by linarith [hp x]
    simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by linarith [hp x] : 0<1+a x)),one_div_one,one_div,inv_one,NNReal.coe_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) h

def fractionC (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x) : RealBorel where
  f x := a x/(1+a x)
  measurable := ha.div (measurable_const.add ha)
  bound := 1
  norm_le x := by
    rw [Real.norm_eq_abs,abs_of_pos (div_pos (hp x) (by linarith [hp x]))]
    exact (div_le_one (by linarith [hp x])).mpr (by linarith)


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_WeakSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX uκ uP uι

namespace ContinuousCircleWeight
open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace

open MeasureTheory Set Filter Topology Algebra Submodule
open scoped BigOperators ComplexConjugate

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X]

theorem compactMap_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    Integrable f μ :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (ae_of_all _ f.norm_coe_le_norm)

theorem probability_integral_lipschitz (μ : ProbabilityMeasure X) :
    LipschitzWith 1 (fun f : C(X, ℂ) => ∫ x, f x ∂(μ : Measure X)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [← integral_sub (compactMap_integrable _ f) (compactMap_integrable _ g)]
  simpa using (norm_integral_le_of_norm_le_const
    (ae_of_all (μ : Measure X) (fun x => (f - g).norm_coe_le_norm x)))

theorem probability_tendsto_of_dense_span {κ : Type uκ} (l : Filter κ)
    (s : Set C(X, ℂ)) (hs : (span ℂ s).topologicalClosure = ⊤)
    (μs : κ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (h : ∀ f ∈ s, Tendsto (fun j => ∫ x, f x ∂(μs j : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X)))) :
    Tendsto μs l (𝓝 μ) := by
  have heq : Equicontinuous
      (fun j (f : C(X, ℂ)) => ∫ x, f x ∂(μs j : Measure X)) :=
    (LipschitzWith.uniformEquicontinuous _ 1
      (fun j => probability_integral_lipschitz (μs j))).equicontinuous
  have hc := heq.isClosed_setOfPred_tendsto (l := l) (probability_integral_lipschitz μ).continuous
  have hspan : (↑(span ℂ s) : Set C(X, ℂ)) ⊆
      {f | Tendsto (fun j => ∫ x, f x ∂(μs j : Measure X)) l
        (𝓝 (∫ x, f x ∂(μ : Measure X)))} := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact h f hf
    | zero => simpa using (tendsto_const_nhds (x := (0 : ℂ)))
    | add f g _ _ hf hg =>
      have hw (ν : ProbabilityMeasure X) :
          (∫ x, (f + g) x ∂(ν : Measure X)) =
            (∫ x, f x ∂(ν : Measure X)) + ∫ x, g x ∂(ν : Measure X) :=
        integral_add (compactMap_integrable _ f) (compactMap_integrable _ g)
      simpa only [Set.mem_ofPred_eq, hw] using hf.add hg
    | smul a f _ hf =>
      have hw (ν : ProbabilityMeasure X) :
          (∫ x, (a • f) x ∂(ν : Measure X)) = a • ∫ x, f x ∂(ν : Measure X) :=
        integral_smul a _
      simpa only [Set.mem_ofPred_eq, hw] using hf.const_smul a
  have hall := closure_minimal hspan hc
  rw [← Submodule.topologicalClosure_coe, hs, Submodule.top_coe] at hall
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  exact hall (a := f.toContinuousMap) (mem_univ _)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma not_mem_frontier_ge_of_continuousAt {f : X → ℝ} {x : X} {t : ℝ}
    (hc : ContinuousAt f x) (hne : f x ≠ t) :
    x ∉ frontier {z | t ≤ f z} := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have he : ∀ᶠ z in 𝓝 x, f z < t := hc.eventually (gt_mem_nhds hlt)
    intro h
    have hd := h.1
    rw [mem_closure_iff_nhds] at hd
    have := hd {z | f z < t} he
    obtain ⟨z, hz, hzt⟩ := this
    exact (not_le_of_gt (show f z < t from hz)) (show t ≤ f z from hzt)
  · have he : {z | t ≤ f z} ∈ 𝓝 x := mem_of_superset (hc.eventually (lt_mem_nhds hgt))
      (fun z hz => show t ≤ f z from le_of_lt hz)
    exact fun h => h.2 (mem_interior_iff_mem_nhds.mpr he)

omit [BorelSpace X] [CompactSpace X] in
lemma ae_null_frontier_ge (μ : Measure X) [SFinite μ] {f : X → ℝ}
    (hf : Measurable f) (hc : ∀ᵐ x ∂μ, ContinuousAt f x) :
    ∀ᵐ t : ℝ, μ (frontier {x | t ≤ f x}) = 0 := by
  have hcount := Measure.countable_meas_level_set_pos (μ := μ) hf
  have hzero : ∀ᵐ t : ℝ, μ {x | f x = t} = 0 := by
    have h := hcount.measure_zero (volume : Measure ℝ)
    rw [measure_eq_zero_iff_ae_notMem] at h
    simpa only [mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] using h
  filter_upwards [hzero] with t ht
  rw [measure_eq_zero_iff_ae_notMem] at ht ⊢
  filter_upwards [hc, ht] with x hx hxt
  exact not_mem_frontier_ge_of_continuousAt hx hxt

omit [CompactSpace X] in

theorem tendsto_integral_nn_of_weak_of_ae_continuous [HasOuterApproxClosed X]
    {κ : Type uκ} {l : Filter κ} [l.IsCountablyGenerated]
    (μs : κ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (f : X → ℝ)
    (hf : Measurable f) (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x)
    (hnn : ∀ x, 0 ≤ f x) (M : ℝ) (hb : ∀ x, f x ≤ M) :
    Tendsto (fun n => ∫ x, f x ∂(μs n : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have hfi (ν : ProbabilityMeasure X) : Integrable f (ν : Measure X) :=
    Integrable.of_bound hf.aestronglyMeasurable M
      (ae_of_all _ (fun x => by simpa only [Real.norm_of_nonneg (hnn x)] using hb x))
  have heq (ν : ProbabilityMeasure X) : (∫ x, f x ∂(ν : Measure X)) =
      ∫ t in Ioc 0 M, (ν : Measure X).real {x | t ≤ f x} :=
    (hfi ν).integral_eq_integral_Ioc_meas_le (ae_of_all _ hnn) (ae_of_all _ hb)
  simp_rw [heq]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · apply Eventually.of_forall
    intro n
    have hm : Antitone (fun t : ℝ => (μs n : Measure X) {x | t ≤ f x}) := by
      intro s t hst
      exact measure_mono (fun x hx => hst.trans hx)
    exact hm.measurable.ennreal_toReal.aestronglyMeasurable
  · exact Eventually.of_forall (fun n => ae_of_all _ (fun t =>
      by simpa only [Measure.real, Real.norm_of_nonneg ENNReal.toReal_nonneg] using
        (measureReal_le_one (μ := (μs n : Measure X)) (s := {x | t ≤ f x}))))
  · exact integrable_const _
  · filter_upwards [ae_restrict_of_ae (ae_null_frontier_ge (μ : Measure X) hf hc)] with t ht
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ ht)

omit [CompactSpace X] in

theorem tendsto_integral_of_weak_of_ae_continuous [HasOuterApproxClosed X]
    {κ : Type uκ} {l : Filter κ} [l.IsCountablyGenerated]
    (μs : κ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (f : X → ℝ)
    (hf : Measurable f) (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x)
    (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    Tendsto (fun n => ∫ x, f x ∂(μs n : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have hb' (x : X) : -M ≤ f x ∧ f x ≤ M := abs_le.mp (hb x)
  have hnn (x : X) : 0 ≤ f x + M := by linarith [(hb' x).1]
  have hupper (x : X) : f x + M ≤ 2 * M := by linarith [(hb' x).2]
  have hc' : ∀ᵐ x ∂(μ : Measure X), ContinuousAt (fun x => f x + M) x :=
    hc.mono (fun _ hx => hx.add continuousAt_const)
  have h := tendsto_integral_nn_of_weak_of_ae_continuous μs μ hμ (fun x => f x + M)
    (hf.add_const M) hc' hnn (2 * M) hupper
  have heq (ν : ProbabilityMeasure X) : (∫ x, f x + M ∂(ν : Measure X)) =
      (∫ x, f x ∂(ν : Measure X)) + M := by
    rw [integral_add (Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hb))
      (integrable_const _)]
    simp
  simp_rw [heq] at h
  simpa only [add_sub_cancel_right] using h.sub_const M

omit [CompactSpace X] in
theorem tendsto_integral_complex_of_weak_of_ae_continuous [HasOuterApproxClosed X]
    {κ : Type uκ} {l : Filter κ} [l.IsCountablyGenerated]
    (μs : κ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (f : X → ℂ)
    (hf : Measurable f) (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x)
    (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    Tendsto (fun n => ∫ x, f x ∂(μs n : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have hfi (ν : ProbabilityMeasure X) : Integrable f (ν : Measure X) :=
    Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hb)
  have hre := tendsto_integral_of_weak_of_ae_continuous μs μ hμ (fun x => (f x).re)
    (Complex.measurable_re.comp hf)
    (hc.mono (fun _ hx => Complex.continuous_re.continuousAt.comp hx)) M
    (fun x => (Complex.abs_re_le_norm _).trans (hb x))
  have him := tendsto_integral_of_weak_of_ae_continuous μs μ hμ (fun x => (f x).im)
    (Complex.measurable_im.comp hf)
    (hc.mono (fun _ hx => Complex.continuous_im.continuousAt.comp hx)) M
    (fun x => (Complex.abs_im_le_norm _).trans (hb x))
  simp_rw [show ∀ ν : ProbabilityMeasure X,
    (∫ x, (f x).re ∂(ν : Measure X)) = (∫ x, f x ∂(ν : Measure X)).re from
      fun ν => integral_re (hfi ν)] at hre
  simp_rw [show ∀ ν : ProbabilityMeasure X,
    (∫ x, (f x).im ∂(ν : Measure X)) = (∫ x, f x ∂(ν : Measure X)).im from
      fun ν => integral_im (hfi ν)] at him
  have hrec := Complex.continuous_ofReal.continuousAt.tendsto.comp hre
  have himc := Complex.continuous_ofReal.continuousAt.tendsto.comp him
  simpa only [Function.comp_apply, Complex.re_add_im] using hrec.add (himc.mul_const Complex.I)

def withParameter {P : Type uP} [TopologicalSpace P] [MeasurableSpace P]
    [BorelSpace P] (ν : ProbabilityMeasure X) (b : P) : ProbabilityMeasure (X × P) :=
  ν.map (f := fun x => (x, b)) (measurable_id.prodMk measurable_const).aemeasurable

omit [CompactSpace X] in
theorem integral_withParameter [SecondCountableTopology X]
    {P : Type uP} [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P]
    [BorelSpace P] (ν : ProbabilityMeasure X) (b : P) (f : C(X × P, ℂ)) :
    (∫ z, f z ∂(withParameter ν b : Measure (X × P))) =
      ∫ x, f (x, b) ∂(ν : Measure X) := by
  exact integral_map (measurable_id.prodMk measurable_const).aemeasurable
    f.continuous.aestronglyMeasurable

theorem probability_tendsto_withParameter [SecondCountableTopology X]
    {P : Type uP} [TopologicalSpace P] [SecondCountableTopology P]
    [MeasurableSpace P] [BorelSpace P]
    {κ : Type uκ} {l : Filter κ} {νs : κ → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hν : Tendsto νs l (𝓝 ν)) {bs : κ → P} {b : P} (hb : Tendsto bs l (𝓝 b)) :
    Tendsto (fun n => withParameter (νs n) (bs n)) l (𝓝 (withParameter ν b)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  let g : C(P, C(X, ℂ)) :=
    (f.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry
  have hgb : Tendsto (fun n => g (bs n)) l (𝓝 (g b)) := g.continuous.continuousAt.tendsto.comp hb
  have hfix : Tendsto (fun n => ∫ x, g b x ∂(νs n : Measure X)) l
      (𝓝 (∫ x, g b x ∂(ν : Measure X))) := by
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hν
      (BoundedContinuousFunction.mkOfCompact (g b))
  have hdist : Tendsto (fun n => dist (∫ x, g b x ∂(νs n : Measure X))
      (∫ x, g (bs n) x ∂(νs n : Measure X))) l (𝓝 0) := by
    apply squeeze_zero (g := fun n => dist (g b) (g (bs n))) (fun _ => dist_nonneg)
      (fun n => by simpa only [NNReal.coe_one, one_mul] using
        (probability_integral_lipschitz (νs n)).dist_le_mul (g b) (g (bs n)))
    simpa only [dist_comm] using (tendsto_iff_dist_tendsto_zero.mp hgb)
  have h := tendsto_of_tendsto_of_dist hfix hdist
  change Tendsto (fun n => ∫ z, f.toContinuousMap z ∂(withParameter (νs n) (bs n) : Measure (X × P))) l
    (𝓝 (∫ z, f.toContinuousMap z ∂(withParameter ν b : Measure (X × P))))
  simpa only [integral_withParameter, g, ContinuousMap.curry_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, Prod.swap_prod_mk] using h

namespace Sampling

local instance instFactLtRealOfNat_solutions : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {ι : Type uι} [Fintype ι]

theorem separated_of_successive {κ : Type uκ} {l : Filter κ} {r : ℕ}
    (q : κ → ℕ → ℝ) (hq : ∀ n i, i < r → q n i ≠ 0)
    (hsep : ∀ i, i + 1 < r → Tendsto (fun n => q n (i + 1) / q n i) l atTop) :
    ∀ i j, i < j → j < r → Tendsto (fun n => q n i / q n j) l (𝓝 0) := by
  intro i j
  induction j with
  | zero => omega
  | succ j ih =>
    intro hij hjr
    have hnext : Tendsto (fun n => q n j / q n (j + 1)) l (𝓝 0) := by
      simpa only [Function.comp_def, inv_div] using
        tendsto_inv_atTop_zero.comp (hsep j hjr)
    by_cases heq : i = j
    · simpa [heq] using hnext
    · have hik : i < j := by omega
      have hlim := (ih hik (by omega)).mul hnext
      simp only [mul_zero] at hlim
      convert hlim using 1
      ext n
      field_simp [hq n j (by omega)]

end Sampling
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FourierSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uι uκ uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace

namespace ContinuousCircleWeight
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
namespace Sampling

def fejerFrequency {H : ℕ} (i : Fin H × Fin H) : ℤ := (i.1 : ℕ) - (i.2 : ℕ)

lemma fejerFrequency_abs_lt {H : ℕ} (i : Fin H × Fin H) : |fejerFrequency i| < H := by
  have hp := i.1.isLt
  have hq := i.2.isLt
  rw [fejerFrequency, abs_lt]
  constructor <;> omega

end Sampling
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Discrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uX uY uΩ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

section

lemma disjoint_prod_of_left {X : Type uX} {Y : Type uY} {A B : Set X} (C D : Set Y)
    (h : Disjoint A B) : Disjoint (A ×ˢ C) (B ×ˢ D) := by
  exact disjoint_left.mpr fun _ hx hy ↦ disjoint_left.mp h hx.1 hy.1
lemma disjoint_prod_of_right {X : Type uX} {Y : Type uY} (A B : Set X) {C D : Set Y}
    (h : Disjoint C D) : Disjoint (A ×ˢ C) (B ×ˢ D) := by
  exact disjoint_left.mpr fun _ hx hy ↦ disjoint_left.mp h hx.2 hy.2

end

variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

lemma boundedLayercake {f : Ω → ℝ} {B : ℝ}
    (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    ∫ x, f x ∂μ = ∫ t in Ioc 0 B, μ.real {x | t < f x} := by
  rw [hfi.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hf0)]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Ioi
    Ioc_subset_Ioi_self
  apply Filter.Eventually.of_forall
  intro t ht
  have hBt : B < t := lt_of_not_ge (fun h ↦ ht.2 ⟨ht.1, h⟩)
  have he : {x | t < f x} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_lt.mpr (le_trans (hfB x) (le_of_lt hBt))
  simp [he]

lemma boundedLayercake_weighted [IsFiniteMeasure μ] {f g : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ B) :
    ∫ x, f x * g x ∂μ =
      ∫ s in Ioc 0 B, ∫ x in {x | s < f x}, g x ∂μ := by
  have hi : Integrable (fun z : ℝ × Ω ↦
      if z.1 < f z.2 then g z.2 else 0)
      ((volume.restrict (Ioc 0 B)).prod μ) :=
    Integrable.of_bound
      ((hg.comp measurable_snd).ite
        (measurableSet_lt measurable_fst (hf.comp measurable_snd)) measurable_const).aestronglyMeasurable B (Filter.Eventually.of_forall fun z ↦ by
        split_ifs
        · simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 z.2)] using hgB z.2
        · simp only [norm_zero]
          by_cases h : Nonempty Ω
          · exact le_trans (hg0 (Classical.choice h)) (hgB (Classical.choice h))
          · exact False.elim (h ⟨z.2⟩))
  have he : (fun s : ℝ ↦ ∫ x in {x | s < f x}, g x ∂μ) =
      (fun s ↦ ∫ x, (if s < f x then g x else 0) ∂μ) := by
    funext s
    rw [← integral_indicator (measurableSet_lt measurable_const hf)]
    rfl
  rw [he, integral_integral_swap hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hset : (Ioc 0 B ∩ Iio (f x)) = Ioo 0 (f x) := by
    ext s
    simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.2⟩
    · exact fun h ↦ ⟨⟨h.1, le_trans (le_of_lt h.2) (hfB x)⟩, h.2⟩
  have hid : (fun s : ℝ ↦ if s < f x then g x else 0) =
      (Iio (f x)).indicator (fun _ ↦ g x) := rfl
  change f x * g x = ∫ s in Ioc 0 B, if s < f x then g x else 0
  rw [hid, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    inter_comm, hset, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal (hf0 x),
    smul_eq_mul]

lemma boundedLayercake_product [IsFiniteMeasure μ] {f g : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ B) :
    ∫ x, f x * g x ∂μ =
      ∫ s in Ioc 0 B, ∫ t in Ioc 0 B, μ.real {x | s < f x ∧ t < g x} := by
  rw [boundedLayercake_weighted hf hg hf0 hfB hg0 hgB]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  have hgi : Integrable g (μ.restrict {x | s < f x}) :=
    Integrable.of_bound hg.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 x)] using hgB x)
  dsimp only
  rw [boundedLayercake hgi hg0 hgB]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [Measure.real, Measure.restrict_apply (measurableSet_lt measurable_const hg)]
  congr 2
  ext x
  exact and_comm

lemma integrable_superlevel_measure [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) (B : ℝ) :
    Integrable (fun z : ℝ × ℝ ↦ μ.real {x | z.1 < f x ∧ z.2 < g x})
      ((volume.restrict (Ioc 0 B)).prod (volume.restrict (Ioc 0 B))) := by
  have hm : Measurable (fun z : ℝ × ℝ ↦ μ {x | z.1 < f x ∧ z.2 < g x}) :=
    measurable_measure_prodMk_left
      ((measurableSet_lt (measurable_fst.comp measurable_fst)
        (hf.comp measurable_snd)).inter
       (measurableSet_lt (measurable_snd.comp measurable_fst)
        (hg.comp measurable_snd)))
  exact Integrable.of_bound hm.ennreal_toReal.aestronglyMeasurable (μ.real univ)
      (Filter.Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_mono (subset_univ _))

lemma superlevel_discrepancy [IsFiniteMeasure μ] {ν : Measure Ω} [IsFiniteMeasure ν]
    {f g : Ω → ℝ} {B ε : ℝ} (hB : 0 ≤ B)
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ B)
    (hdisc : ∀ s ∈ Ioc 0 B, ∀ t ∈ Ioc 0 B,
      |μ.real {x | s < f x ∧ t < g x} - ν.real {x | s < f x ∧ t < g x}| ≤ ε) :
    |(∫ x, f x * g x ∂μ) - (∫ x, f x * g x ∂ν)| ≤ B ^ 2 * ε := by
  rw [boundedLayercake_product hf hg hf0 hfB hg0 hgB,
    boundedLayercake_product hf hg hf0 hfB hg0 hgB]
  have hiμ := integrable_superlevel_measure (μ := μ) hf hg B
  have hiν := integrable_superlevel_measure (μ := ν) hf hg B
  rw [integral_integral hiμ, integral_integral hiν, ← integral_sub hiμ hiν,
    ← Real.norm_eq_abs]
  have hb : ∀ᵐ z : ℝ × ℝ ∂((volume.restrict (Ioc 0 B)).prod
      (volume.restrict (Ioc 0 B))),
      ‖μ.real {x | z.1 < f x ∧ z.2 < g x} -
        ν.real {x | z.1 < f x ∧ z.2 < g x}‖ ≤ ε := by
    have hm : ∀ᵐ z : ℝ × ℝ ∂((volume.restrict (Ioc 0 B)).prod
        (volume.restrict (Ioc 0 B))), z ∈ Ioc 0 B ×ˢ Ioc 0 B := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioc.prod measurableSet_Ioc)]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact ⟨hs, ht⟩
    filter_upwards [hm] with z hz
    exact hdisc z.1 hz.1 z.2 hz.2
  convert! norm_integral_le_of_norm_le (integrable_const ε) hb using 1
  simp [Measure.prod_apply, Measure.real, Real.volume_Ioc, hB, pow_two, mul_assoc]



end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TrialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uι uX uκ uτ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology

open Set MeasureTheory
open scoped BigOperators ENNReal Classical
section

lemma product_many_failures_bound {ι : Type uι} {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ι) (A : ∀ i, Set (X i))
    (hA : ∀ i, MeasurableSet (A i)) (q : ℕ) (p : ℝ≥0∞)
    (hp : ∀ i∈I, μ i (A i) ≤ p) :
    Measure.infinitePi μ {x | q ≤ (I.filter fun i ↦ x i ∈ A i).card} ≤
      (I.card.choose q : ℝ≥0∞) * p^q := by
  classical
  let S := I.powersetCard q
  have hcover : {x | q ≤ (I.filter fun i ↦ x i∈A i).card} ⊆
      ⋃ J∈S, Set.pi (J : Set ι) A := by
    intro x hx
    obtain ⟨J,hJI,hJq⟩ := Finset.exists_subset_card_eq hx
    refine mem_iUnion.mpr ⟨J,mem_iUnion.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨hJI.trans (Finset.filter_subset _ _),hJq⟩
    · intro i hi
      exact (Finset.mem_filter.mp (hJI hi)).2
  calc
    Measure.infinitePi μ {x | q ≤ (I.filter fun i ↦ x i ∈ A i).card} ≤
        Measure.infinitePi μ (⋃ J∈S, Set.pi (J : Set ι) A) := measure_mono hcover
    _ ≤ ∑ J∈S, Measure.infinitePi μ (Set.pi (J : Set ι) A) := measure_biUnion_finset_le _ _
    _ = ∑ J∈S, ∏ i∈J, μ i (A i) := by
      apply Finset.sum_congr rfl
      intro J hJ
      exact Measure.infinitePi_pi μ (fun i _ ↦ hA i)
    _ ≤ ∑ _J∈S, p^q := by
      apply Finset.sum_le_sum
      intro J hJ
      obtain ⟨hJI,hJq⟩ := Finset.mem_powersetCard.mp hJ
      calc
        (∏ i∈J, μ i (A i)) ≤ ∏ _i∈J, p := Finset.prod_le_prod' fun i hi ↦ hp i (hJI hi)
        _ = p^q := by simp [hJq]
    _ = _ := by simp [S,Finset.card_powersetCard,nsmul_eq_mul]

lemma product_many_failures_exp_bound {ι : Type uι} {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ι) (A : ∀ i, Set (X i))
    (hA : ∀ i, MeasurableSet (A i)) (q : ℕ) (p : ℝ≥0∞)
    (hp : ∀ i∈I, μ i (A i) ≤ p) :
    Measure.infinitePi μ {x | q ≤ (I.filter fun i ↦ x i ∈ A i).card} ≤
      (2 : ℝ≥0∞)^I.card * p^q := by
  apply (product_many_failures_bound μ I A hA q p hp).trans
  gcongr
  exact_mod_cast Nat.choose_le_two_pow I.card q

end
open Filter Set
open scoped Topology
section

lemma phase_failure_count_lower (m : ℕ) : (9:ℝ)/10*m ≤ ((m-m/20:ℕ):ℝ) := by
  have hle : m/20 ≤ m := Nat.div_le_self _ _
  have hd : ((m/20:ℕ):ℝ) ≤ (m:ℝ)/20 := Nat.cast_div_le
  rw [Nat.cast_sub hle]
  nlinarith [show (0:ℝ) ≤ m by positivity]

open ContinuousCircleWeight.Sampling
open scoped Classical ENNReal

end
open Set MeasureTheory
open scoped ENNReal Classical
open ContinuousCircleWeight.Sampling Filter
open scoped Topology


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FiniteSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uι uκ uP uτ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical

open Filter
open scoped Topology
section
lemma finite_accuracy_of_sequential {P : Type uP} [MetricSpace P]
    {r : ℕ} (b : P) (T : (ℕ → ℤ) → P → ℝ) {L η : ℝ} (hL : L < η)
    (hseq : ∀ (q : ℕ → ℕ → ℤ), (∀ n i, i < r → 0 < q n i) →
      (∀ i, i+1 < r → Tendsto (fun n => (q n (i+1):ℝ)/q n i) atTop atTop) →
      ∀ (bs : ℕ → P), Tendsto bs atTop (𝓝 b) →
        Tendsto (fun n => T (q n) (bs n)) atTop (𝓝 L)) :
    ∃ M : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ (q : ℕ → ℤ) (β : P),
      (∀ i, i < r → 0 < q i) →
      (∀ i, i+1 < r → (M:ℝ) ≤ (q (i+1):ℝ)/q i) →
      dist β b < δ → T q β < η := by
  classical
  by_contra! h
  have hex (n : ℕ) : ∃ (q : ℕ → ℤ) (β : P),
      (∀ i, i < r → 0 < q i) ∧
      (∀ i, i+1 < r → (n:ℝ) ≤ (q (i+1):ℝ)/q i) ∧
      dist β b < 1/((n:ℝ)+1) ∧ η ≤ T q β := by
    exact h n (1/((n:ℝ)+1)) (by positivity)
  choose q bs hq hsep hdist hbad using hex
  have hq' : ∀ i, i+1 < r → Tendsto (fun n => (q n (i+1):ℝ)/q n i) atTop atTop := by
    intro i hi
    exact tendsto_atTop_mono (fun n => hsep n i hi) tendsto_natCast_atTop_atTop
  have hb : Tendsto bs atTop (𝓝 b) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hh := (hseq q hq hq' bs hb).eventually (gt_mem_nhds hL)
  obtain ⟨n,hn⟩ := hh.exists
  exact (not_lt_of_ge (hbad n)) hn

open ContinuousCircleWeight.Sampling
open scoped Topology
end

open Set Filter
open scoped Topology
section

lemma fractional_interval {a b u v q : ℝ} (_hab : a < b) (hq : 0 < q)
    (hlong : 2 < q*(b-a)) (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u < v) :
    ∃ c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧
      ∀ x∈Icc c d, Int.fract (q*x) ∈ Ioo u v := by
  let t := (u+v)/2
  have ht : t∈Ioo u v := ⟨by dsimp [t]; linarith,by dsimp [t]; linarith⟩
  have ht0 : 0 < t := lt_of_le_of_lt hu ht.1
  have ht1 : t < 1 := lt_of_lt_of_le ht.2 hv
  let x := ((⌊q*a⌋:ℝ)+1+t)/q
  have hqx : q*x = (⌊q*a⌋:ℝ)+1+t := by dsimp [x]; field_simp
  have hxa : a < x := by
    apply (lt_div_iff₀ hq).mpr
    have h := Int.lt_floor_add_one (q*a)
    nlinarith
  have hxb : x < b := by
    apply (div_lt_iff₀ hq).mpr
    have h := Int.floor_le (q*a)
    nlinarith
  have hfract : Int.fract (q*x)=t := by
    rw [hqx,add_comm _ t,← Int.cast_one,← Int.cast_add,Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨ht0.le,ht1⟩
  have hne : q*x ≠ (⌊q*x⌋:ℝ) := by
    intro he
    have hz : Int.fract (q*x)=0 := by rw [he,Int.fract_intCast]
    linarith
  have hc : ContinuousAt (fun z : ℝ => Int.fract (q*z)) x :=
    (continuousAt_fract hne).comp (by fun_prop)
  have hU : Ioo a b ∩ (fun z : ℝ => Int.fract (q*z)) ⁻¹' Ioo u v ∈ 𝓝 x :=
    inter_mem (Ioo_mem_nhds hxa hxb) (hc.preimage_mem_nhds (by rw [hfract]; exact Ioo_mem_nhds ht.1 ht.2))
  obtain ⟨c,d,⟨hc,hd⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
  refine ⟨(c+x)/2,(x+d)/2,by linarith,?_,?_⟩
  · intro z hz
    exact (hsub ⟨by linarith [hz.1],by linarith [hz.2]⟩).1
  · intro z hz
    exact (hsub ⟨by linarith [hz.1],by linarith [hz.2]⟩).2

lemma divisible_frequency_interval {a b u v : ℝ} (hab : a < b)
    (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u < v) {p : ℕ} (hp : 0 < p) (M : ℝ) :
    ∃ q : ℕ, 0 < q ∧ p ∣ q ∧ M < (q:ℝ)/p ∧
      ∃ c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧
        ∀ x∈Icc c d, Int.fract ((q:ℝ)*x)∈Ioo u v := by
  obtain ⟨L,hL⟩ := exists_nat_gt (max (max M 1) (2/((p:ℝ)*(b-a))))
  have hpR : 0 < (p:ℝ) := Nat.cast_pos.mpr hp
  have hL1 : 1 < (L:ℝ) := lt_of_le_of_lt (le_trans (le_max_right M 1) (le_max_left _ _)) hL
  have hL0 : 0 < L := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<1) hL1)
  have hM : M < (L:ℝ) := lt_of_le_of_lt (le_trans (le_max_left M 1) (le_max_left _ _)) hL
  have hlong : 2 < (p*L:ℕ)* (b-a) := by
    have h := lt_of_le_of_lt (le_max_right (max M 1) (2/((p:ℝ)*(b-a)))) hL
    have hh := (div_lt_iff₀ (mul_pos hpR (sub_pos.mpr hab))).mp h
    push_cast
    nlinarith
  obtain ⟨c,d,hcd,hsub,hfr⟩ := fractional_interval hab
    (show 0 < ((p*L:ℕ):ℝ) by positivity) hlong hu hv huv
  refine ⟨p*L,Nat.mul_pos hp hL0, dvd_mul_right p L,?_,c,d,hcd,hsub,hfr⟩
  simpa only [Nat.cast_mul,mul_div_cancel_left₀ _ hpR.ne'] using hM

lemma finite_frequency_realization (m : ℕ) (u v : ℕ → ℝ)
    (hu : ∀ i < m, 0 ≤ u i) (hv : ∀ i < m, v i ≤ 1) (huv : ∀ i < m, u i < v i)
    {a b : ℝ} (hab : a < b) {p : ℕ} (hp : 0 < p) (M : ℝ) :
    ∃ q : ℕ → ℕ, q 0=p ∧ (∀ i ≤ m, 0 < q i) ∧
      (∀ i < m, q i ∣ q (i+1) ∧ M < (q (i+1):ℝ)/q i) ∧
      ∃ c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧
        ∀ i < m, ∀ x∈Icc c d, Int.fract ((q (i+1):ℝ)*x)∈Ioo (u i) (v i) := by
  induction m with
  | zero =>
    refine ⟨fun _ => p,rfl,fun _ _ => hp,by simp, (2*a+b)/3,(a+2*b)/3,by linarith,?_,by simp⟩
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  | succ m ih =>
    obtain ⟨q,hq0,hqp,hqM,c,d,hcd,hsub,hfr⟩ :=
      ih (fun i hi => hu i (by omega)) (fun i hi => hv i (by omega)) (fun i hi => huv i (by omega))
    obtain ⟨r,hr,hrdiv,hrM,e,f,hef,hefs,hphase⟩ :=
      divisible_frequency_interval hcd (hu m (by omega)) (hv m (by omega)) (huv m (by omega)) (hqp m le_rfl) M
    refine ⟨Function.update q (m+1) r,?_,?_,?_,e,f,hef,?_,?_⟩
    · simpa using hq0
    · intro i hi
      by_cases he : i=m+1
      · subst i; simpa
      · rw [Function.update_of_ne he]
        exact hqp i (by omega)
    · intro i hi
      by_cases he : i=m
      · subst i
        simpa [Function.update_of_ne (show m ≠ m+1 by omega)] using And.intro hrdiv hrM
      · rw [Function.update_of_ne (show i≠m+1 by omega),Function.update_of_ne (show i+1≠m+1 by omega)]
        exact hqM i (by omega)
    · exact fun x hx => hsub ⟨(hefs hx).1.le,(hefs hx).2.le⟩
    · intro i hi x hx
      by_cases he : i=m
      · subst i
        simpa using hphase x hx
      · rw [Function.update_of_ne (show i+1≠m+1 by omega)]
        exact hfr i (by omega) x ⟨(hefs hx).1.le,(hefs hx).2.le⟩

def fractionalCube (m : ℕ) (q : ℕ → ℕ) (θ : ℝ) : Fin m → Set.Icc (0:ℝ) 1 :=
  fun i => ⟨Int.fract ((q (i+1):ℝ)*θ),Int.fract_nonneg _,(Int.fract_lt_one _).le⟩

lemma realize_phase_neighborhood {m : ℕ} (γ : Fin m → Set.Icc (0:ℝ) 1)
    (hγ : ∀ i, (γ i:ℝ)∈Ioo 0 1) {U : Set (Fin m → Set.Icc (0:ℝ) 1)} (hU : U∈𝓝 γ)
    {a b : ℝ} (hab : a < b) {p : ℕ} (hp : 0 < p) (M : ℝ) :
    ∃ q : ℕ → ℕ, q 0=p ∧ (∀ i ≤ m, 0 < q i) ∧
      (∀ i < m, q i ∣ q (i+1) ∧ M < (q (i+1):ℝ)/q i) ∧
      ∃ c d : ℝ, c < d ∧ Icc c d ⊆ Ioo a b ∧
        ∀ θ∈Icc c d, fractionalCube m q θ ∈ U := by
  obtain ⟨δ,hδ,hdU⟩ := Metric.mem_nhds_iff.mp hU
  let g : ℕ → ℝ := fun i => if hi : i < m then (γ ⟨i,hi⟩:ℝ) else 1/2
  let u : ℕ → ℝ := fun i => max 0 (g i-δ/2)
  let v : ℕ → ℝ := fun i => min 1 (g i+δ/2)
  have hg (i : ℕ) (hi : i < m) : g i∈Ioo 0 1 := by simpa [g,hi] using hγ ⟨i,hi⟩
  have huv (i : ℕ) (hi : i < m) : u i < v i := by
    dsimp [u,v]
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    constructor <;> constructor <;> linarith [(hg i hi).1,(hg i hi).2]
  obtain ⟨q,hq0,hqp,hqM,c,d,hcd,hsub,hfr⟩ := finite_frequency_realization m u v
    (fun i _ => le_max_left _ _) (fun i _ => min_le_left _ _) huv hab hp M
  refine ⟨q,hq0,hqp,hqM,c,d,hcd,hsub,?_⟩
  intro θ hθ
  apply hdU
  rw [Metric.mem_ball,dist_pi_lt_iff hδ]
  intro i
  rw [Subtype.dist_eq,Real.dist_eq,abs_lt]
  have h := hfr i i.isLt θ hθ
  have hl := lt_of_le_of_lt (le_max_right 0 (g i-δ/2)) h.1
  have hh := lt_of_lt_of_le h.2 (min_le_right 1 (g i+δ/2))
  simp only [g,i.isLt,↓reduceDIte,Fin.eta] at hl hh
  change -δ < Int.fract ((q (i+1):ℝ)*θ)-(γ i:ℝ) ∧ Int.fract ((q (i+1):ℝ)*θ)-(γ i:ℝ) < δ
  constructor <;> linarith
end

open ContinuousCircleWeight.Sampling
open scoped Topology


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ReturnSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uV

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology

section
open scoped BigOperators

def phaseRange (N R : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌊R⌋) ⌊R⌋).filter (fun k => N/4 ≤ |(k:ℝ)|)
lemma mem_phaseRange {N R : ℝ} {k : ℤ} (hk : N/4 ≤ |(k:ℝ)|) (hkR : |(k:ℝ)| ≤ R) :
    k∈phaseRange N R := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,hk⟩
  · have h : (-k:ℝ) ≤ R := by linarith [(abs_le.mp hkR).1]
    have hh : -k ≤ ⌊R⌋ := Int.le_floor.mpr (by simpa using h)
    omega
  · exact Int.le_floor.mpr (abs_le.mp hkR).2
lemma phaseRange_bound {N R : ℝ} (hR : 1 ≤ R) : (phaseRange N R).card ≤ 3*R := by
  have hR0 : 0 ≤ ⌊R⌋ := Int.floor_nonneg.mpr (by linarith)
  calc
    ((phaseRange N R).card:ℝ) ≤ ((Finset.Icc (-⌊R⌋) ⌊R⌋).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    _ = 2*(⌊R⌋:ℝ)+1 := by
      rw [Int.card_Icc]
      have hh : 0 ≤ ⌊R⌋+1-(-⌊R⌋) := by omega
      rw [← Int.cast_natCast,Int.toNat_of_nonneg hh]
      push_cast
      ring
    _ ≤ 3*R := by have := Int.floor_le R; linarith
lemma phaseRange_lower {N R : ℝ} {k : ℤ} (hk : k∈phaseRange N R) : N/4 ≤ |(k:ℝ)| :=
  (Finset.mem_filter.mp hk).2
end

open Set Topology

open scoped BigOperators

open Set Filter
open scoped Topology


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_SamplingStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uτ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators

open scoped BigOperators
namespace ContinuousCircleWeight

theorem exists_nonzero_low_product_coefficient (K : ℕ) (A B : Polynomial ℂ)
    (hA : A.coeff K ≠ 0) (hB : B.coeff K ≠ 0) :
    ∃ n ≤ 2 * K, (A * B).coeff n ≠ 0 := by
  have hA0 : A ≠ 0 := by contrapose! hA; simp [hA]
  have hB0 : B ≠ 0 := by contrapose! hB; simp [hB]
  refine ⟨(A * B).natTrailingDegree, ?_,
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr (mul_ne_zero hA0 hB0)⟩
  rw [Polynomial.natTrailingDegree_mul hA0 hB0]
  have ha := Polynomial.natTrailingDegree_le_of_ne_zero hA
  have hb := Polynomial.natTrailingDegree_le_of_ne_zero hB
  omega

end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_NestedAngles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uS

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators

open Set
section

lemma prefix_persistent (d : ℕ → ℕ) (q : ℕ → ℕ → ℕ)
    (hd : Monotone d) (hq : ∀ j i, i≤d j → q (j+1) i=q j i)
    {j n i : ℕ} (hjn : j≤n) (hi : i≤d j) : q n i=q j i := by
  induction n,hjn using Nat.le_induction with
  | base => rfl
  | succ n hjn ih => rw [hq n i (hi.trans (hd hjn)),ih]

lemma diagonal_prefix_eq (d : ℕ → ℕ) (q : ℕ → ℕ → ℕ)
    (hd : Monotone d) (hlen : ∀ j,j≤d j) (hq : ∀ j i, i≤d j → q (j+1) i=q j i)
    {j i : ℕ} (hi : i≤d j) : q i i=q j i := by
  rcases le_total j i with hji|hij
  · exact prefix_persistent d q hd hq hji hi
  · exact (prefix_persistent d q hd hq hij (hlen i)).symm

end

open Set

open Set

structure BlockPartition where
  m : ℕ → ℕ
  d : ℕ → ℕ
  zero : d 0=0
  step : ∀ j,d (j+1)=d j+m j
  positive : ∀ j,0 < m j

lemma BlockPartition.strictMono (B : BlockPartition) : StrictMono B.d :=
  strictMono_nat_of_lt_succ (fun j => by rw [B.step]; exact Nat.lt_add_of_pos_right (B.positive j))
lemma BlockPartition.ge (B : BlockPartition) (j : ℕ) : j≤ B.d j := by
  induction j with
  | zero => omega
  | succ j ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (B.strictMono (Nat.lt_succ_self j)))

lemma BlockPartition.exists_unique (B : BlockPartition) (i : ℕ) :
    ∃! j, B.d j≤ i ∧ i< B.d (j+1) := by
  have hex : ∃ j,i< B.d (j+1) := ⟨i,(Nat.lt_succ_self i).trans_le (B.ge (i+1))⟩
  let j := Nat.find hex
  have hj : i< B.d (j+1) := Nat.find_spec hex
  have hlo : B.d j≤ i := by
    by_cases h0 : j=0
    · rw [h0,B.zero]; omega
    · have hfalse : ¬ i< B.d ((j-1)+1) := Nat.find_min hex (by omega : j-1< j)
      have he : j-1+1=j := by omega
      rw [he] at hfalse
      omega
  refine ⟨j,⟨hlo,hj⟩,?_⟩
  intro k hk
  apply le_antisymm
  · by_contra hn
    have hd := B.strictMono.monotone (show j+1≤ k by omega)
    omega
  · by_contra hn
    have hd := B.strictMono.monotone (show k+1≤ j by omega)
    omega

def BlockPartition.number (B : BlockPartition) (i : ℕ) : ℕ := (B.exists_unique i).choose
lemma BlockPartition.number_spec (B : BlockPartition) (i : ℕ) :
    B.d (B.number i)≤ i ∧ i< B.d (B.number i+1) := (B.exists_unique i).choose_spec.1
lemma BlockPartition.number_eq (B : BlockPartition) {i j : ℕ} (hlo : B.d j≤ i) (hhi : i< B.d (j+1)) :
    B.number i=j := ((B.exists_unique i).choose_spec.2 j ⟨hlo,hhi⟩).symm

def BlockPartition.position (B : BlockPartition) (i : ℕ) : Fin (B.m (B.number i)) :=
  ⟨i-B.d (B.number i),by have hh := B.number_spec i; rw [B.step] at hh; omega⟩

def BlockPartition.equiv (B : BlockPartition) : (Σ j,Fin (B.m j)) ≃ ℕ where
  toFun x := B.d x.1+x.2.val
  invFun i := ⟨B.number i,B.position i⟩
  left_inv x := by
    have hn : B.number (B.d x.1+x.2.val)=x.1 := by
      apply B.number_eq (by omega)
      rw [B.step]
      exact Nat.add_lt_add_left x.2.isLt _
    apply Sigma.ext hn
    apply (Fin.heq_ext_iff (congrArg B.m hn)).mpr
    simp [position,hn]
  right_inv i := by
    change B.d (B.number i)+(i-B.d (B.number i))=i
    exact Nat.add_sub_of_le (B.number_spec i).1


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_OrbitBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

universe uX uY uι

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Set Filter
open scoped ENNReal Topology
section

def weightedMeasure {X : Type uX} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))
lemma weightedMeasure_finite {X : Type uX} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : Integrable f μ) (hn : ∀ x,0≤f x) : IsFiniteMeasure (weightedMeasure μ f) := by
  apply isFiniteMeasure_withDensity
  rw [←ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ hn)]
  exact ENNReal.ofReal_ne_top

def weightedGraph {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → ℝ) (T : X → Y) : Measure (X×Y) :=
  Measure.map (fun x => (x,T x)) (weightedMeasure μ f)

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

def finiteGraphAverage {X : Type uX} {ι : Type uι} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (w : ι → X → ℝ) (T : ι → X → X) : Measure (X×X) :=
  ENNReal.ofReal ((Fintype.card ι:ℝ)⁻¹) • ∑ i,weightedGraph μ (w i) (T i)
def finiteAverage {X : Type uX} {ι : Type uι} [Fintype ι] (w : ι → X → ℝ) (x : X) : ℝ :=
  (Fintype.card ι:ℝ)⁻¹ * ∑ i,w i x

lemma finiteGraphAverage_finite {X : Type uX} {ι : Type uι} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (w : ι → X → ℝ) (T : ι → X → X)
    (hw : ∀ i,Integrable (w i) μ) (hn : ∀ i x,0≤w i x) :
    IsFiniteMeasure (finiteGraphAverage μ w T) := by
  have (i : ι) : IsFiniteMeasure (weightedMeasure μ (w i)) := weightedMeasure_finite μ (hw i) (hn i)
  have (i : ι) : IsFiniteMeasure (weightedGraph μ (w i) (T i)) := by unfold weightedGraph; infer_instance
  unfold finiteGraphAverage
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

end

open Set MeasureTheory
open scoped BigOperators


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_RationalGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uι uX uY

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CircleSampling

open Set
lemma rational_grid_lift {N P : ℕ} (hN : 0 < N) (hP : 0 < P) (hNP : N ∣ P)
    (a : Fin N) : ∃ t : Fin P, ((t.val:ℝ)/(P:ℝ):ℝ) = (a.val:ℝ)/(N:ℝ) := by
  obtain ⟨c,rfl⟩ := hNP
  have hc : 0 < c := Nat.pos_of_mul_pos_left hP
  refine ⟨⟨a.val*c,Nat.mul_lt_mul_of_pos_right a.isLt hc⟩,?_⟩
  dsimp
  push_cast
  field_simp
end CircleSampling

open MeasureTheory Set

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_GraphTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX uY uι uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

open MeasureTheory Set Filter Topology TopologicalSpace
namespace ContinuousCircleWeight

section

def cappedRatio {X : Type uX} (F : ℤ → X → ℝ) (B : ℝ≥0) (x y : X) (k : ℤ) : ℝ :=
  min (B : ℝ) (max 0 (F k y / F k x))

lemma cappedRatio_bounds {X : Type uX} (F : ℤ → X → ℝ) (B : ℝ≥0)
    (x y : X) (k : ℤ) : 0 ≤ cappedRatio F B x y k ∧ cappedRatio F B x y k ≤ B :=
  ⟨le_min B.coe_nonneg (le_max_left _ _), min_le_left _ _⟩

def cappedDiagonal {X : Type uX} (F : ℤ → X → ℝ) (B : ℝ≥0) (x y : X) : FiberOperator :=
  lpDiagonal (fun k ↦ (cappedRatio F B x y k : ℂ)) B (fun k ↦ by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cappedRatio_bounds F B x y k).1] using (cappedRatio_bounds F B x y k).2)

instance fiberSeparable : SeparableSpace FiberHilbert := by
  let b := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ FiberHilbert)
  apply isSeparable_univ_iff.mp
  have hs := ((countable_range (b : ℤ → FiberHilbert)).isSeparable.span (R := ℂ)).closure
  rw [← Submodule.topologicalClosure_coe, b.dense_span] at hs
  exact hs

local instance fiberMeasurable : MeasurableSpace FiberHilbert := borel FiberHilbert

def cappedPairRelation {X : Type uX} (p : X → FiberOperator) (F : ℤ → X → ℝ)
    (B : ℝ≥0) : Set (X × X) :=
  {z | ∀ k : ℤ, (1-p z.2) (cappedDiagonal F B z.1 z.2 (p z.1 (lp.single 2 k 1)))=0}

end

open MeasureTheory Set
open scoped ComplexConjugate

end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ProjectionIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace

namespace CircleSampling
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ComplexInnerProductSpace Topology ENNReal
local instance instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert : MeasurableSpace FiberHilbert := borel FiberHilbert
end CircleSampling

namespace ContinuousCircleWeight
open MeasureTheory Filter Set
open scoped Topology ComplexInnerProductSpace
local instance instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert_1 : MeasurableSpace FiberHilbert := borel FiberHilbert
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ActualDigits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal

namespace CircleSampling
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped Topology ENNReal ComplexInnerProductSpace
def hybridChoice (D : ℕ) (i : ℕ) : Bool := decide (i<D+1)
end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Thresholds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleSampling

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal

section
open Set ContinuousCircleWeight.Sampling
open scoped BigOperators

lemma threshold_bounds_of_abs {k : ℤ} {β a : ℝ} (ha : 0<a) (hat : a≤|(k:ℝ)| *β)
    (ht : |(k:ℝ)| *β<1/2) : a≤1-Int.fract ((k:ℝ)*β) ∧ 1-Int.fract ((k:ℝ)*β)≤1-a := by
  have hp : 0 < |(k:ℝ)| *β := ha.trans_le hat
  by_cases hk : 0≤k
  · rw [abs_of_nonneg ((by exact_mod_cast hk))] at hat ht hp
    rw [Int.fract_eq_self.mpr ⟨hp.le,by linarith⟩]
    constructor <;> linarith
  · have hk' : (k:ℝ)<0 := (by exact_mod_cast (lt_of_not_ge hk))
    rw [abs_of_neg hk'] at hat ht hp
    have hf : Int.fract (-((k:ℝ)*β))=-((k:ℝ)*β) := Int.fract_eq_self.mpr ⟨by nlinarith,by nlinarith⟩
    have hne : Int.fract (-((k:ℝ)*β))≠0 := by rw [hf]; nlinarith
    have hn := Int.fract_neg hne
    rw [neg_neg,hf] at hn
    rw [hn]
    constructor <;> nlinarith

end

open MeasureTheory Set
open scoped ENNReal


end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_LaurentCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ContinuousCircleWeight

open scoped BigOperators

def laurentArray (K : ℕ) (a : ℤ → ℂ) (i : Fin (2*K+1)) : ℂ := a ((i.val:ℤ)-(K:ℤ))
def retainedIndices (K n : ℕ) : Finset ℤ := Finset.Icc (-(K:ℤ)) ((K:ℤ)-(n:ℤ))
lemma mem_retainedIndices (K n : ℕ) (v : ℤ) : v∈retainedIndices K n ↔ |v| ≤ (K:ℤ) ∧ |(n:ℤ)+v| ≤ (K:ℤ) := by
  simp only [retainedIndices,Finset.mem_Icc,abs_le]
  omega
end ContinuousCircleWeight

namespace CircleSampling

section

section
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped Topology ENNReal ComplexInnerProductSpace BigOperators
local instance instMeasurableSpaceSubtypePreLpIntComplexMemAddSubgroupFiberHilbert_2 : MeasurableSpace FiberHilbert := borel FiberHilbert
end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal ComplexInnerProductSpace BigOperators

end

open MeasureTheory Set Filter
open scoped ENNReal

end CircleSampling

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_ContinuousWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

def concentratedWeight {X : Type uX} (H : ℕ → X → ℝ) (z : X) (x : X) : ℝ :=
  by classical exact if x = z then 0 else Real.exp (- ∑' i, H i x)

@[simp] lemma concentratedWeight_self {X : Type uX} (H : ℕ → X → ℝ) (z : X) :
    concentratedWeight H z z = 0 := by simp [concentratedWeight]

lemma concentratedWeight_bounds {X : Type uX} (H : ℕ → X → ℝ) (z : X)
    (hH : ∀ i x, 0 ≤ H i x) (x : X) :
    0 ≤ concentratedWeight H z x ∧ concentratedWeight H z x ≤ 1 := by
  classical
  unfold concentratedWeight
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (tsum_nonneg (fun i ↦ hH i x)))⟩

@[simp] lemma concentratedWeight_eq_zero {X : Type uX} (H : ℕ → X → ℝ) (z x : X) :
    concentratedWeight H z x = 0 ↔ x = z := by
  classical
  unfold concentratedWeight
  split_ifs with h
  · simp [h]
  · simp [h, Real.exp_ne_zero]

def LocallyFiniteOff {X : Type uX} [TopologicalSpace X] (H : ℕ → X → ℝ) (z : X) : Prop :=
  ∀ x, x ≠ z → ∃ s : Finset ℕ, ∀ᶠ y in 𝓝 x, ∀ i, i ∉ s → H i y = 0

lemma finite_support_of_locallyFiniteOff {X : Type uX} [TopologicalSpace X]
    (H : ℕ → X → ℝ) (z : X) (hlocal : LocallyFiniteOff H z) {x : X} (hx : x ≠ z) :
    (Function.support (fun i ↦ H i x)).Finite := by
  obtain ⟨s,hs⟩ := hlocal x hx
  exact s.finite_toSet.subset (by
    intro i hi
    by_contra his
    exact hi (mem_of_mem_nhds hs i his))

lemma locallyFiniteOff_of_shrinking_supports {X : Type uX} [MetricSpace X]
    (H : ℕ → X → ℝ) (z : X) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hs : ∀ i x, r i ≤ dist x z → H i x = 0) : LocallyFiniteOff H z := by
  classical
  intro x hx
  have hd : 0 < dist x z := dist_pos.mpr hx
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hr.eventually (gt_mem_nhds (half_pos hd)))
  refine ⟨Finset.range N, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (half_pos hd)] with y hy
  intro i hi
  apply hs
  have hn : N ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
  have hlt := hN i hn
  have htri := dist_triangle x y z
  have hxy : dist x y < dist x z / 2 := by
    simpa only [Metric.mem_ball, dist_comm y x] using hy
  linarith



end ContinuousCircleWeight

end

end OAI
end


