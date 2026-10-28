-- Prove2me | Definitions.Def_OAIQ5T4001
-- name    : OAIQ5T4001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T12:40:57.917912+00:00
-- url     : https://prove2.me/theorems/e0115a8c-0adc-4890-bee0-38f4893e241e
-- title:
--   Definitions bundle OAIQ5T4001 of the split of OpenAI, The Euclidean plane cannot be colored with five colors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EuclideanFiveColor.no_proper_five_coloring`, carved from OpenAI's openai/math development (OpenAI, *The Euclidean plane cannot be colored with five colors*, OpenAI Math Release, September 23, 2026, result family 158, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 174 declarations of OpenAI's Lean: 97 definitions, 12 instances and 65 theorems. The definitions and types are `OAI.EuclideanFiveColor.ThreeLabelRegion`, `OAI.EuclideanFiveColor.VectorMeasure.cyclicIsometry`, `OAI.EuclideanFiveColor.VectorMeasure.cyclicMap`, `OAI.EuclideanFiveColor.VectorMeasure.functional`, `OAI.EuclideanFiveColor.VectorMeasure.measure`, `OAI.EuclideanFiveColor.VectorMeasure.realCM`, `OAI.EuclideanFiveColor.VectorMeasure.vectorLinear`, `OAI.EuclideanFiveColor.approxField`, `OAI.EuclideanFiveColor.approxIndex`, `OAI.EuclideanFiveColor.binaryB`, `OAI.EuclideanFiveColor.binaryBeta`, `OAI.EuclideanFiveColor.binaryCircleMap`, `OAI.EuclideanFiveColor.binaryConjugate`, `OAI.EuclideanFiveColor.binaryE`, `OAI.EuclideanFiveColor.binaryM`, `OAI.EuclideanFiveColor.binaryOther`, `OAI.EuclideanFiveColor.binaryPhi`, `OAI.EuclideanFiveColor.binaryQ`, `OAI.EuclideanFiveColor.binaryR`, `OAI.EuclideanFiveColor.binaryTarget`, `OAI.EuclideanFiveColor.certificateX`, `OAI.EuclideanFiveColor.certificateY`, `OAI.EuclideanFiveColor.circleOscillation`, `OAI.EuclideanFiveColor.closedCoverMap`, `OAI.EuclideanFiveColor.colorCutoff`, `OAI.EuclideanFiveColor.colorIndicator`, `OAI.EuclideanFiveColor.derivLowerOrderIso`, `OAI.EuclideanFiveColor.diskCone`, `OAI.EuclideanFiveColor.essentialLocalSet`, `OAI.EuclideanFiveColor.evenOffset`, `OAI.EuclideanFiveColor.evenPath`, `OAI.EuclideanFiveColor.fiveAdj`, `OAI.EuclideanFiveColor.fiveCanonical`, `OAI.EuclideanFiveColor.fiveDiag`, `OAI.EuclideanFiveColor.fourCanonical`, `OAI.EuclideanFiveColor.fourGroup`, `OAI.EuclideanFiveColor.graphDrop`, `OAI.EuclideanFiveColor.graphLift`, `OAI.EuclideanFiveColor.interfaceFourDiagonal`, `OAI.EuclideanFiveColor.iterComposition` and 57 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/PlaneColoring, in whole or in part: `CompactFactors_ConditionalLimits`, `PlaneColoring_BinaryDynamics`, `PlaneColoring_BinaryPalettes`, `PlaneColoring_BorelTransfer`, `PlaneColoring_CircleTransport`, `PlaneColoring_Compactness`, `PlaneColoring_DiskExtension`, `PlaneColoring_Exclusion`, `PlaneColoring_Expansion`, `PlaneColoring_FiveSupport`, `PlaneColoring_Interfaces`, `PlaneColoring_Moser`, `PlaneColoring_PaletteDensity`, `PlaneColoring_PaletteTransport`, `PlaneColoring_Rigidity`, `PlaneColoring_Sectors`, `PlaneColoring_States`, `PlaneColoring_WeakColoring`, `PlaneSpectrum_Characters`, `PlaneSpectrum_CircleDecay`, `PlaneSpectrum_CircleOperator`, `PlaneSpectrum_ConditionalSpectrum`, `PlaneSpectrum_Fourier`, `PlaneSpectrum_FourierTests`, `PlaneSpectrum_InvariantMean`, `PlaneSpectrum_Multipliers`, `PlaneSpectrum_Representations`, `PlaneSpectrum_SpectralMeasure`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ5T4002`.
-- source:
--   OpenAI, The Euclidean plane cannot be colored with five colors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 158; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/PlaneColoring at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ5_T4.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators
namespace PlaneFiveColor.ContinuousCharacters

/-- Canonical frequencies of the dyadic restrictions. -/
def frequency (X : ℕ → Circle) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * Complex.arg (X n : ℂ)

@[simp] theorem exp_frequency_div (X : ℕ → Circle) (n : ℕ) :
    Circle.exp (frequency X n / (2 : ℝ)^n) = X n := by
  rw [frequency, mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num)), Circle.exp_arg]

open MeasureTheory

def deviation (z : Circle) (k : ℕ) : ℝ := 1 - ((z : ℂ)^k).re

abbrev F := algebraicClosure ℚ ℝ

def dyadicApprox (t : F) (n : ℕ) : F :=
  (Int.floor ((2 : ℝ)^n * (t : ℝ)) : F) / (2 : F)^n

variable {Ω : Type*} [MeasurableSpace Ω]

def coeff (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle) (t : F) : ℝ :=
  ∫ x, deviation (χ x (Multiplicative.ofAdd t)) 1 ∂μ

@[simp] lemma coeff_zero (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle) :
    coeff μ χ 0 = 0 := by
  simp [coeff, deviation]

instance F_countable : Countable F := by
  apply Set.Countable.to_subtype
  have heq : (algebraicClosure ℚ ℝ : Set ℝ) = {x | IsAlgebraic ℚ x} := by
    ext z
    exact mem_algebraicClosure_iff
  rw [heq]
  exact Algebraic.countable ℚ ℝ

end PlaneFiveColor.ContinuousCharacters

end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_InvariantMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
/-! A discrete abelian invariant mean, constructed from weighted cube
averages. Repeated group elements keep their multiplicities. -/
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
namespace PlaneFiveColor.InvariantMean

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

def realPart (f : G →ᵇ ℂ) : G →ᵇ ℝ := Complex.reCLM.compLeftContinuousBounded G f

def imagPart (f : G →ᵇ ℂ) : G →ᵇ ℝ := Complex.imCLM.compLeftContinuousBounded G f

omit [AddCommGroup G] [DiscreteTopology G] in
@[simp] lemma realPart_apply (f : G →ᵇ ℂ) (x : G) : realPart f x = (f x).re := rfl
omit [AddCommGroup G] [DiscreteTopology G] in
@[simp] lemma imagPart_apply (f : G →ᵇ ℂ) (x : G) : imagPart f x = (f x).im := rfl

omit [AddCommGroup G] [DiscreteTopology G] in
lemma realPart_norm_le (f : G →ᵇ ℂ) : ‖realPart f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  exact (Complex.abs_re_le_norm (f x)).trans (f.norm_coe_le_norm x)

omit [AddCommGroup G] [DiscreteTopology G] in
lemma imagPart_norm_le (f : G →ᵇ ℂ) : ‖imagPart f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  exact (Complex.abs_im_le_norm (f x)).trans (f.norm_coe_le_norm x)

/-- Complex translation; no ordinary measurability is asserted or needed. -/
def cshift (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  f.compContinuous ⟨fun x => x + g, continuous_of_discreteTopology⟩

@[simp] lemma cshift_apply (g x : G) (f : G →ᵇ ℂ) : cshift g f x = f (x+g) := rfl

open MeasureTheory AddCircle

/-- Pullback along the dense algebraic circle embedding. -/
def circlePull (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => f (ρ x)) ‖f‖ (fun _x => f.norm_coe_le_norm _)

@[simp] lemma circlePull_apply (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) (x : G) :
    circlePull ρ f x = f (ρ x) := rfl

lemma circlePull_norm_le (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) :
    ‖circlePull ρ f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  exact fun x => f.norm_coe_le_norm _

/-- Normalized Haar integral on the ordinary circle. -/
def circleIntegral : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂haarAddCircle
      map_add' := by
        intro f h
        exact integral_add (BoundedContinuousFunction.mkOfCompact f |>.integrable _)
          (BoundedContinuousFunction.mkOfCompact h |>.integrable _)
      map_smul' := by intro c f; exact integral_smul c f }
    1 (by
      intro f
      change ‖∫ x, f x ∂haarAddCircle‖ ≤ 1 * ‖f‖
      simpa only [one_mul, BoundedContinuousFunction.norm_mkOfCompact, BoundedContinuousFunction.mkOfCompact_apply] using
        (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_norm haarAddCircle)

@[simp] lemma circleIntegral_apply (f : C(UnitAddCircle, ℂ)) :
    circleIntegral f = ∫ x, f x ∂haarAddCircle := rfl

/-- The real algebraic field and the literal discrete quotient F/Z. -/
abbrev AF := algebraicClosure ℚ ℝ

def PeriodGroup := AF ⧸ AddSubgroup.zmultiples (1 : AF) deriving AddCommGroup
instance instTopologicalSpacePeriodGroup : TopologicalSpace PeriodGroup := ⊥
instance instDiscreteTopologyPeriodGroup : DiscreteTopology PeriodGroup := ⟨rfl⟩

def periodMk : AF →+ PeriodGroup := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : AF))

/-- The ordinary circle quotient map, before passage to F/Z. -/
def fieldCircle : AF →+ UnitAddCircle :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
    (algebraicClosure ℚ ℝ).subtype.toAddMonoidHom

@[simp] lemma fieldCircle_apply (t : AF) : fieldCircle t = ((t : ℝ) : UnitAddCircle) := rfl

/-- F/Z embeds in the ordinary circle; no ordinary topology is imposed on its source. -/
def periodMap : PeriodGroup →+ UnitAddCircle :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : AF)) fieldCircle (by
    rw [AddSubgroup.zmultiples_le]
    change (((1 : AF) : ℝ) : UnitAddCircle) = 0
    exact (QuotientAddGroup.eq_zero_iff (1 : ℝ)).mpr (AddSubgroup.mem_zmultiples 1))

@[simp] lemma periodMap_apply (t : AF) :
    periodMap (QuotientAddGroup.mk t) = ((t : ℝ) : UnitAddCircle) := rfl

section WeakMean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Norm of a bounded vector field, still an arbitrary bounded function on
this discrete domain. -/
def normFn (V : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => ‖V x‖) ‖V‖ (fun x => by simpa only [norm_norm] using V.norm_coe_le_norm x)

omit [AddCommGroup G] [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] lemma normFn_apply (V : G →ᵇ H) (x : G) : normFn V x = ‖V x‖ := rfl

def pairing (V : G →ᵇ H) (v : H) : G →ᵇ ℝ :=
  (innerSL ℝ v).compLeftContinuousBounded G V

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
@[simp] lemma pairing_apply (V : G →ᵇ H) (v : H) (x : G) : pairing V v x = inner ℝ v (V x) := rfl

end WeakMean

section Periodization
variable {H : Type*} [NormedAddCommGroup H]

/-- Periodization is defined for all functions; bounded support below ensures
that these sums are finite and uniformly bounded. -/
def periodSum (h : AF → H) (t : AF) : H := ∑' k : ℤ, h (t + k)

lemma periodSum_periodic (h : AF → H) : Function.Periodic (periodSum h) 1 := by
  intro t
  unfold periodSum
  calc
    (∑' k : ℤ, h (t+1+k)) = ∑' k : ℤ, h (t+((k+1 : ℤ) : AF)) := by
      apply tsum_congr
      intro k
      congr 1
      push_cast
      ring
    _ = ∑' k : ℤ, h (t+k) := (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => h (t+k))

/-- Literal quotient-valued periodization. -/
def periodLift (h : AF → H) : PeriodGroup → H := (periodSum_periodic h).lift

@[simp] lemma periodLift_mk (h : AF → H) (t : AF) :
    periodLift h (QuotientAddGroup.mk t) = periodSum h t := rfl

/-- A uniform finite interval of integers contains all summands after the
argument has been moved to [0,1). -/
lemma period_term_zero {h : AF → H} {N : ℕ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    {t : AF} (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1) (k : ℤ)
    (hk : k ∉ Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)) : h (t+k) = 0 := by
  apply hs
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  change (N : ℝ) < |(t : ℝ)+(k : ℝ)|
  rcases hk with hk | hk
  · have hk' : (k : ℝ) < -(N : ℝ)-2 := by exact_mod_cast hk
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+2 < (k : ℝ) := by exact_mod_cast hk
    rw [abs_of_pos] <;> linarith

lemma periodSum_norm_le {h : AF → H} {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (t : AF) :
    ‖periodSum h t‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  let t' : AF := t - (⌊(t : ℝ)⌋ : ℤ)
  have ht0 : 0 ≤ (t' : ℝ) := Int.fract_nonneg (t : ℝ)
  have ht1 : (t' : ℝ) < 1 := Int.fract_lt_one (t : ℝ)
  have he : periodSum h t = periodSum h t' := by
    simpa only [t', mul_one] using
      ((periodSum_periodic h).sub_int_mul_eq (x := t) ⌊(t : ℝ)⌋).symm
  rw [he, periodSum, tsum_eq_sum (period_term_zero hs ht0 ht1)]
  calc
    _ ≤ ∑ k ∈ Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2), ‖h (t'+k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2), B :=
      Finset.sum_le_sum (fun k _ => hb (t'+k))
    _ = _ := by simp

/-- Every bounded, boundedly supported vector function has a bounded
periodization on the discrete quotient F/Z. -/
def periodBCF (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : PeriodGroup →ᵇ H :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (periodLift h)
    ((Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B) (fun x => by
      induction x using QuotientAddGroup.induction_on with
      | H t => exact periodSum_norm_le hs hb t)

@[simp] lemma periodBCF_mk (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (t : AF) :
    periodBCF h hs hb (QuotientAddGroup.mk t) = periodSum h t := rfl

end Periodization
section OrdinaryIntegral
open ContinuousMap TopologicalSpace

/-- The ordinary continuous periodic function associated with a test
function. Continuous-map summation agrees pointwise by local finiteness. -/
def ordinaryPeriod (f : C(ℝ, ℂ)) : C(UnitAddCircle, ℂ) :=
  ⟨(f.periodic_tsum_comp_add_zsmul 1).lift,
    continuous_coinduced_dom.mpr (map_continuous _)⟩

end OrdinaryIntegral

section Smoothing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (U : AF → H ≃ₗᵢ[ℝ] H)

omit [CompleteSpace H] in
lemma smoothed_support (φ : AF → ℝ) {N : ℕ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0) (v : H) :
    ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t • U t v = 0 := by
  intro t ht
  rw [hφ t ht, zero_smul]

omit [CompleteSpace H] in
lemma smoothed_bound (φ : AF → ℝ) {B : ℝ} (hb : ∀ t, |φ t| ≤ B) (v : H) :
    ∀ t, ‖φ t • U t v‖ ≤ B * ‖v‖ := by
  intro t
  rw [norm_smul, Real.norm_eq_abs, (U t).norm_map]
  exact mul_le_mul_of_nonneg_right (hb t) (norm_nonneg v)

end Smoothing
end PlaneFiveColor.InvariantMean
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Multipliers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
namespace PlaneFiveColor.LpMultiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma mul_memLp (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    MemLp (fun x => h x * v x) 2 μ := by
  apply (Lp.memLp v).of_le (hm.mul (Lp.aestronglyMeasurable v))
  exact Eventually.of_forall (fun x => by simp [hn])

def mul (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (mul_memLp h hm hn v).toLp _

lemma mul_ae (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    mul h hm hn v =ᵐ[μ] (fun x => h x * v x) := MemLp.coeFn_toLp _

lemma mul_norm (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    ‖mul h hm hn v‖ = ‖v‖ := by
  simp only [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [mul_ae h hm hn v] with x hx
  simp [hx, hn]

def mulIsometry (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) : Lp ℂ 2 μ →ₗᵢ[ℝ] Lp ℂ 2 μ where
  toFun := mul h hm hn
  map_add' v w := by
    apply Lp.ext
    filter_upwards [mul_ae h hm hn (v+w), mul_ae h hm hn v, mul_ae h hm hn w,
      Lp.coeFn_add v w, Lp.coeFn_add (mul h hm hn v) (mul h hm hn w)] with x ha hb hc hd he
    simp only [ha, hd, he, Pi.add_apply, hb, hc, mul_add]
  map_smul' r v := by
    apply Lp.ext
    filter_upwards [mul_ae h hm hn (r • v), mul_ae h hm hn v,
      Lp.coeFn_smul r v, Lp.coeFn_smul r (mul h hm hn v)] with x ha hb hc hd
    simp only [ha, hc, hd, Pi.smul_apply, hb, RingHom.id_apply, mul_smul_comm]
  norm_map' := mul_norm h hm hn

lemma mul_inverse (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    mul h hm hn (mul (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v) = v := by
  apply Lp.ext
  filter_upwards [mul_ae h hm hn (mul (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v),
    mul_ae (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v] with x hx hy
  rw [hx, hy, ← mul_assoc]
  have hh : h x * conj (h x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  rw [hh, one_mul]

def mulEquiv (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) : Lp ℂ 2 μ ≃ₗᵢ[ℝ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (mulIsometry h hm hn) (fun v =>
    ⟨mul (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v, mul_inverse h hm hn v⟩)

/-- Spectral weighting by a Hilbert vector, exactly |v|² μ. -/
def weight (v : Lp ℂ 2 μ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (‖v x‖^2))

instance weight_finite (v : Lp ℂ 2 μ) : IsFiniteMeasure (weight v) := by
  apply isFiniteMeasure_withDensity
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((Lp.aestronglyMeasurable v).norm.pow 2) (Eventually.of_forall (fun x => sq_nonneg ‖v x‖))).mpr
  exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)

end PlaneFiveColor.LpMultiplier

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_FourierTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace PlaneFiveColor.InvariantMean
open scoped BigOperators
open MeasureTheory Filter Topology

lemma weighted_bound (φ f : AF → ℝ) {B : ℝ}
    (hb : ∀ t, ‖φ t‖ ≤ B) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) :
    ∀ t, ‖φ t * f t‖ ≤ B := by
  intro t
  rw [norm_mul, Real.norm_of_nonneg (hf t).1]
  exact (mul_le_of_le_one_right (norm_nonneg _) (hf t).2).trans (hb t)

end PlaneFiveColor.InvariantMean

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_ConditionalSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

local instance instMeasurableSpaceCircle_solutions : MeasurableSpace Circle := borel Circle

end

end PlaneFiveColor.Spectral

namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance instMeasurableSpaceCircle_solutions_1 : MeasurableSpace Circle := borel Circle

abbrev MomentTest (M N : ℕ) := Fin N × {p : Fin M × Fin M // p.1 ≠ p.2}

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance instMeasurableSpaceCircle_solutions_2 : MeasurableSpace Circle := borel Circle

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_ConditionalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! Bounded finite-dimensional L² approximation at a generated limit factor.
The filtration is the pullback of an increasing sequence of earlier factors;
no martingale convergence theorem beyond Mathlib is assumed. -/

namespace PlaneFiveColor.Spectral

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
local instance instMeasurableSpaceCircle_solutions_3 : MeasurableSpace Circle := borel Circle

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
def iterComposition (f : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => id
  | n+1 => fun x => f n (iterComposition f n x)
def iterDerivative (f D : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n+1 => fun x => D n (iterComposition f n x)*iterDerivative f D n x
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BinaryDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
def binaryQ (d t : ℝ) : ℝ := 1-2*d*Real.cos t+d^2
def binaryR (d t : ℝ) : ℝ := 2*Real.sqrt (binaryQ d t)*Real.sqrt (1-binaryQ d t/4)
def binaryB (d t : ℝ) : ℝ := (Real.cos t-d)/binaryQ d t+Real.sin t/binaryR d t
def binaryM (d t : ℝ) : ℝ := Real.sin t/binaryQ d t+(d-Real.cos t)/binaryR d t
def binaryCircleMap (d t : ℝ) : ℝ :=
  t+Real.pi/3+Real.arctan (d*Real.sin t/(1-d*Real.cos t))-Real.arccos (Real.sqrt (binaryQ d t)/2)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
def binaryE (d t : ℝ) : ℝ := fderiv ℝ (fun q : ℝ × ℝ => binaryB q.1 q.2) (d,t) (0,1)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace EuclideanFiveColor
def binaryConjugate (d : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  binaryCircleMap d (t+(n : ℝ)*(Real.pi/3))-(n : ℝ)*(Real.pi/3)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CircleTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
def binaryPhi (d t : ℝ) : ℝ := t+Real.arctan (d*Real.sin t/(1-d*Real.cos t))
def binaryBeta (d t : ℝ) : ℝ := Real.arccos (Real.sqrt (binaryQ d t)/2)
def binaryTarget (d t : ℝ) : ℝ := -binaryCircleMap d (-t)+Real.pi/3
def binaryOther (d t : ℝ) : ℝ := binaryCircleMap d t+2*(Real.pi/3)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma deriv_lower_surjective {f D : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (D x) x)
    (hp : ∀ x, (1/2 : ℝ) ≤ D x) : Function.Surjective f := by
  intro y
  let R := 2*(|y-f 0|+1)
  have hR : 0 < R := by dsimp [R]; positivity
  have h₁ := mul_sub_le_image_sub_of_le_deriv (fun x => (hd x).differentiableAt)
    (fun x => by rw [(hd x).deriv]; exact hp x) (show -R ≤ 0 by linarith)
  have h₂ := mul_sub_le_image_sub_of_le_deriv (fun x => (hd x).differentiableAt)
    (fun x => by rw [(hd x).deriv]; exact hp x) hR.le
  have hy : y ∈ Icc (f (-R)) (f R) := by
    constructor <;> dsimp [R] at * <;> linarith [le_abs_self (y-f 0),neg_abs_le (y-f 0)]
  obtain ⟨x,_,hx⟩ := intermediate_value_Icc (by linarith : -R ≤ R)
    (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).continuousOn hy
  exact ⟨x,hx⟩
def derivLowerOrderIso {f D : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (D x) x)
    (hp : ∀ x, (1/2 : ℝ) ≤ D x) : ℝ ≃o ℝ :=
  (strictMono_of_deriv_pos (fun x => by rw [(hd x).deriv]; linarith [hp x])).orderIsoOfRightInverse f
    (Function.surjInv (deriv_lower_surjective hd hp)) (Function.rightInverse_surjInv (deriv_lower_surjective hd hp))
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_WeakColoring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
def truncatedClass (i : Fin k) (n : ℕ) : Set ℂ := {z | c z=i} ∩ Metric.closedBall 0 n
include hc
lemma truncatedClass_measurable (i : Fin k) (n : ℕ) : MeasurableSet (truncatedClass c i n) :=
  (measurableSet_eq_fun hc measurable_const).inter measurableSet_closedBall
omit hc in
lemma truncatedClass_finite (i : Fin k) (n : ℕ) : volume (truncatedClass c i n) ≠ ⊤ := by
  exact ne_top_of_le_ne_top ((isCompact_closedBall (0 : ℂ) (n : ℝ)).measure_ne_top)
    (measure_mono Set.inter_subset_right)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Compactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
instance instFactNeENNRealOfNatTop_solutions : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Fourier
attribute [-instance] _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
def planePhase (h ξ : ℂ) : ℂ := Real.fourierChar (inner ℝ h ξ)
lemma planePhase_norm (h ξ : ℂ) : ‖planePhase h ξ‖=1 := Circle.norm_coe _
lemma planePhase_continuous (h : ℂ) : Continuous (planePhase h) := by
  unfold planePhase
  fun_prop

def schwartzTranslate (h : ℂ) : SchwartzMap ℂ ℂ →L[ℂ] SchwartzMap ℂ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const h)) (isometry_add_right h).antilipschitz
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_CircleDecay
attribute [-instance] _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
def circleOscillation (r t : ℝ) : ℂ := Complex.exp ((r*Real.cos t : ℝ)*Complex.I)
end EuclideanFiveColor

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_CircleOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
def colorCutoff {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (x : ℂ) (R : ℝ) : ℂ → ℂ :=
  (Metric.closedBall x (R+2)).indicator (fun q => if c q=i then 1 else 0)
lemma colorCutoff_memLp {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (i : Fin k) (x : ℂ) (R : ℝ) :
    MemLp (colorCutoff c i x R) 2 volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall x (R+2))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall x (R+2)).measure_lt_top (μ := volume)⟩
  have hm : MeasureTheory.MemLp (fun q : ℂ => if c q=i then (1:ℂ) else 0) 2
      (volume.restrict (Metric.closedBall x (R+2))) := by
    apply MemLp.of_bound ((measurable_one.piecewise (measurableSet_eq_fun hc measurable_const)
      measurable_zero).aestronglyMeasurable) 1
    exact Eventually.of_forall fun q => by simp only [Set.piecewise]; split_ifs <;> simp
  exact (memLp_indicator_iff_restrict measurableSet_closedBall).mpr hm
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PaletteDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
def colorIndicator (i : Fin k) (z : ℂ) : ℝ := if c z=i then 1 else 0
end EuclideanFiveColor

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PaletteTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Topology Set MeasureTheory
namespace EuclideanFiveColor
def sixty : ℝ := Real.pi/3
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BinaryPalettes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
def triangleAngle : ℝ := Real.arccos (5/6)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Representations
attribute [-instance] _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace EuclideanFiveColor.VectorMeasure
variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
def realCM (f : C(X,ℝ)) : C(X,ℂ) := ⟨fun x => (f x : ℂ),by fun_prop⟩
@[simp] lemma realCM_apply (f : C(X,ℝ)) (x : X) : realCM f x = (f x : ℂ) := rfl
@[simp] lemma realCM_add (f g : C(X,ℝ)) : realCM (f+g) = realCM f+realCM g := by ext; simp
@[simp] lemma realCM_sub (f g : C(X,ℝ)) : realCM (f-g) = realCM f-realCM g := by ext; simp
@[simp] lemma realCM_smul (c : ℝ) (f : C(X,ℝ)) : realCM (c • f) = (c:ℂ) • realCM f := by ext; simp
@[simp] lemma realCM_one : realCM (1:C(X,ℝ)) = 1 := by ext; simp
variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma real_nonneg (f : C(X,ℝ)) (hf : 0 ≤ f) : 0 ≤ (⟪v, Φ (realCM f) v⟫_ℂ).re := by
  let g : C(X,ℂ) := realCM ⟨fun x => Real.sqrt (f x),by fun_prop⟩
  have he : star g * g = realCM f := by
    ext x
    simp only [ContinuousMap.mul_apply,ContinuousMap.star_apply,realCM_apply,g,ContinuousMap.coe_mk,Complex.star_def,Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    exact congrArg Complex.ofReal (Real.mul_self_sqrt (show 0 ≤ f x from hf x))
  rw [← he,map_mul,map_star]
  change 0 ≤ (⟪v, (star (Φ g)) ((Φ g) v)⟫_ℂ).re
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (x := (Φ g) v)

def functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := (⟪v,Φ (realCM f.toContinuousMap) v⟫_ℂ).re
  map_add' f g := by
    change (⟪v,Φ (realCM (f.toContinuousMap+g.toContinuousMap)) v⟫_ℂ).re = _
    simp
  map_smul' c f := by
    change (⟪v,Φ (realCM (c • f.toContinuousMap)) v⟫_ℂ).re = c * _
    rw [realCM_smul,map_smul]
    simp only [FunLike.coe_smul,Pi.smul_apply,inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  monotone' f g hfg := by
    have he := real_nonneg Φ v (g.toContinuousMap-f.toContinuousMap) (sub_nonneg.mpr hfg)
    simpa [inner_sub_right] using he

def measure : Measure X := RealRMK.rieszMeasure (functional Φ v)
instance instIsFiniteMeasureMeasure : IsFiniteMeasure (measure Φ v) := by dsimp [measure]; infer_instance
instance instRegularMeasure : (measure Φ v).Regular := by dsimp [measure]; infer_instance
lemma integral_real (f : C(X,ℝ)) : ∫ x, f x ∂measure Φ v = (⟪v,Φ (realCM f) v⟫_ℂ).re := by
  exact RealRMK.integral_rieszMeasure (functional Φ v) (CompactlySupportedContinuousMap.continuousMapEquiv f)
lemma integral_complex (f : C(X,ℂ)) : ∫ x, f x ∂measure Φ v = ⟪v,Φ f v⟫_ℂ := by
  let fr : C(X,ℝ) := ⟨fun x => (f x).re,by fun_prop⟩
  let fi : C(X,ℝ) := ⟨fun x => (f x).im,by fun_prop⟩
  have he : f = realCM fr + Complex.I • realCM fi := by
    ext x
    simpa [fr,fi,smul_eq_mul,mul_comm] using (Complex.re_add_im (f x)).symm
  have hi_real (g : C(X,ℝ)) : (⟪v,Φ (realCM g) v⟫_ℂ).im = 0 := by
    have hs : star (Φ (realCM g)) = Φ (realCM g) := by
      rw [← map_star]; congr 1; ext x; simp
    have ht := inner_conj_symm (𝕜 := ℂ) v (Φ (realCM g) v)
    rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,hs] at ht
    have hh := congrArg Complex.im ht
    simp only [Complex.conj_im] at hh
    linarith
  have hb (g : C(X,ℝ)) : ∫ x, (g x : ℂ) ∂measure Φ v = ⟪v,Φ (realCM g) v⟫_ℂ := by
    rw [integral_complex_ofReal,integral_real]
    exact Complex.ext (by simp) (by simp [hi_real])
  rw [he,map_add,map_smul]
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,realCM_apply,add_apply,
    smul_apply,inner_add_right,inner_smul_right]
  have hir : Integrable (fun x => (fr x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fr.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hii : Integrable (fun x => (fi x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fi.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = (∫ x, (fr x : ℂ) ∂measure Φ v) +
        (∫ x, Complex.I • (fi x : ℂ) ∂measure Φ v) := integral_add hir (hii.smul Complex.I)
    _ = _ := by rw [integral_smul,hb,hb]; rfl
end EuclideanFiveColor.VectorMeasure
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_SpectralMeasure
attribute [-instance] _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace EuclideanFiveColor.VectorMeasure
variable {X H : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
lemma inner_toLp (f g : C(X,ℂ)) :
    ⟪ContinuousMap.toLp 2 (measure Φ v) ℂ f, ContinuousMap.toLp 2 (measure Φ v) ℂ g⟫_ℂ =
      ⟪Φ f v,Φ g v⟫_ℂ := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, (star f*g) x ∂measure Φ v := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (μ := measure Φ v) (p := 2) (𝕜 := ℂ) f,
        ContinuousMap.coeFn_toLp (μ := measure Φ v) (p := 2) (𝕜 := ℂ) g] with x hx hy
      simp only [hx,hy,RCLike.inner_apply,ContinuousMap.mul_apply,ContinuousMap.star_apply,Complex.star_def]
      ring
    _ = ⟪v,Φ (star f*g) v⟫_ℂ := integral_complex Φ v _
    _ = _ := by
      rw [map_mul,map_star]
      change ⟪v,star (Φ f) (Φ g v)⟫_ℂ = _
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
def vectorLinear : C(X,ℂ) →ₗ[ℂ] H where
  toFun f := Φ f v
  map_add' f g := by simp
  map_smul' c f := by simp
lemma norm_toLp (f : C(X,ℂ)) :
    ‖ContinuousMap.toLp 2 (measure Φ v) ℂ f‖ = ‖vectorLinear Φ v f‖ := by
  have he := congrArg Complex.re (inner_toLp Φ v f f)
  change RCLike.re (⟪ContinuousMap.toLp 2 (measure Φ v) ℂ f,ContinuousMap.toLp 2 (measure Φ v) ℂ f⟫_ℂ) =
    RCLike.re (⟪Φ f v,Φ f v⟫_ℂ) at he
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he
def cyclicMap : Lp ℂ 2 (measure Φ v) →L[ℂ] H :=
  (vectorLinear Φ v).extendOfNorm (ContinuousMap.toLp 2 (measure Φ v) ℂ).toLinearMap
lemma cyclicMap_toLp (f : C(X,ℂ)) :
    cyclicMap Φ v (ContinuousMap.toLp 2 (measure Φ v) ℂ f) = Φ f v := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)
  · exact ⟨1,fun g => by simp only [one_mul]; exact le_of_eq (norm_toLp Φ v g).symm⟩
lemma norm_cyclicMap (f : Lp ℂ 2 (measure Φ v)) : ‖cyclicMap Φ v f‖ = ‖f‖ := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)).induction
    (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) f
  obtain ⟨g,rfl⟩ := hy
  rw [cyclicMap_toLp]
  exact (norm_toLp Φ v g).symm
def cyclicIsometry : Lp ℂ 2 (measure Φ v) →ₗᵢ[ℂ] H :=
  ⟨(cyclicMap Φ v).toLinearMap,norm_cyclicMap Φ v⟩
end EuclideanFiveColor.VectorMeasure
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BorelTransfer
attribute [-instance] _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal
namespace EuclideanFiveColor
variable {T X : Type*} [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
  [MeasurableSpace T] [BorelSpace T] [MeasurableSpace X] (μ : Measure X)
  (f : T → Lp ℂ 2 μ) (hf : Continuous f)
include hf
omit [MeasurableSpace T] [BorelSpace T] in
lemma dense_approx (t : T) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, dist (f (TopologicalSpace.denseSeq T n)) (f t) < ε := by
  have h := mem_closure_image hf.continuousAt (TopologicalSpace.denseRange_denseSeq T t)
  rw [← Set.range_comp] at h
  obtain ⟨n,hn⟩ := Metric.mem_closure_range_iff.mp h ε hε
  exact ⟨n,by simpa only [Function.comp_apply,dist_comm] using hn⟩
def approxIndex (n : ℕ) (t : T) : ℕ := Nat.find (dense_approx μ f hf t ((1/2:ℝ)^n) (by positivity))
def approxField (n : ℕ) (p : T × X) : ℂ :=
  f (TopologicalSpace.denseSeq T (approxIndex μ f hf n p.1)) p.2
def measurableField (p : T × X) : ℂ :=
  ⟨limsup (fun n => (approxField μ f hf n p).re) atTop,
   limsup (fun n => (approxField μ f hf n p).im) atTop⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] {k : ℕ} [NeZero k]
def positiveSupport (f : Fin k → X → ℝ) (x : X) : Finset (Fin k) := Finset.univ.filter fun i => 0 < f i x
def pickSupport (s : Finset (Fin k)) : Fin k := if h : s.Nonempty then h.choose else 0
def positiveSelect (f : Fin k → X → ℝ) (x : X) : Fin k := pickSupport (positiveSupport f x)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Rigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
/-- Common unit neighbor for the transverse chord of length `t`. -/
def evenOffset (v : ℂ) (t : ℝ) : ℂ :=
  ((Real.sqrt (1-t^2/4) : ℂ)+((t/2 : ℝ) : ℂ)*Complex.I)*v
@[fun_prop] lemma continuous_evenOffset (v : ℂ) : Continuous (evenOffset v) := by
  unfold evenOffset
  fun_prop
def transverseDet (v w : ℂ) : ℝ :=
  (Complex.I*v).re*(Complex.I*w).im-(Complex.I*w).re*(Complex.I*v).im
def transverseFirst (v w h : ℂ) : ℝ :=
  (h.re*(Complex.I*w).im-(Complex.I*w).re*h.im)/transverseDet v w
def transverseSecond (v w h : ℂ) : ℝ :=
  ((Complex.I*v).re*h.im-h.re*(Complex.I*v).im)/transverseDet v w
@[fun_prop] lemma continuous_transverseFirst (v w : ℂ) : Continuous (transverseFirst v w) := by
  unfold transverseFirst
  fun_prop
@[fun_prop] lemma continuous_transverseSecond (v w : ℂ) : Continuous (transverseSecond v w) := by
  unfold transverseSecond
  fun_prop
def evenPath (v w h : ℂ) : Fin 5 → ℂ := ![0,
  evenOffset v (transverseFirst v w h),
  (transverseFirst v w h : ℂ)*(Complex.I*v),
  (transverseFirst v w h : ℂ)*(Complex.I*v)+evenOffset w (transverseSecond v w h),h]
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
def radialSide (b : Bool) (ε : ℝ) : Set ℝ := if b then Ioo 1 (1+ε) else Ioo (1-ε) 1
def polarBox (x e : ℂ) (b : Bool) (ε : ℝ) : Set ℂ :=
  (fun rt : ℝ × ℝ => x+(rt.1:ℂ)*(e*(Circle.exp rt.2 : ℂ))) ''
    (radialSide b ε ×ˢ Ioo (-ε) ε)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Points having a fixed essential color on some ambient neighborhood. -/
def essentialLocalSet {ι : Type*} (c : ℂ → ι) (i : ι) : Set ℂ :=
  {p | ∃U : Set ℂ,IsOpen U ∧ p∈U ∧ ∀ᵐq : ℂ∂volume,q∈U → c q=i}
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_States
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
def fourGroup (s : Fin 3) : Finset (Fin 5) := if s=0 then {4} else if s=1 then {0,2} else {1,3}
def fourCanonical (p : Finset (Fin 5)) : Fin 3 := if 4∈p then 0 else if 0∈p then 1 else 2
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Exclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
def fiveDiag (i : Fin 5) : Finset (Fin 5) := {i,i+2}
def fiveAdj (i j : Fin 5) : Prop := i+1=j ∨ j+1=i
instance instDecidableFiveAdj (i j : Fin 5) : Decidable (fiveAdj i j) := inferInstanceAs (Decidable (_ ∨ _))
def fiveCanonical (p : Finset (Fin 5)) : Fin 5 :=
  if p=fiveDiag 0 then 0 else if p=fiveDiag 1 then 1 else if p=fiveDiag 2 then 2 else
    if p=fiveDiag 3 then 3 else 4
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FiveSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
def stateSupport (f : ℝ → ι) (i : ι) : Set ℝ := (volume.restrict {t | f t=i}).support
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_DiskExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
lemma cone_dist (c : ℂ) {r : ℝ} (z : Metric.sphere c r) (t : unitInterval) :
    dist ((1-t.val) • (z.val-c)+c) c=(1-t.val)*r := by
  rw [dist_eq_norm,add_sub_cancel_right,norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr t.property.2)]
  rw [←dist_eq_norm,z.property]
def diskCone (c : ℂ) {r : ℝ} (hr : 0 < r) :
    C(unitInterval × Metric.sphere c r, Metric.closedBall c r) where
  toFun p := ⟨(1-p.1.val) • (p.2.val-c)+c,by
    change dist ((1-p.1.val) • (p.2.val-c)+c) c ≤ r
    rw [cone_dist]
    nlinarith [p.1.property.1]⟩
  continuous_toFun := (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    ((continuous_subtype_val.comp continuous_snd).sub continuous_const)).add continuous_const).subtype_mk _
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
universe u
namespace EuclideanFiveColor

def graphDrop {V : Type u} (v : V) (p : V → ℝ) : {i : V // i≠v} → ℝ := fun i => p i

def graphLift {V : Type u} (v : V) (p : {i : V // i≠v} → ℝ) : V → ℝ :=
  fun i => if hi : i≠v then p ⟨i,hi⟩ else 0
lemma continuous_graphDrop {V : Type u} (v : V) : Continuous (graphDrop v) :=
  continuous_pi fun i => continuous_apply i.val
lemma continuous_graphLift {V : Type u} (v : V) : Continuous (graphLift v) := by
  apply continuous_pi
  intro i
  by_cases hi : i≠v
  · simpa [graphLift,hi] using (continuous_apply (⟨i,hi⟩ : {i : V // i≠v}))
  · simpa [graphLift,hi] using (continuous_const : Continuous (fun _ : ({i : V // i≠v} → ℝ) => (0:ℝ)))
@[simp] lemma graphLift_drop {V : Type u} (v : V) (p : V → ℝ) (hp : p v=0) :
    graphLift v (graphDrop v p)=p := by
  ext i
  by_cases hi : i=v
  · subst i; simp [graphLift,hp]
  · simp [graphLift,graphDrop,hi]
@[simp] lemma graphDrop_lift {V : Type u} (v : V) (p : {i : V // i≠v} → ℝ) :
    graphDrop v (graphLift v p)=p := by
  ext i; simp [graphDrop,graphLift,i.property]
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u v w
namespace EuclideanFiveColor
/-- Finite closed-cover pasting, with the actual glued continuous map. -/
def closedCoverMap {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    (S : ι → Set X) (hS : ∀i,IsClosed (S i)) (hc : ⋃i,S i=univ)
    (f : ∀i,C(S i,Y))
    (hf : ∀i j x (hi : x∈S i) (hj : x∈S j), f i ⟨x,hi⟩=f j ⟨x,hj⟩) : C(X,Y) where
  toFun := Set.liftCover S (fun i => f i) hf hc
  continuous_toFun := (locallyFinite_of_finite S).continuous hc hS (fun i => by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa +unfoldPartialApp only [Set.domRestrict,Set.liftCover_coe] using (f i).continuous)
@[simp] lemma closedCoverMap_apply {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    (S : ι → Set X) (hS : ∀i,IsClosed (S i)) (hc : ⋃i,S i=univ)
    (f : ∀i,C(S i,Y))
    (hf : ∀i j x (hi : x∈S i) (hj : x∈S j), f i ⟨x,hi⟩=f j ⟨x,hj⟩)
    {i : ι} (x : S i) : closedCoverMap S hS hc f hf x=f i x := by
  change Set.liftCover S (fun i => f i) hf hc x=f i x
  exact Set.liftCover_coe x
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Interfaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
def interfaceFourDiagonal (s : Fin 4 → Bool) : Fin 3 := if s 0=s 1 then 2 else 1
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Moser
attribute [-instance] _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace EuclideanFiveColor
def ThreeLabelRegion (x y : ℝ) : Prop :=
  0<x^2+y^2 ∧ x^2+y^2<4 ∧
    y^2*(3*x^2-y^2)^2 < (x^2+y^2)^3*(1-(x^2+y^2)/4)*(x^2+y^2-1)^2
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
def moserA : ℂ := ((Real.sqrt 3 : ℂ)+Complex.I)/2
def moserB : ℂ := ((Real.sqrt 3 : ℂ)-Complex.I)/2
def moserT : ℂ := Real.sqrt 3
def moserU : ℂ := (5+Complex.I*(Real.sqrt 11 : ℂ))/6
def moserPoint : Fin 7 → ℂ := ![0,moserA,moserB,moserT,moserU*moserA,moserU*moserB,moserU*moserT]
@[simp] lemma moserPoint_0 : moserPoint 0=0 := rfl
@[simp] lemma moserPoint_1 : moserPoint 1=moserA := rfl
@[simp] lemma moserPoint_2 : moserPoint 2=moserB := rfl
@[simp] lemma moserPoint_3 : moserPoint 3=moserT := rfl
@[simp] lemma moserPoint_4 : moserPoint 4=moserU*moserA := rfl
@[simp] lemma moserPoint_5 : moserPoint 5=moserU*moserB := rfl
@[simp] lemma moserPoint_6 : moserPoint 6=moserU*moserT := rfl
def moserEdges : Finset (Fin 7 × Fin 7) :=
  {(0,1),(0,2),(1,2),(3,1),(3,2),(0,4),(0,5),(4,5),(6,4),(6,5),(3,6)}
def moserRotation : ℂ := (35+12*Complex.I)/37
def placedMoser (i : Fin 7) : ℂ := moserRotation*(moserPoint i+(-290+149*Complex.I)/250)
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
def certificateX : Fin 7 → ℝ := ![-1.2906,-0.6335,-0.3092,0.3478,-1.1598,-0.3666,-0.2358]
def certificateY : Fin 7 → ℝ := ![0.1876,0.9414,-0.0045,0.7493,1.1790,0.5700,1.5614]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Sectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
def triangleEdge (i : Fin 3) : Finset (Fin 5) := if i=0 then {0,1} else if i=1 then {1,2} else {2,0}
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
def positiveSector (φ : ℝ) : Set ℝ := {t | 0<Real.sin (3*(t-φ))}
def negativeSector (φ : ℝ) : Set ℝ := {t | Real.sin (3*(t-φ))<0}
end EuclideanFiveColor
end

end OAI
end


