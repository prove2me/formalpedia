-- Prove2me | Definitions.Def_OAIQ3Ho001
-- name    : OAIQ3Ho001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T05:01:11.73725+00:00
-- url     : https://prove2.me/theorems/f04b0094-6ae0-4161-9ad1-1d605451513d
-- title:
--   Definitions bundle OAIQ3Ho001 of the split of OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 146 declarations of OpenAI's Lean: 65 definitions, 2 inductive types or structures, 6 instances and 73 theorems. The definitions and types are `OAI.StrictHotSpots.DirichletOperator.green`, `OAI.StrictHotSpots.DirichletOperator.solution`, `OAI.StrictHotSpots.DiskCompact.regularizationParameter`, `OAI.StrictHotSpots.DiskCutoff.cutoff`, `OAI.StrictHotSpots.DiskFormula.boundaryInteraction`, `OAI.StrictHotSpots.DiskFormula.green`, `OAI.StrictHotSpots.DiskFormula.logRatio`, `OAI.StrictHotSpots.DiskFormula.poisson`, `OAI.StrictHotSpots.DiskKernel.Disk`, `OAI.StrictHotSpots.DiskKernel.f`, `OAI.StrictHotSpots.DiskKernel.green`, `OAI.StrictHotSpots.DiskKernel.h`, `OAI.StrictHotSpots.DiskKernel.logMean`, `OAI.StrictHotSpots.DiskKernel.regularized`, `OAI.StrictHotSpots.Douglas.imagDatum`, `OAI.StrictHotSpots.GreenFundamental.direction`, `OAI.StrictHotSpots.GreenFundamental.logRegularized`, `OAI.StrictHotSpots.GreenFundamental.peak`, `OAI.StrictHotSpots.GreenLp.logPole`, `OAI.StrictHotSpots.GreenPotential.correctionIntegrand`, `OAI.StrictHotSpots.GreenPotential.potential`, `OAI.StrictHotSpots.Helmholtz.WeakEquation`, `OAI.StrictHotSpots.Helmholtz.angularDeriv`, `OAI.StrictHotSpots.Helmholtz.angularSecond`, `OAI.StrictHotSpots.Helmholtz.circleFunction`, `OAI.StrictHotSpots.Helmholtz.coeff`, `OAI.StrictHotSpots.Helmholtz.coeffDeriv`, `OAI.StrictHotSpots.Helmholtz.coeffSecond`, `OAI.StrictHotSpots.Helmholtz.direction`, `OAI.StrictHotSpots.Helmholtz.mollifier`, `OAI.StrictHotSpots.Helmholtz.radial`, `OAI.StrictHotSpots.Helmholtz.radialDeriv`, `OAI.StrictHotSpots.Helmholtz.radialSecond`, `OAI.StrictHotSpots.Helmholtz.reference`, `OAI.StrictHotSpots.Helmholtz.referenceReal`, `OAI.StrictHotSpots.Helmholtz.referenceSin`, `OAI.StrictHotSpots.Helmholtz.smoothen`, `OAI.StrictHotSpots.Helmholtz.smulFlip`, `OAI.StrictHotSpots.Helmholtz.weight`, `OAI.StrictHotSpots.HilbertMultipliers.vanishingOn` and 27 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/HotSpots, in whole or in part: `HotSpots_BoundaryEnergy`, `HotSpots_BoundaryKernel`, `HotSpots_Dirichlet`, `HotSpots_DiskKernel`, `HotSpots_DouglasEnergy`, `HotSpots_Eigenfunction`, `HotSpots_Green`, `HotSpots_GreenOperator`, `HotSpots_GreenSolution`, `HotSpots_Helmholtz`, `HotSpots_KernelLimit`, `HotSpots_Multiplicity`, `HotSpots_Multiplier`, `HotSpots_Potentials`, `HotSpots_Riemann`, `HotSpots_Sobolev`, `HotSpots_TraceRank`.
--
--   **Imports.** It imports the published bundle `Def_HotSpots`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ3Ho002` and `OAIQ3Ho003`; the proof of `OAI.StrictHotSpots.CircleSigns.disk_family_finrank_le_two`.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/HotSpots at commit adc7f12

import Mathlib
import Definitions.Def_HotSpots

section
-- module Solutions.OAIQ3_Hot.Compat
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
-- module Solutions.OAIQ3_Hot.HotSpots_DiskKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section DiskFiniteLayer

open Filter Matrix
open scoped Topology
namespace StrictHotSpots.ScalarKernel

def coeff (a : ℝ) (n : ℕ) : ℝ := -(Ring.choose a (n + 2) * (-1) ^ (n + 2))


def dilation (n : ℕ) : ℝ := 1 - ((n : ℝ) + 2)⁻¹

lemma invLog_continuousAt_zero : ContinuousAt (fun x : ℝ => (Real.log x)⁻¹) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simpa only [one_div, Real.log_zero, _root_.inv_zero] using
    Real.tendsto_log_nhdsNE_zero.const_div_atBot 1

end StrictHotSpots.ScalarKernel





open Matrix Filter _root_.Complex
open scoped Topology ComplexOrder ENNReal
namespace StrictHotSpots.DiskKernel

abbrev Disk := {z : ℂ // ‖z‖ < 1}

def h (x y : Disk) : ℝ :=
  ‖(x : ℂ) - y‖ ^ 2 / ((1 - ‖(x : ℂ)‖ ^ 2) * (1 - ‖(y : ℂ)‖ ^ 2))

def logMean (t : ℝ) : ℝ := (Real.log (1 + 1 / t))⁻¹

def f (t : ℝ) : ℝ := t + 1 / 2 - logMean t


def green (x y : Disk) : ℝ :=
  (4 * Real.pi)⁻¹ * Real.log (1 + 1 / h x y)


def regularized (ε : ℝ) (x y : Disk) : ℝ :=
  (4 * Real.pi * (h x y + 1 / 2 - (1 - ε) * f (h x y)))⁻¹

lemma disk_weight_pos (x : Disk) : 0 < 1 - ‖(x : ℂ)‖ ^ 2 := by
  have hn := norm_nonneg (x : ℂ)
  have hx := x.property
  nlinarith

lemma h_nonneg (x y : Disk) : 0 ≤ h x y :=
  div_nonneg (sq_nonneg _) (mul_pos (disk_weight_pos x) (disk_weight_pos y)).le

@[simp] lemma h_self (x : Disk) : h x x = 0 := by simp [h]
@[simp] lemma logMean_zero : logMean 0 = 0 := by simp [logMean]
@[simp] lemma f_zero : f 0 = 1 / 2 := by simp [f]

end StrictHotSpots.DiskKernel

namespace StrictHotSpots.DiskKernel

lemma logMean_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ logMean t := by
  apply inv_nonneg.mpr
  exact Real.log_nonneg (by have := one_div_nonneg.mpr ht; linarith)

end StrictHotSpots.DiskKernel

namespace StrictHotSpots.DiskKernel

lemma f_alt (t : ℝ) : f t = t + 1 / 2 + (Real.log (t / (1 + t)))⁻¹ := by
  by_cases ht : t = 0
  · subst t
    norm_num [f, logMean]
  · have he : 1 + 1 / t = (t / (1 + t))⁻¹ := by
      rw [inv_div]
      field_simp
      ring
    rw [f, logMean, he, Real.log_inv, inv_neg]
    ring

lemma f_continuousAt {t : ℝ} (ht : 0 ≤ t) : ContinuousAt f t := by
  rw [show f = fun t => t + 1 / 2 + (Real.log (t / (1 + t)))⁻¹ from funext f_alt]
  apply (continuousAt_id.add continuousAt_const).add
  have hden : 1 + t ≠ 0 := by positivity
  have hquot : ContinuousAt (fun t : ℝ => t / (1 + t)) t :=
    continuousAt_id.div (continuousAt_const.add continuousAt_id) hden
  rcases eq_or_lt_of_le ht with he | hp
  · subst t
    exact ScalarKernel.invLog_continuousAt_zero.comp_of_eq hquot (by simp)
  · have hq : 0 < t / (1 + t) := div_pos hp (by positivity)
    have hql : t / (1 + t) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    exact ((Real.continuousAt_log hq.ne').comp (f := fun t : ℝ => t / (1 + t)) hquot).inv₀
      (ne_of_lt (Real.log_neg hq hql))

lemma h_continuous : Continuous (fun p : Disk × Disk => h p.1 p.2) := by
  apply ((continuous_subtype_val.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd)).norm.pow 2 |>.div
  · exact (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).norm.pow 2)).mul
      (continuous_const.sub ((continuous_subtype_val.comp continuous_snd).norm.pow 2))
  · intro p
    exact (mul_pos (disk_weight_pos p.1) (disk_weight_pos p.2)).ne'

lemma regularized_denominator {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x y : Disk) :
    ε / 2 ≤ h x y + 1 / 2 - (1 - ε) * f (h x y) := by
  have ht := h_nonneg x y
  have hl := logMean_nonneg ht
  have he : h x y + 1 / 2 - (1 - ε) * f (h x y) =
      ε * (h x y + 1 / 2) + (1 - ε) * logMean (h x y) := by
    dsimp [f]; ring
  rw [he]
  nlinarith [mul_nonneg hε.le ht, mul_nonneg (sub_nonneg.mpr hε1) hl]

lemma regularized_continuous {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Continuous (fun p : Disk × Disk => regularized ε p.1 p.2) := by
  have hf : Continuous (fun p : Disk × Disk => f (h p.1 p.2)) :=
    continuous_iff_continuousAt.mpr fun p =>
      (f_continuousAt (h_nonneg p.1 p.2)).comp
        (f := fun p : Disk × Disk => h p.1 p.2) h_continuous.continuousAt
  apply (continuous_const.mul ((h_continuous.add continuous_const).sub
    (continuous_const.mul hf))).inv₀
  intro p
  exact (mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (lt_of_lt_of_le (by positivity : 0 < ε / 2)
      (regularized_denominator hε hε1 p.1 p.2))).ne'

end StrictHotSpots.DiskKernel




end DiskFiniteLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Sobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer



open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots



lemma test_sobolev_ennreal {Ω : Set Plane} {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    eLpNorm f 2 (volume.restrict Ω) ≤
      eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 *
        eLpNorm (fderiv ℝ f) 1 (volume.restrict Ω) := by
  have hn : NNReal.HolderConjugate (Module.finrank ℝ Plane) 2 := by
    simpa [Plane, finrank_euclideanSpace] using NNReal.HolderConjugate.two_two
  have hS := eLpNorm_le_eLpNorm_fderiv_one (volume : Measure Plane)
    (hf.of_le (by simp)) hc hn
  have hs' : Function.support f ⊆ Ω := (subset_tsupport _).trans hs
  have hds : Function.support (fderiv ℝ f) ⊆ Ω :=
    (subset_tsupport _).trans ((tsupport_fderiv_subset ℝ).trans hs)
  rw [eLpNorm_restrict_eq_of_support_subset hs',
    eLpNorm_restrict_eq_of_support_subset (f := fderiv ℝ f)
      (p := (1 : ℝ≥0∞)) (μ := volume) hds]
  exact hS

lemma eLpNorm_fderiv_le_L2_gradient {Ω : Set Plane} {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    eLpNorm (fderiv ℝ f) 1 (volume.restrict Ω) ≤
      eLpNorm (gradient f) 2 (volume.restrict Ω) * (volume Ω) ^ (1 / 2 : ℝ) := by
  have hL := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict Ω) (f := fderiv ℝ f)
    (p := 1) (q := 2) (by norm_num)
    (hf.continuous_fderiv (by simp)).aestronglyMeasurable
  have hG : eLpNorm (fderiv ℝ f) 2 (volume.restrict Ω) =
      eLpNorm (gradient f) 2 (volume.restrict Ω) := by
    apply eLpNorm_congr_norm_ae
    exact Filter.Eventually.of_forall fun x =>
      ((InnerProductSpace.toDual ℝ Plane).symm.norm_map _).symm
  rw [hG] at hL
  convert hL using 1
  norm_num


lemma test_poincare_ennreal {Ω : Set Plane} {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    eLpNorm f 2 (volume.restrict Ω) ≤
      (eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 : ℝ≥0∞) *
      (volume Ω) ^ (1 / 2 : ℝ) * eLpNorm (gradient f) 2 (volume.restrict Ω) := by
  calc
    _ ≤ (eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 1 (volume.restrict Ω) := test_sobolev_ennreal hf hc hs
    _ ≤ (eLpNormLESNormFDerivOneConst (volume : Measure Plane) 2 : ℝ≥0∞) *
        (eLpNorm (gradient f) 2 (volume.restrict Ω) * (volume Ω) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_right (eLpNorm_fderiv_le_L2_gradient hf) _
    _ = _ := by ac_rfl

lemma norm_bound_on_closure {Domain : Type*} {Value : Type*} {Gradient : Type*}
    [TopologicalSpace Domain] [SeminormedAddCommGroup Value]
    [SeminormedAddCommGroup Gradient] (value : Domain → Value) (grad : Domain → Gradient)
    (hvalue : Continuous value) (hgrad : Continuous grad) (constant : ℝ)
    {tests : Set Domain} (hbound : ∀ point ∈ tests, ‖value point‖ ≤ constant * ‖grad point‖)
    {point : Domain} (hpoint : point ∈ closure tests) :
    ‖value point‖ ≤ constant * ‖grad point‖ :=
  closure_minimal hbound (isClosed_le hvalue.norm (continuous_const.mul hgrad.norm)) hpoint

end StrictHotSpots




open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
namespace StrictHotSpots.DiskCutoff

variable {E : Type*} [NormedAddCommGroup E]

def cutoff (κ : ℝ) (x : E) : ℝ :=
  Real.smoothTransition (κ * (1 - ‖x‖ ^ 2) - 1)

end StrictHotSpots.DiskCutoff

namespace StrictHotSpots.L2VectorLimits
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma norm_sq_eq_integral_norm_sq (f : Lp F 2 ν) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma norm_toLp_sub_sq {f g : X → F} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 ∂ν := by
  rw [norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with x hx hfx hgx
  simp only [hx, hfx, hgx, Pi.sub_apply]

lemma tendsto_toLp_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → X → F} {g : X → F} {b : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 ν) (hg : MemLp g 2 ν) (hb : MemLp b 2 ν)
    (hdom : ∀ᶠ n in l, ∀ᵐ x ∂ν, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) l (𝓝 (hg.toLp g)) := by
  have ht : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂ν) l (𝓝 0) := by
    have hm : ∀ᶠ n in l, AEStronglyMeasurable (fun x => ‖f n x-g x‖ ^ 2) ν :=
      Eventually.of_forall fun n => ((hf n).sub hg).aestronglyMeasurable.norm.pow 2
    have hd : ∀ᶠ n in l, ∀ᵐ x ∂ν, ‖‖f n x-g x‖ ^ 2‖ ≤ (b x+‖g x‖)^2 := by
      filter_upwards [hdom] with n hn
      filter_upwards [hn] with x hx
      have h1 : ‖f n x-g x‖ ≤ b x+‖g x‖ :=
        by linarith [norm_sub_le (f n x) (g x)]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hl : ∀ᵐ x ∂ν, Tendsto (fun n => ‖f n x-g x‖ ^ 2) l (𝓝 (0 : ℝ)) := by
      filter_upwards [hlim] with x hx
      simpa using (hx.sub_const (g x)).norm.pow 2
    simpa using tendsto_integral_filter_of_dominated_convergence
      (fun x => (b x+‖g x‖)^2) hm hd (hb.add hg.norm).integrable_sq hl
  have hs : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖^2) l (𝓝 0) := by
    simpa only [norm_toLp_sub_sq] using ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr

end StrictHotSpots.L2VectorLimits

open scoped Laplacian







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Green
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian

open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace

namespace StrictHotSpots.GreenFundamental

def logRegularized (ε : ℝ) (z : ℂ) : ℝ := Real.log (‖z‖ ^ 2 + ε ^ 2)

def peak (z : ℂ) : ℝ := 1 / (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)

def direction (f : ℂ → ℝ) (e : ℂ) (z : ℂ) : ℝ := fderiv ℝ f z e

end StrictHotSpots.GreenFundamental

namespace StrictHotSpots.DiskFormula
open StrictHotSpots.GreenFundamental



def green (x y : ℂ) : ℝ :=
  Real.log (1 + (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) / ‖x-y‖ ^ 2) / (4 * Real.pi)

end StrictHotSpots.DiskFormula

open scoped Convolution
namespace StrictHotSpots.GreenPotential
open StrictHotSpots.GreenFundamental

def correctionIntegrand (f : ℂ → ℝ) (p : ℂ × ℂ) : ℝ :=
  f p.2 * Real.log ‖1-p.1*star p.2‖

end StrictHotSpots.GreenPotential



open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian


namespace StrictHotSpots.GreenPotential
open StrictHotSpots.GreenFundamental StrictHotSpots.DiskFormula


def potential (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  (∫ y : ℂ, f y * Real.log ‖1-z*star y‖) / (2 * Real.pi) -
    (((fun x : ℂ => Real.log ‖x‖) ⋆ f) z) / (2 * Real.pi)

end StrictHotSpots.GreenPotential




open InnerProductSpace
open scoped Laplacian ContDiff







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology
namespace StrictHotSpots.DiskFormula

def poisson (s x : ℂ) : ℝ := (1 - ‖x‖ ^ 2) / (2 * Real.pi * ‖s-x‖ ^ 2)

def boundaryInteraction (s t : ℂ) : ℝ := 1 / (Real.pi * ‖s-t‖ ^ 2)

def logRatio (u : ℝ) : ℝ := dslope Real.log 1 (1+u)

lemma radial_one_formula (s x : ℂ) (hs : ‖s‖ = 1) (r : ℝ) :
    green (r • s) x = Real.log (1 + (1-r^2) * (1-‖x‖^2) / ‖r • s-x‖^2) /
      (4 * Real.pi) := by
  simp only [green, norm_smul, Real.norm_eq_abs, hs, mul_one, sq_abs]

end StrictHotSpots.DiskFormula




open MeasureTheory Filter
open scoped Topology ENNReal


namespace StrictHotSpots.DiskFormula
open MeasureTheory

lemma log_mul_div_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ Real.log (1+a*b)/a ∧ Real.log (1+a*b)/a ≤ b := by
  have h1 : 1 ≤ 1+a*b := by linarith [mul_nonneg ha.le hb]
  constructor
  · exact div_nonneg (Real.log_nonneg h1) ha.le
  · apply (div_le_iff₀ ha).mpr
    have hh := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one h1)
    nlinarith

lemma radial_one_bounded (s x : ℂ) (hs : ‖s‖ = 1)
    {R rmin r : ℝ} (hR : ‖x‖ ≤ R) (hRmin : R < rmin)
    (hrmin : rmin ≤ r) (hr : r < 1) :
    0 ≤ green (r • s) x / (1-r) ∧
      green (r • s) x / (1-r) ≤ (2/(rmin-R)^2)/(4*Real.pi) := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hR
  have hr0 : 0 ≤ r := hR0.trans (hRmin.le.trans hrmin)
  have hx1 : ‖x‖ < 1 := hR.trans_lt (hRmin.trans_le hrmin |>.trans hr)
  have hx2 : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hδ : 0 < rmin-R := sub_pos.mpr hRmin
  have hdist : rmin-R ≤ ‖r • s-x‖ := by
    have hh := norm_sub_norm_le (r • s) x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0, hs, mul_one] at hh
    linarith
  have hdist0 : 0 < ‖r • s-x‖ := hδ.trans_le hdist
  have hd2 : (rmin-R)^2 ≤ ‖r • s-x‖^2 := sq_le_sq₀ hδ.le (norm_nonneg _) |>.mpr hdist
  have hnum : (1+r)*(1-‖x‖^2) ≤ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hb0 : 0 ≤ (1+r)*(1-‖x‖^2)/‖r • s-x‖^2 := by positivity
  have hb : (1+r)*(1-‖x‖^2)/‖r • s-x‖^2 ≤ 2/(rmin-R)^2 := by
    calc
      _ ≤ 2/‖r • s-x‖^2 := div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ) hd2
  have hlog := log_mul_div_bounds (sub_pos.mpr hr) hb0
  have he : green (r • s) x/(1-r) =
      (Real.log (1 + (1-r)*((1+r)*(1-‖x‖^2)/‖r • s-x‖^2))/(1-r))/(4*Real.pi) := by
    rw [radial_one_formula s x hs]
    have hh : (1-r^2)*(1-‖x‖^2)/‖r • s-x‖^2 =
        (1-r)*((1+r)*(1-‖x‖^2)/‖r • s-x‖^2) := by ring
    rw [hh]
    ring
  rw [he]
  exact ⟨div_nonneg hlog.1 (by positivity),
    div_le_div_of_nonneg_right (hlog.2.trans hb) (by positivity)⟩

end StrictHotSpots.DiskFormula

namespace StrictHotSpots.DiskFormula
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma poisson_nonneg (s x : ℂ) (hx : ‖x‖ < 1) : 0 ≤ poisson s x := by
  have hh : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  exact div_nonneg hh (by positivity)

lemma poisson_bounded (s x : ℂ) (hs : ‖s‖ = 1)
    {R : ℝ} (hR : ‖x‖ ≤ R) (hR1 : R < 1) :
    poisson s x ≤ 1 / (2*Real.pi*(1-R)^2) := by
  have hh := norm_sub_norm_le s x
  rw [hs] at hh
  have hd : 1-R ≤ ‖s-x‖ := by linarith
  have hd0 : 0 < 1-R := sub_pos.mpr hR1
  have hd2 : (1-R)^2 ≤ ‖s-x‖^2 := (sq_le_sq₀ hd0.le (norm_nonneg _)).mpr hd
  have hn : 1-‖x‖^2 ≤ 1 := by nlinarith [sq_nonneg ‖x‖]
  unfold poisson
  calc
    _ ≤ 1/(2*Real.pi*‖s-x‖^2) := div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hd2 (by positivity))

end StrictHotSpots.DiskFormula





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal
namespace StrictHotSpots.GreenLp

def logPole (z : ℂ) : ℝ := Real.log (1 + 1 / ‖z‖^2)

lemma logPole_nonneg (z : ℂ) : 0 ≤ logPole z := by
  apply Real.log_nonneg
  have : 0 ≤ 1 / ‖z‖^2 := one_div_nonneg.mpr (sq_nonneg _)
  linarith

lemma measurable_logPole : Measurable logPole := by
  unfold logPole
  fun_prop

lemma logPole_cube_bound {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) :
    (Real.log (1 + 1/t^2))^3 ≤ 648 / t := by
  have harg : 1 + 1/t^2 ≤ (3/t)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos ht)).2
    field_simp
    nlinarith
  have hl : Real.log (1 + 1/t^2) ≤ 2 * Real.log (3/t) := by
    have hh := Real.log_le_log (by positivity : 0 < 1 + 1/t^2) harg
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hp : 0 < 3/t := by positivity
  have hr := Real.log_le_rpow_div hp.le (show 0 < (3:ℝ)⁻¹ by norm_num)
  have he : Real.log (1 + 1/t^2) ≤ 6 * (3/t)^((3:ℝ)⁻¹) := by
    norm_num at hr
    linarith
  have hnon : 0 ≤ Real.log (1 + 1/t^2) := by
    apply Real.log_nonneg
    have := one_div_nonneg.mpr (sq_nonneg t)
    linarith
  have hh := pow_le_pow_left₀ hnon he 3
  have hh3 : ((3/t)^((3:ℝ)⁻¹))^3 = 3/t := by
    simpa only [Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hp.le (show (3:ℕ) ≠ 0 by decide)
  rw [mul_pow, hh3] at hh
  calc
    _ ≤ 6^3 * (3/t) := hh
    _ = 648/t := by ring

lemma logPole_cube_integrable : IntegrableOn (fun z : ℂ => (logPole z)^3) (ball 0 2) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 648) (α := 1)
    (by norm_num : 1 ≤ Module.finrank ℝ ℂ) (by norm_num : (1:ℝ) < Module.finrank ℝ ℂ)
  · filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
    rw [Real.norm_of_nonneg (pow_nonneg (logPole_nonneg z) _), Real.rpow_neg_one]
    by_cases hzero : z = 0
    · simp [hzero, logPole]
    · have hp := norm_pos_iff.mpr hzero
      have hlt : ‖z‖ < 2 := by simpa using hz
      simpa only [logPole, div_eq_mul_inv] using logPole_cube_bound hp hlt.le
  · exact (measurable_logPole.pow_const 3).aestronglyMeasurable

lemma logPole_memLp_three : MemLp logPole 3 (volume.restrict (ball 0 2)) := by
  apply (integrable_norm_rpow_iff measurable_logPole.aestronglyMeasurable
    (by norm_num : (3:ℝ≥0∞) ≠ 0) (by simp : (3:ℝ≥0∞) ≠ (∞ : ℝ≥0∞))).1
  simpa only [IntegrableOn, ENNReal.toReal_ofNat, ← Real.rpow_natCast, Nat.cast_ofNat,
    Real.norm_of_nonneg (logPole_nonneg _)] using logPole_cube_integrable

lemma shifted_logPole_memLp_three (x : ℂ) (hx : ‖x‖ < 1) :
    MemLp (fun y => logPole (x-y)) 3 (volume.restrict (ball 0 1)) := by
  have hpres := (measurePreserving_sub_right (volume : Measure ℂ) x).restrict_preimage
    (show MeasurableSet (ball (0:ℂ) 2) from measurableSet_ball)
  have hh := logPole_memLp_three.comp_measurePreserving hpres
  have hsub : ball (0:ℂ) 1 ⊆ (fun y => y-x) ⁻¹' ball 0 2 := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa using hy
    have hd := norm_sub_le y x
    change y-x ∈ ball (0:ℂ) 2
    rw [mem_ball_zero_iff]
    linarith
  have hm := MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hh
  convert hm using 1
  funext y
  dsimp only [Function.comp_def, logPole]
  rw [norm_sub_rev]

end StrictHotSpots.GreenLp


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal
namespace StrictHotSpots.DiskFormula
open GreenLp

lemma measurable_green_left (x : ℂ) : Measurable (green x) := by
  unfold green
  fun_prop

lemma green_bounds {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    0 ≤ green x y ∧ green x y ≤ logPole (x-y) / (4*Real.pi) := by
  have hwx : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hwy : 0 ≤ 1-‖y‖^2 := by nlinarith [norm_nonneg y]
  have hn : (1-‖x‖^2)*(1-‖y‖^2) ≤ 1 := by
    nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖, mul_nonneg hwx (sq_nonneg ‖y‖)]
  have hdiv : 0 ≤ (1-‖x‖^2)*(1-‖y‖^2)/‖x-y‖^2 := by positivity
  have hdiv' := div_le_div_of_nonneg_right hn (sq_nonneg ‖x-y‖)
  have hlog : 0 ≤ Real.log (1+(1-‖x‖^2)*(1-‖y‖^2)/‖x-y‖^2) :=
    Real.log_nonneg (by linarith)
  refine ⟨div_nonneg hlog (by positivity), ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 4*Real.pi)
  exact Real.log_le_log (by linarith) (by simpa only [logPole] using add_le_add_right hdiv' 1)

lemma green_pos {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (hne : x ≠ y) :
    0 < green x y := by
  apply div_pos _ (by positivity)
  apply Real.log_pos
  have hwx : 0 < 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hwy : 0 < 1-‖y‖^2 := by nlinarith [norm_nonneg y]
  have hd : 0 < ‖x-y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have := div_pos (mul_pos hwx hwy) hd
  linarith

lemma green_memLp_three (x : ℂ) (hx : ‖x‖ < 1) :
    MemLp (green x) 3 (volume.restrict (ball 0 1)) := by
  have hm : MemLp (fun y => logPole (x-y)/(4*Real.pi)) 3
      (volume.restrict (ball 0 1)) := by
    simpa only [div_eq_mul_inv] using
      (shifted_logPole_memLp_three x hx).mul_const (4*Real.pi)⁻¹
  apply hm.mono (measurable_green_left x).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with y hy
  have hy' : ‖y‖ ≤ 1 := (by simpa using hy : ‖y‖ < 1).le
  have hb := green_bounds hx.le hy'
  rw [Real.norm_of_nonneg hb.1, Real.norm_of_nonneg (div_nonneg (logPole_nonneg (x-y)) (by positivity :
    0 ≤ 4*Real.pi))]
  exact hb.2

lemma green_memLp_two (x : ℂ) (hx : ‖x‖ < 1) :
    MemLp (green x) 2 (volume.restrict (ball 0 1)) := by
  have : IsFiniteMeasure (volume.restrict (ball (0:ℂ) 1)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using measure_ball_lt_top (x := (0:ℂ)) (r := 1)⟩
  exact (green_memLp_three x hx).mono_exponent (by norm_num)

end StrictHotSpots.DiskFormula


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal
namespace StrictHotSpots.GreenLp

lemma logPole_memLp_two : MemLp logPole 2 (volume.restrict (ball (0 : ℂ) 2)) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 2)) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  exact logPole_memLp_three.mono_exponent (by norm_num)

lemma shifted_logPole_norm_bound (x : ℂ) (hx : ‖x‖ < 1) :
    eLpNorm (fun y => logPole (x-y)) 2 (volume.restrict (ball 0 1)) ≤
      eLpNorm logPole 2 (volume.restrict (ball (0 : ℂ) 2)) := by
  have hm := (measurePreserving_sub_right (volume : Measure ℂ) x).restrict_preimage
    (show MeasurableSet (ball (0 : ℂ) 2) from measurableSet_ball)
  have hs : ball (0 : ℂ) 1 ⊆ (fun y => y-x) ⁻¹' ball 0 2 := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa using hy
    have hd := norm_sub_le y x
    change y-x ∈ ball (0 : ℂ) 2
    rw [mem_ball_zero_iff]
    linarith
  calc
    _ = eLpNorm (logPole ∘ fun y => y-x) 2 (volume.restrict (ball 0 1)) := by
      congr 1
      funext y
      simp only [Function.comp_apply, logPole, norm_sub_rev x y]
    _ ≤ eLpNorm (logPole ∘ fun y => y-x) 2
        (volume.restrict ((fun y => y-x) ⁻¹' ball 0 2)) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl)
    _ = _ := eLpNorm_comp_measurePreserving logPole_memLp_two.aestronglyMeasurable hm

end StrictHotSpots.GreenLp
namespace StrictHotSpots.DiskFormula
open GreenLp

lemma green_uniform_L2_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℂ, ‖x‖ < 1 →
    (eLpNorm (green x) 2 (volume.restrict (ball 0 1))).toReal ≤ B := by
  let C := ENNReal.ofReal (4*Real.pi)⁻¹ *
    eLpNorm logPole 2 (volume.restrict (ball (0 : ℂ) 2))
  have hC : C ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top logPole_memLp_two.eLpNorm_ne_top
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun x hx => ?_⟩
  apply ENNReal.toReal_mono hC
  calc
    _ ≤ ENNReal.ofReal (4*Real.pi)⁻¹ *
        eLpNorm (fun y => logPole (x-y)) 2 (volume.restrict (ball 0 1)) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have hy' : ‖y‖ ≤ 1 := (by simpa using hy : ‖y‖ < 1).le
      have hh := green_bounds hx.le hy'
      rw [Real.norm_of_nonneg hh.1, Real.norm_of_nonneg (logPole_nonneg _)]
      simpa only [div_eq_mul_inv, mul_comm] using hh.2
    _ ≤ C := by
      dsimp [C]
      gcongr
      exact shifted_logPole_norm_bound x hx

end StrictHotSpots.DiskFormula



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.MeasurableL2Kernel

lemma integral_mul_eq_inner {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    (∫ x, f x * g x ∂ν) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx,hy, RCLike.inner_apply, conj_trivial]
  ring

lemma norm_integral_mul_le {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ‖∫ x, f x * g x ∂ν‖ ≤ (eLpNorm f 2 ν).toReal * (eLpNorm g 2 ν).toReal := by
  rw [integral_mul_eq_inner hf hg]
  simpa only [Lp.norm_toLp] using norm_inner_le_norm (hf.toLp f) (hg.toLp g)

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (K : X × Y → ℝ) (hK : AEStronglyMeasurable K (μ.prod ν))
  (hrow : ∀ᵐ x ∂μ, MemLp (fun y => K (x,y)) 2 ν)
  {B : ℝ} (hB : 0 ≤ B)
  (hbound : ∀ᵐ x ∂μ, (eLpNorm (fun y => K (x,y)) 2 ν).toReal ≤ B)

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
include hrow hbound in
lemma apply_bound (f : Lp ℝ 2 ν) :
    ∀ᵐ x ∂μ, ‖∫ y, K (x,y) * f y ∂ν‖ ≤ B * ‖f‖ := by
  filter_upwards [hrow, hbound] with x hx hb
  have hh := norm_integral_mul_le hx (Lp.memLp f)
  have he : (eLpNorm (fun y => f y) 2 ν).toReal = ‖f‖ := rfl
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg f))

include hK hrow hbound in
lemma apply_memLp (f : Lp ℝ 2 ν) :
    MemLp (fun x => ∫ y, K (x,y) * f y ∂ν) 2 μ := by
  have hm : AEStronglyMeasurable (fun z : X × Y => K z * f z.2) (μ.prod ν) :=
    hK.mul (Lp.aestronglyMeasurable f).comp_snd
  exact MemLp.of_bound hm.integral_prod_right' (B * ‖f‖)
    (apply_bound K hrow hbound f)



def operator : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ := by
  let T : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun f => (apply_memLp K hK hrow hbound f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(apply_memLp K hK hrow hbound (f+g)).coeFn_toLp,
          (apply_memLp K hK hrow hbound f).coeFn_toLp,
          (apply_memLp K hK hrow hbound g).coeFn_toLp,
          Lp.coeFn_add ((apply_memLp K hK hrow hbound f).toLp _)
            ((apply_memLp K hK hrow hbound g).toLp _), hrow] with x hx hf hg ha hr
        rw [hx,ha, Pi.add_apply,hf,hg]
        have he : (fun y => K (x,y) * (f+g) y) =ᵐ[ν]
            (fun y => K (x,y) * f y + K (x,y) * g y) := by
          filter_upwards [Lp.coeFn_add f g] with y hy
          rw [hy, Pi.add_apply, mul_add]
        rw [integral_congr_ae he, integral_add]
        · exact hr.integrable_mul (Lp.memLp f)
        · exact hr.integrable_mul (Lp.memLp g)
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(apply_memLp K hK hrow hbound (c • f)).coeFn_toLp,
          (apply_memLp K hK hrow hbound f).coeFn_toLp,
          Lp.coeFn_smul c ((apply_memLp K hK hrow hbound f).toLp _)] with x hx hf hs
        simp only [RingHom.id_apply]
        rw [hx,hs, Pi.smul_apply,hf]
        have he : (fun y => K (x,y) * (c • f) y) =ᵐ[ν]
            (fun y => c * (K (x,y) * f y)) := by
          filter_upwards [Lp.coeFn_smul c f] with y hy
          rw [hy, Pi.smul_apply, smul_eq_mul]
          ring
        rw [integral_congr_ae he, integral_const_mul, smul_eq_mul] }
  refine T.mkContinuous ((measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * B) ?_
  intro f
  have hh := Lp.norm_le_of_ae_bound (mul_nonneg hB (norm_nonneg f))
    (show ∀ᵐ x ∂μ, ‖T f x‖ ≤ B * ‖f‖ from by
      filter_upwards [(apply_memLp K hK hrow hbound f).coeFn_toLp,
        apply_bound K hrow hbound f] with x hx hb
      change ‖((apply_memLp K hK hrow hbound f).toLp _) x‖ ≤ _
      rw [hx]
      exact hb)
  exact hh.trans_eq (mul_assoc _ _ _).symm

end StrictHotSpots.MeasurableL2Kernel



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology







open scoped InnerProductSpace
namespace StrictHotSpots.DirichletOperator

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


def solution (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H) :
    H →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp J.adjoint


def green (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H) :
    H →L[ℝ] H := J.comp (solution B hB J)

end StrictHotSpots.DirichletOperator


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace


open MeasureTheory
open scoped InnerProductSpace ENNReal


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section TransferLayer



open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.MeasureKernelTransfer

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure X} {μ : Measure Y} (e : X → Y) (he : MeasurePreserving e ν μ)

def observe : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℝ e he).toContinuousLinearMap

def operator (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  ((observe e he).comp T).comp (observe e he).adjoint

end StrictHotSpots.MeasureKernelTransfer

end TransferLayer


section DiskCompactLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace StrictHotSpots.DiskCompact
variable {X : Type}
  [MetricSpace X]
  [CompactSpace X]
  [MeasurableSpace X]
  [BorelSpace X]
  (ν : Measure X)
  [IsFiniteMeasure ν]
  (e : X → Plane)
  (he : Continuous e)

def regularizationParameter (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

lemma parameter_pos (n : ℕ) : 0 < regularizationParameter n := by
  unfold regularizationParameter
  positivity
lemma parameter_le_one (n : ℕ) : regularizationParameter n ≤ 1 := by
  unfold regularizationParameter
  exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])

end StrictHotSpots.DiskCompact
end
end DiskCompactLayer

section BoundaryRowLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.DiskFormula
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma poisson_memLp_ae (s : ℂ) (hs : ‖s‖ = 1) (x : X → ℂ) (hm : Measurable x)
    {R : ℝ} (hR : ∀ᵐ z ∂ν, ‖x z‖ ≤ R) (hR1 : R < 1) :
    MemLp (fun z => poisson s (x z)) 2 ν := by
  refine MemLp.of_bound ?_ (1 / (2*Real.pi*(1-R)^2)) ?_
  · apply Measurable.aestronglyMeasurable
    unfold poisson
    fun_prop
  · filter_upwards [hR] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (poisson_nonneg s (x z) (hz.trans_lt hR1))]
    exact poisson_bounded s (x z) hs hz hR1

lemma radial_one_memLp_ae (s : ℂ) (hs : ‖s‖ = 1) (x : X → ℂ) (hm : Measurable x)
    {R rmin r : ℝ} (hR : ∀ᵐ z ∂ν, ‖x z‖ ≤ R) (hRmin : R < rmin)
    (hrmin : rmin ≤ r) (hr : r < 1) :
    MemLp (fun z => green (r • s) (x z)/(1-r)) 2 ν := by
  refine MemLp.of_bound ?_ ((2/(rmin-R)^2)/(4*Real.pi)) ?_
  · apply Measurable.aestronglyMeasurable
    unfold green
    fun_prop
  · filter_upwards [hR] with z hz
    obtain ⟨h0,hb⟩ := radial_one_bounded s (x z) hs hz hRmin hrmin hr
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using hb



end StrictHotSpots.DiskFormula
end
end BoundaryRowLayer

section BoundarySmoothingLayer
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology
namespace StrictHotSpots.GreenLp

lemma shifted_logPole_norm_bound_three (x : ℂ) (hx : ‖x‖ < 1) :
    eLpNorm (fun y => logPole (x-y)) 3 (volume.restrict (ball 0 1)) ≤
      eLpNorm logPole 3 (volume.restrict (ball (0 : ℂ) 2)) := by
  have hm := (measurePreserving_sub_right (volume : Measure ℂ) x).restrict_preimage
    (show MeasurableSet (ball (0 : ℂ) 2) from measurableSet_ball)
  have hs : ball (0 : ℂ) 1 ⊆ (fun y => y-x) ⁻¹' ball 0 2 := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa using hy
    have hd := norm_sub_le y x
    change y-x ∈ ball (0 : ℂ) 2
    rw [mem_ball_zero_iff]
    linarith
  calc
    _ = eLpNorm (logPole ∘ fun y => y-x) 3 (volume.restrict (ball 0 1)) := by
      congr 1
      funext y
      simp only [Function.comp_apply, logPole, norm_sub_rev x y]
    _ ≤ eLpNorm (logPole ∘ fun y => y-x) 3
        (volume.restrict ((fun y => y-x) ⁻¹' ball 0 2)) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl)
    _ = _ := eLpNorm_comp_measurePreserving logPole_memLp_three.aestronglyMeasurable hm

lemma invnorm_memLp_three_halves : MemLp (fun z : ℂ => ‖z‖⁻¹) (3/2)
    (volume.restrict (ball (0 : ℂ) 2)) := by
  have hm : Measurable (fun z : ℂ => ‖z‖⁻¹) := by fun_prop
  apply (integrable_norm_rpow_iff hm.aestronglyMeasurable
    (by norm_num : (3/2 : ℝ≥0∞) ≠ 0) (ENNReal.div_ne_top (by norm_num) (by norm_num) : (3/2 : ℝ≥0∞) ≠ ∞)).1
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 3/2)
    (by norm_num : 1 ≤ Module.finrank ℝ ℂ) (by norm_num : (3/2:ℝ) < Module.finrank ℝ ℂ)
  · filter_upwards [] with z
    simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
      Real.inv_rpow (norm_nonneg z), Real.rpow_neg (norm_nonneg z), one_mul]
    rw [Real.norm_of_nonneg (by positivity)]
  · exact (hm.norm.pow_const _).aestronglyMeasurable

lemma shifted_invnorm_memLp_bound (s : ℂ) (hs : ‖s‖ = 1) :
    MemLp (fun y => ‖s-y‖⁻¹) (3/2) (volume.restrict (ball 0 1)) ∧
    eLpNorm (fun y => ‖s-y‖⁻¹) (3/2) (volume.restrict (ball 0 1)) ≤
      eLpNorm (fun z : ℂ => ‖z‖⁻¹) (3/2) (volume.restrict (ball (0 : ℂ) 2)) := by
  have hm := (measurePreserving_sub_right (volume : Measure ℂ) s).restrict_preimage
    (show MeasurableSet (ball (0 : ℂ) 2) from measurableSet_ball)
  have he : (fun y : ℂ => ‖s-y‖⁻¹) = (fun z : ℂ => ‖z‖⁻¹) ∘ (fun y => y-s) := by
    funext y
    simp only [Function.comp_apply,norm_sub_rev s y]
  have hsub : ball (0 : ℂ) 1 ⊆ (fun y => y-s) ⁻¹' ball 0 2 := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa using hy
    have hd := norm_sub_le y s
    change y-s ∈ ball (0 : ℂ) 2
    rw [mem_ball_zero_iff]
    rw [hs] at hd
    linarith
  rw [he]
  refine ⟨(invnorm_memLp_three_halves.comp_measurePreserving hm).mono_measure
    (Measure.restrict_mono hsub le_rfl), ?_⟩
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans_eq
    (eLpNorm_comp_measurePreserving invnorm_memLp_three_halves.aestronglyMeasurable hm)

end StrictHotSpots.GreenLp
namespace StrictHotSpots.DiskFormula
open GreenLp

lemma green_uniform_L3_bound : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x : ℂ, ‖x‖ < 1 →
    eLpNorm (green x) 3 (volume.restrict (ball 0 1)) ≤ B := by
  let C := ENNReal.ofReal (4*Real.pi)⁻¹ *
    eLpNorm logPole 3 (volume.restrict (ball (0 : ℂ) 2))
  refine ⟨C, ENNReal.mul_ne_top ENNReal.ofReal_ne_top logPole_memLp_three.eLpNorm_ne_top,
    fun x hx => ?_⟩
  calc
    _ ≤ ENNReal.ofReal (4*Real.pi)⁻¹ *
        eLpNorm (fun y => logPole (x-y)) 3 (volume.restrict (ball 0 1)) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      have hy' : ‖y‖ ≤ 1 := (by simpa using hy : ‖y‖ < 1).le
      have hh := green_bounds hx.le hy'
      rw [Real.norm_of_nonneg hh.1, Real.norm_of_nonneg (logPole_nonneg _)]
      simpa only [div_eq_mul_inv, mul_comm] using hh.2
    _ ≤ C := by
      dsimp [C]
      gcongr
      exact shifted_logPole_norm_bound_three x hx

lemma poisson_invnorm_bound (s x : ℂ) (hs : ‖s‖ = 1) (hx : ‖x‖ < 1) :
    poisson s x ≤ Real.pi⁻¹ * ‖s-x‖⁻¹ := by
  have hn : 0 < ‖s-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => by
    rw [← h,hs] at hx; exact lt_irrefl _ hx))
  have hd : 1-‖x‖ ≤ ‖s-x‖ := by
    have ht := norm_le_norm_sub_add s x
    rw [hs] at ht
    linarith
  have hnum : 1-‖x‖^2 ≤ 2*‖s-x‖ := by
    nlinarith [norm_nonneg x]
  unfold poisson
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_pos hn))).2
  calc
    _ ≤ 2*‖s-x‖ := hnum
    _ = Real.pi⁻¹ * ‖s-x‖⁻¹ * (2*Real.pi*‖s-x‖^2) := by
      field_simp

lemma poisson_memLp_three_halves (s : ℂ) (hs : ‖s‖ = 1) :
    MemLp (poisson s) (3/2) (volume.restrict (ball 0 1)) := by
  apply ((shifted_invnorm_memLp_bound s hs).1.const_mul Real.pi⁻¹).mono
    (by
      have hm : Measurable (poisson s) := by unfold poisson; fun_prop
      exact hm.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hx' : ‖x‖ < 1 := by simpa using hx
  simpa only [Real.norm_of_nonneg (poisson_nonneg s x hx'),
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      (inv_nonneg.mpr (norm_nonneg _)))] using poisson_invnorm_bound s x hs hx'

lemma poisson_uniform_L32_bound : ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ s : ℂ, ‖s‖ = 1 →
    eLpNorm (poisson s) (3/2) (volume.restrict (ball 0 1)) ≤ B := by
  let C := ENNReal.ofReal Real.pi⁻¹ *
    eLpNorm (fun z : ℂ => ‖z‖⁻¹) (3/2) (volume.restrict (ball (0 : ℂ) 2))
  refine ⟨C, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    invnorm_memLp_three_halves.eLpNorm_ne_top, fun s hs => ?_⟩
  calc
    _ ≤ ENNReal.ofReal Real.pi⁻¹ *
        eLpNorm (fun x => ‖s-x‖⁻¹) (3/2) (volume.restrict (ball 0 1)) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hx' : ‖x‖ < 1 := by simpa using hx
      simpa only [Real.norm_of_nonneg (poisson_nonneg s x hx'),
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
        poisson_invnorm_bound s x hs hx'
    _ ≤ C := mul_le_mul' le_rfl (shifted_invnorm_memLp_bound s hs).2

end StrictHotSpots.DiskFormula
end
end BoundarySmoothingLayer
section FullBoundarySmoothingLayer
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen

local instance holder_three_three_halves : ENNReal.HolderTriple 3 (3/2) 1 := by
  rw [ENNReal.holderTriple_iff]
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by norm_num)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]

end StrictHotSpots.PlaneGreen
end
end FullBoundarySmoothingLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Helmholtz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section LpZeroExtensionCombinedLayer
open MeasureTheory Set Filter
open scoped ENNReal
namespace StrictHotSpots.LpZeroExtension
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set α} (hs : MeasurableSet s)

def lift (f : Lp E 2 (μ.restrict s)) : Lp E 2 μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator f)

omit [NormedSpace ℝ E] in
lemma lift_ae (f : Lp E 2 (μ.restrict s)) : lift hs f =ᵐ[μ] s.indicator f :=
  MemLp.coeFn_toLp _

omit [NormedSpace ℝ E] in
lemma lift_norm (f : Lp E 2 (μ.restrict s)) : ‖lift hs f‖ = ‖f‖ := by
  rw [lift,Lp.norm_toLp,eLpNorm_indicator_eq_eLpNorm_restrict hs,Lp.norm_def]

def linearIsometry : Lp E 2 (μ.restrict s) →ₗᵢ[ℝ] Lp E 2 μ where
  toFun := lift hs
  map_add' f g := by
    apply Lp.ext
    filter_upwards [lift_ae hs (f+g),Lp.coeFn_add (lift hs f) (lift hs g),
      lift_ae hs f,lift_ae hs g,
      (ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_add f g)] with x hx hy hf hg hh
    rw [hx,hy]
    simp only [Pi.add_apply]
    rw [hf,hg,hh]
    by_cases hx : x ∈ s <;> simp [hx]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [lift_ae hs (c • f),Lp.coeFn_smul c (lift hs f),
      lift_ae hs f,(ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_smul c f)] with x hx hy hf hh
    change (lift hs (c • f) : α → E) x = (c • lift hs f : Lp E 2 μ) x
    rw [hx,hy]
    simp only [Pi.smul_apply]
    rw [hf,hh]
    by_cases hx : x ∈ s <;> simp [hx]
  norm_map' := lift_norm hs

end StrictHotSpots.LpZeroExtension
end LpZeroExtensionCombinedLayer

section HelmholtzUCPCombinedLayer






open Set MeasureTheory Filter Metric _root_.Complex
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Helmholtz


def direction (θ : ℝ) : ℂ := circleMap 0 1 θ

def radial (u : ℂ → ℂ) (a : ℂ) (r θ : ℝ) : ℂ := u (circleMap a r θ)
def radialDeriv (u : ℂ → ℂ) (a : ℂ) (r θ : ℝ) : ℂ :=
  fderiv ℝ u (circleMap a r θ) (direction θ)
def radialSecond (u : ℂ → ℂ) (a : ℂ) (r θ : ℝ) : ℂ :=
  fderiv ℝ (fderiv ℝ u) (circleMap a r θ) (direction θ) (direction θ)
def angularDeriv (u : ℂ → ℂ) (a : ℂ) (r θ : ℝ) : ℂ :=
  fderiv ℝ u (circleMap a r θ) (circleMap 0 r θ * I)
def angularSecond (u : ℂ → ℂ) (a : ℂ) (r θ : ℝ) : ℂ :=
  fderiv ℝ (fderiv ℝ u) (circleMap a r θ)
      (circleMap 0 r θ * I) (circleMap 0 r θ * I) - r • radialDeriv u a r θ

end StrictHotSpots.Helmholtz
end HelmholtzUCPCombinedLayer

section HelmholtzFourierCombinedLayer

open Set MeasureTheory Filter Metric _root_.Complex
open scoped Topology ContDiff Laplacian Interval
namespace StrictHotSpots.Helmholtz


def weight (n : ℤ) (θ : ℝ) : ℂ := fourier (-n) (θ : AddCircle (2*Real.pi))

def coeff (u : ℂ → ℂ) (a : ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in 0..2*Real.pi, weight n θ * radial u a r θ

def coeffDeriv (u : ℂ → ℂ) (a : ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in 0..2*Real.pi, weight n θ * radialDeriv u a r θ

def coeffSecond (u : ℂ → ℂ) (a : ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in 0..2*Real.pi, weight n θ * radialSecond u a r θ

end StrictHotSpots.Helmholtz
end HelmholtzFourierCombinedLayer

section HelmholtzContinuationCombinedLayer

open Set MeasureTheory Filter Metric _root_.Complex
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Helmholtz

def circleFunction (u : ℂ → ℂ) (a : ℂ) (r : ℝ) (s : AddCircle (2 * Real.pi)) : ℂ :=
  u (a + r • (AddCircle.homeomorphCircle' s : ℂ))

end StrictHotSpots.Helmholtz
end HelmholtzContinuationCombinedLayer

section HelmholtzMollificationCombinedLayer

open Set MeasureTheory Filter Metric _root_.Complex ContinuousLinearMap
open scoped Topology ContDiff Laplacian Convolution
namespace StrictHotSpots.Helmholtz

abbrev smulFlip : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip


def WeakEquation (U : Set ℂ) (μ : ℝ) (u : ℂ → ℂ) : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ z, (Δ φ) z • u z) = -μ • (∫ z, φ z • u z)

end StrictHotSpots.Helmholtz
end HelmholtzMollificationCombinedLayer

section HelmholtzWeakCombinedLayer

open Set MeasureTheory Filter Metric _root_.Complex ContinuousLinearMap
open scoped Topology ContDiff Laplacian Convolution
namespace StrictHotSpots.Helmholtz

def mollifier (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1/((n:ℝ)+1)
  rOut := 2/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

def smoothen (u : ℂ → ℂ) (n : ℕ) : ℂ → ℂ := u ⋆[smulFlip] (mollifier n).normed volume

end StrictHotSpots.Helmholtz
end HelmholtzWeakCombinedLayer

section GapWeakPDECombinedLayer
open scoped Laplacian ContDiff InnerProductSpace
open Set MeasureTheory Filter
namespace StrictHotSpots
open Laplacian

abbrev planeBasis := EuclideanSpace.basisFun (Fin 2) ℝ


end StrictHotSpots

end GapWeakPDECombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Dirichlet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section H10DilationCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots

namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) {R : ℝ} (hR : 1 ≤ R)
  (hb : Ω ⊆ Metric.ball 0 R)

include hR in
lemma radius_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR

end H10
end StrictHotSpots
end H10DilationCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_DouglasEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PoissonComponents

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace Convolution
namespace StrictHotSpots.Douglas
local notation "τ" => (2*Real.pi)



def imagDatum (f : C(AddCircle τ,ℂ)) : C(AddCircle τ,ℂ) := (-Complex.I) • f

end StrictHotSpots.Douglas
end
end PoissonComponents

section DouglasLipschitzEnergy

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen
local instance instFactLtRealOfNatHMulPi_solutions_16 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

end StrictHotSpots.Douglas
end
end DouglasLipschitzEnergy

section DouglasLipschitzBilinear

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen
local instance instFactLtRealOfNatHMulPi_solutions_18 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

end StrictHotSpots.Douglas
end
end DouglasLipschitzBilinear

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_KernelLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section L2CutoffLayer

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.L2Cutoff
variable {X : Type*} [MeasurableSpace X] {ν : Measure X} (s : Set X) (hs : MeasurableSet s)

include hs in
lemma extension_memLp (f : Lp ℝ 2 (ν.restrict s)) : MemLp (s.indicator f) 2 ν :=
  (memLp_indicator_iff_restrict hs).2 (Lp.memLp f)

def extension : Lp ℝ 2 (ν.restrict s) →L[ℝ] Lp ℝ 2 ν := by
  let J : Lp ℝ 2 (ν.restrict s) →ₗ[ℝ] Lp ℝ 2 ν :=
    { toFun := fun f => (extension_memLp s hs f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(extension_memLp s hs (f+g)).coeFn_toLp,
          (extension_memLp s hs f).coeFn_toLp, (extension_memLp s hs g).coeFn_toLp,
          Lp.coeFn_add ((extension_memLp s hs f).toLp _) ((extension_memLp s hs g).toLp _),
          ae_imp_of_ae_restrict (Lp.coeFn_add f g)] with x hfg hf hg ha he
        rw [hfg,ha,Pi.add_apply,hf,hg]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx, he hx, Pi.add_apply]
        · simp [indicator_of_notMem hx]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(extension_memLp s hs (c • f)).coeFn_toLp,
          (extension_memLp s hs f).coeFn_toLp,
          Lp.coeFn_smul c ((extension_memLp s hs f).toLp _),
          ae_imp_of_ae_restrict (Lp.coeFn_smul c f)] with x hcf hf hc he
        simp only [RingHom.id_apply]
        rw [hcf,hc,Pi.smul_apply,hf]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx, he hx, Pi.smul_apply]
        · simp [indicator_of_notMem hx] }
  refine J.mkContinuous 1 (fun f => ?_)
  change ‖(extension_memLp s hs f).toLp _‖ ≤ 1 * ‖f‖
  rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs, one_mul]
  rfl

def restriction : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 (ν.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    (show ν.restrict s ≤ 1 • ν by simpa using Measure.restrict_le_self)

def projection : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν := (extension s hs).comp (restriction s)

end StrictHotSpots.L2Cutoff

end L2CutoffLayer

section CutoffOperatorsLayer
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.L2Cutoff
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  (s : Set X) (hs : MeasurableSet s)

def restrictedOperator (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    Lp ℝ 2 (ν.restrict s) →L[ℝ] Lp ℝ 2 (ν.restrict s) :=
  (restriction s).comp (T.comp (extension s hs))

def compressedOperator (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (projection s hs).comp (T.comp (projection s hs))

end StrictHotSpots.L2Cutoff
end
end CutoffOperatorsLayer

section DiskCutoffLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen

def cutoffRadius (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 1)

lemma cutoffRadius_lt_one (n : ℕ) : cutoffRadius n < 1 := by
  unfold cutoffRadius
  exact sub_lt_self _ (one_div_pos.mpr (by positivity))

end StrictHotSpots.PlaneGreen
end
end DiskCutoffLayer



end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzBoundaryScalarSupport

noncomputable section

section BoundaryMeasureScalarSupportLayer

section BoundaryMeasureLayer
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen

local instance twoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

end StrictHotSpots.PlaneGreen
end
end BoundaryMeasureLayer
end BoundaryMeasureScalarSupportLayer

section BochnerL2RowsScalarSupportLayer

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.L2Rows

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]


lemma average_memLp {r : A → B → ℝ}
    (hm : Measurable (fun z : A × B => r z.1 z.2)) {M : ℝ}
    (hM : ∀ᵐ z ∂μ.prod ν, ‖r z.1 z.2‖ ≤ M) :
    MemLp (fun x => ∫ a, r a x ∂μ) 2 ν := by
  have hh : StronglyMeasurable (fun x => ∫ a, r a x ∂μ) :=
    hm.stronglyMeasurable.integral_prod_left'
  apply MemLp.of_bound hh.aestronglyMeasurable (M * μ.real univ)
  have hb := (Measure.ae_ae_comm (p := fun a x => ‖r a x‖ ≤ M)
    (measurableSet_le hm.norm measurable_const)).mp
    (Measure.ae_ae_of_ae_prod hM)
  filter_upwards [hb] with x hx
  exact norm_integral_le_of_norm_le_const hx

end StrictHotSpots.L2Rows
end BochnerL2RowsScalarSupportLayer

end
end LipschitzBoundaryScalarSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Potentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport

noncomputable section

section HarmonicRadialRegularityBaseLayer
open Set MeasureTheory Metric _root_.Complex Function Filter Real
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Weyl

def radialBump (R : ℝ) (z : ℂ) : ℝ := expNegInvGlue (R^2-‖z‖^2)

end StrictHotSpots.Weyl
end HarmonicRadialRegularityBaseLayer


section PrimitiveAtlasInteriorSupportLayer




open Set Filter Bundle
open scoped Topology
namespace StrictHotSpots.Primitives

structure DiscreteReal where
  val : ℝ

instance instTopologicalSpaceDiscreteReal : TopologicalSpace DiscreteReal := ⊥
instance instDiscreteTopologyDiscreteReal : DiscreteTopology DiscreteReal := ⟨rfl⟩

@[ext] lemma DiscreteReal.ext {x y : DiscreteReal} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

structure Atlas (X ι : Type*) [TopologicalSpace X] where
  U : ι → Set X
  isOpen_U : ∀ i, IsOpen (U i)
  idx : X → ι
  mem_U : ∀ x, x ∈ U (idx x)
  potential : ι → X → ℝ
  constant_overlap : ∀ i j x y, x ∈ U i ∩ U j → y ∈ U i ∩ U j →
    potential i x-potential j x = potential i y-potential j y

namespace Atlas
variable {X ι : Type*} [TopologicalSpace X] (A : Atlas X ι)

def core : FiberBundleCore ι X DiscreteReal where
  baseSet := A.U
  isOpen_baseSet := A.isOpen_U
  indexAt := A.idx
  mem_baseSet_at := A.mem_U
  coordChange i j x d := ⟨d.val+A.potential i x-A.potential j x⟩
  coordChange_self := by
    intro i x _ d
    ext
    dsimp
    ring
  continuousOn_coordChange := by
    intro i j
    by_cases hn : (A.U i ∩ A.U j).Nonempty
    · obtain ⟨z,hz⟩ := hn
      have hc : Continuous (fun d : DiscreteReal =>
          (⟨d.val+(A.potential i z-A.potential j z)⟩ : DiscreteReal)) := continuous_of_discreteTopology
      apply (hc.comp continuous_snd).continuousOn.congr
      intro p hp
      ext
      dsimp
      have he := A.constant_overlap i j p.1 z hp.1 hz
      linarith
    · have he : (A.U i ∩ A.U j) ×ˢ (univ : Set DiscreteReal) = ∅ := by
        rw [not_nonempty_iff_eq_empty.mp hn,empty_prod]
      rw [he]
      exact continuousOn_empty _
  coordChange_comp := by
    intro i j k x _ d
    ext
    dsimp
    ring



end Atlas
end StrictHotSpots.Primitives

end PrimitiveAtlasInteriorSupportLayer


section SmoothTruncationInteriorSupportLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace StrictHotSpots.Truncation

def trunc (n : ℕ) (t : ℝ) : ℝ := ((n:ℝ)+1) * Real.arctan (t/((n:ℝ)+1))
end StrictHotSpots.Truncation

end SmoothTruncationInteriorSupportLayer



end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Riemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RiemannBiholomorphic





noncomputable section
open Set Filter Metric _root_.Complex Function
open scoped Topology

namespace StrictHotSpots.Riemann

variable {U : Set ℂ}


def extend (f : C(U,ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ U then f ⟨z,hz⟩ else 0

@[simp] lemma extend_coe (f : C(U,ℂ)) (z : U) : extend f z=f z := by
  simp [extend,z.property]

def holomorphicBall (U : Set ℂ) : Set C(U,ℂ) :=
  {f | DifferentiableOn ℂ (extend f) U ∧ ∀ z : U, ‖f z‖ ≤ 1}

end StrictHotSpots.Riemann




noncomputable section
open Set Filter Metric Complex Function
open scoped Topology

namespace StrictHotSpots.Riemann

def normalizedMaps {U : Set ℂ} (a : U) : Set C(U,ℂ) :=
  {f | f ∈ holomorphicBall U ∧ f a=0 ∧ (Injective f ∨ f=0)}

end StrictHotSpots.Riemann




noncomputable section
open Set Filter Metric Complex Function
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Riemann

def mobius (a z : ℂ) : ℂ := (z-a)/(1-conj a*z)

@[simp] lemma mobius_self (a : ℂ) : mobius a a=0 := by simp [mobius]
@[simp] lemma mobius_zero (a : ℂ) : mobius a 0 = -a := by simp [mobius]

end StrictHotSpots.Riemann

end
end
end
end RiemannBiholomorphic


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenSolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section BoundaryHarmonicEnergy

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
local instance instFactLtRealOfNatHMulPi_solutions_1 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

end StrictHotSpots.PlaneGreen
end
end BoundaryHarmonicEnergy


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PhysicalHelmholtz

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PhysicalHelmholtz
variable {Ω : Set Plane} (ho : IsOpen Ω)

lemma subcritical_numeric {μ L C x y z : ℝ} (hμ : 0 ≤ μ) (hl : μ < L)
    (hv : C*x*x ≤ z^2) (hd : L*y^2 ≤ z^2) :
    ((1-μ/L)*C)*x*x ≤ z^2-μ*y^2 := by
  have hL : 0 < L := lt_of_le_of_lt hμ hl
  have hρ : 0 < 1-μ/L := sub_pos.mpr ((div_lt_one hL).mpr hl)
  have hmul := mul_le_mul_of_nonneg_left hd (div_nonneg hμ hL.le)
  have he : μ/L*(L*y^2)=μ*y^2 := by field_simp [ne_of_gt hL]
  rw [he] at hmul
  have hh := mul_le_mul_of_nonneg_left hv hρ.le
  nlinarith

end StrictHotSpots.PhysicalHelmholtz
end
end PhysicalHelmholtz


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Eigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualInteriorEigenSupport



section HelmholtzRadialActualInteriorLayer
noncomputable section
open Set MeasureTheory Metric _root_.Complex Filter Function Real
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Helmholtz


def referenceReal (k : ℝ) (z : ℂ) : ℝ := Real.cos (k*z.re)
def referenceSin (k : ℝ) (z : ℂ) : ℝ := Real.sin (k*z.re)
def reference (μ : ℝ) (z : ℂ) : ℂ := referenceReal (Real.sqrt μ) z

open StrictHotSpots.Weyl



end StrictHotSpots.Helmholtz
end
end HelmholtzRadialActualInteriorLayer


end ActualInteriorEigenSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section MultiplicityComplete

noncomputable section

section PositiveWeightLayer
open Set Filter MeasureTheory Function
open scoped Topology InnerProductSpace
namespace StrictHotSpots.PositiveWeight
variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (μ : Measure X) [IsFiniteMeasure μ]

omit [Nonempty X] [FiniteDimensional ℝ E] in
lemma product_integrable (F : C(X,E)) (f : C(X,ℝ)) : Integrable (fun s => f s • F s) μ :=
  (f.continuous.smul F.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def momentLinear (F : C(X,E)) : C(X,ℝ) →ₗ[ℝ] E where
  toFun f := ∫ s, f s • F s ∂μ
  map_add' f g := by
    simp only [ContinuousMap.add_apply,add_smul]
    exact integral_add (product_integrable μ F f) (product_integrable μ F g)
  map_smul' a f := by
    simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_smul,integral_smul,RingHom.id_apply]

def moment (F : C(X,E)) : C(X,ℝ) →L[ℝ] E :=
  (momentLinear μ F).mkContinuous (‖F‖ * μ.real univ) (fun f => by
    have hh := norm_integral_le_of_norm_le_const (μ := μ)
      (Eventually.of_forall fun s => show ‖f s • F s‖ ≤ ‖f‖*‖F‖ by
        rw [norm_smul]
        exact mul_le_mul (f.norm_coe_le_norm s) (F.norm_coe_le_norm s) (norm_nonneg _) (norm_nonneg _))
    change ‖∫ s, f s • F s ∂μ‖ ≤ _
    nlinarith only [hh])

def probe (F : C(X,E)) : E →ₗ[ℝ] C(X,ℝ) where
  toFun a := ⟨fun s => inner ℝ a (F s),continuous_const.inner F.continuous⟩
  map_add' a b := by
    ext s
    change inner ℝ (a+b) (F s) = inner ℝ a (F s) + inner ℝ b (F s)
    exact inner_add_left _ _ _
  map_smul' c a := by
    ext s
    change inner ℝ (c • a) (F s) = c * inner ℝ a (F s)
    simp only [inner_smul_left,conj_trivial]

def positive : Set C(X,ℝ) := {f | ∀ s, 0 < f s}
end StrictHotSpots.PositiveWeight
end PositiveWeightLayer

end
end MultiplicityComplete


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_TraceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualHilbertContradiction


section

section

section

noncomputable section
open Set Function Module
open scoped InnerProductSpace Topology
namespace StrictHotSpots.HilbertMultipliers

variable {S E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]


def vanishingOn (T : Submodule ℝ (S → E)) (U : Set S) : Submodule ℝ (S → E) where
  carrier := {f | f ∈ T ∧ ∀ x ∈ U, f x = 0}
  zero_mem' := ⟨T.zero_mem,fun _ _ => rfl⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨T.add_mem hf.1 hg.1,fun x hx => by simp [hf.2 x hx,hg.2 x hx]⟩
  smul_mem' := by
    intro c f hf
    exact ⟨T.smul_mem c hf.1,fun x hx => by simp [hf.2 x hx]⟩

end StrictHotSpots.HilbertMultipliers

end
end
end
end
end ActualHilbertContradiction



end OAI
end


