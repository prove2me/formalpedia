-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CappedJumpSumMeasurable_F000
-- name    : LevyStochCalc_Ito_CappedJumpSumMeasurable_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:08:59.942313+00:00
-- url     : https://prove2.me/theorems/e1d4d8d8-938f-491b-b515-960d00d1e10f
-- title:
--   Source declarations: LevyStochCalc.Ito.CappedJumpSumMeasurable
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CappedJumpSumMeasurable. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftAtomSum_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F002
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F003
import Definitions.Def_SourceProof_6bebe70af91e345e56c64c09
import Definitions.Def_SourceProof_f0e19fe5080e26942cb86e6b
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Measurability of the capped jump sum

The jumps of a mark set accumulated up to an arrival time capped at the horizon, with the jump
coefficient read at the left limits of the path, form a random vector known at that capped
arrival time. The pathwise jump sum over a window is the integral against the random measure of
the jump coefficient at the left limits, which is a predictable marked process; restricting the
random measure to a window on which its mass is finite everywhere gives an s-finite kernel, and
integrals of jointly measurable integrands against an s-finite kernel are measurable. The jump
sum is therefore progressively measurable in the time and the sample point, and its value at
the capped arrival time — a stopping time — is measurable for the σ-algebra of that stopping
time. Without the pathwise finiteness of the count the same integral is only almost surely equal
to a measurable function, which gives almost-everywhere measurability.

## Main definitions

* `LevyStochCalc.Poisson.windowKernel` — a family of measures restricted to a window and set to
  zero at the sample points where the window carries infinite mass, as a kernel.
* `LevyStochCalc.Ito.JumpFormula.leftLimJumpCoeff` — the jump coefficient at the left limits of
  the path, cut to the positive times up to a horizon, on the sample–time–mark space.

## Main statements

* `LevyStochCalc.Poisson.isSFiniteKernel_windowKernel`,
  `LevyStochCalc.Poisson.measurable_integral_windowKernel`,
  `LevyStochCalc.Poisson.measurable_integral_windowKernel_indicator` — the window kernel is
  s-finite, so integrals of jointly measurable integrands against it are measurable.
* `LevyStochCalc.Ito.JumpFormula.jumpSumAt_leftLimPath_eq_integral_windowKernel` — where the
  window count is finite, the left-limit jump sum is the integral against the window kernel.
* `LevyStochCalc.Ito.JumpFormula.isStronglyProgressive_jumpSumAt_leftLimPath`,
  `LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_jumpSumAt_leftLimPath` — the
  left-limit jump sum is progressively measurable when the count is finite everywhere.
* `LevyStochCalc.Ito.JumpFormula.measurable_cappedJumpSumAt_leftLimPath` — the capped
  left-limit jump sum is measurable when the count is finite everywhere.
* `LevyStochCalc.Ito.JumpFormula.measurable_cappedJumpSumAt_leftLimPath_of_isStoppingTime` —
  the capped left-limit jump sum is measurable for the σ-algebra of the capped arrival time.
* `LevyStochCalc.Ito.JumpFormula.aemeasurable_cappedJumpSumAt_leftLimPath` — for a mark set of
  finite intensity the capped left-limit jump sum is almost-everywhere measurable.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §2.3, §4.4.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

section WindowKernel

variable {Ω β : Type*} {m : MeasurableSpace Ω} [MeasurableSpace β]

/-- A family of measures restricted to a window and set to zero at the sample points where the
window carries infinite mass, as a kernel. -/
noncomputable def windowKernel (μ : Ω → Measure β) (R : Set β)
    (hμ : ∀ ⦃s : Set β⦄, MeasurableSet s → Measurable fun ω => μ ω (s ∩ R)) : Kernel Ω β where
  toFun ω := if μ ω R = ⊤ then 0 else (μ ω).restrict R
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have hR : Measurable fun ω => μ ω R := by simpa using hμ MeasurableSet.univ
    have hfun : (fun ω => (if μ ω R = ⊤ then (0 : Measure β) else (μ ω).restrict R) s)
        = fun ω => if μ ω R = ⊤ then 0 else μ ω (s ∩ R) := by
      funext ω
      split_ifs <;> simp [Measure.restrict_apply hs]
    rw [hfun]
    exact Measurable.ite (hR (measurableSet_singleton ⊤)) measurable_const (hμ hs)
variable {μ : Ω → Measure β} {R : Set β}
  {hμ : ∀ ⦃s : Set β⦄, MeasurableSet s → Measurable fun ω => μ ω (s ∩ R)}

theorem windowKernel_apply (ω : Ω) :
    windowKernel μ R hμ ω = if μ ω R = ⊤ then 0 else (μ ω).restrict R := rfl
/-- Where the window carries finite mass the window kernel is the restricted measure. -/
theorem windowKernel_apply_of_ne_top {ω : Ω} (h : μ ω R ≠ ⊤) :
    windowKernel μ R hμ ω = (μ ω).restrict R := by
  rw [windowKernel_apply, if_neg h]
/-- The part of the window kernel carried by the sample points whose window mass has integer
part `n`. -/
noncomputable def windowKernelSlice (μ : Ω → Measure β) (R : Set β)
    (hμ : ∀ ⦃s : Set β⦄, MeasurableSet s → Measurable fun ω => μ ω (s ∩ R)) (n : ℕ) :
    Kernel Ω β where
  toFun ω := if μ ω R ≠ ⊤ ∧ ⌊(μ ω R).toReal⌋₊ = n then (μ ω).restrict R else 0
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have hR : Measurable fun ω => μ ω R := by simpa using hμ MeasurableSet.univ
    have hset : MeasurableSet {ω | μ ω R ≠ ⊤ ∧ ⌊(μ ω R).toReal⌋₊ = n} :=
      (hR (measurableSet_singleton ⊤)).compl.inter
        (hR.ennreal_toReal.nat_floor (measurableSet_singleton n))
    have hfun : (fun ω => (if μ ω R ≠ ⊤ ∧ ⌊(μ ω R).toReal⌋₊ = n then (μ ω).restrict R
          else (0 : Measure β)) s)
        = fun ω => if μ ω R ≠ ⊤ ∧ ⌊(μ ω R).toReal⌋₊ = n then μ ω (s ∩ R) else 0 := by
      funext ω
      split_ifs <;> simp [Measure.restrict_apply hs]
    rw [hfun]
    exact Measurable.ite hset (hμ hs) measurable_const
theorem windowKernelSlice_apply (n : ℕ) (ω : Ω) :
    windowKernelSlice μ R hμ n ω
      = if μ ω R ≠ ⊤ ∧ ⌊(μ ω R).toReal⌋₊ = n then (μ ω).restrict R else 0 := rfl
instance isFiniteKernel_windowKernelSlice (n : ℕ) :
    IsFiniteKernel (windowKernelSlice μ R hμ n) := by
  refine ⟨⟨(n : ℝ≥0∞) + 1,
    ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top n, ENNReal.one_lt_top⟩, fun ω => ?_⟩⟩
  rw [windowKernelSlice_apply]
  split_ifs with h
  · rw [Measure.restrict_apply_univ]
    obtain ⟨hne, hfl⟩ := h
    calc μ ω R = ENNReal.ofReal (μ ω R).toReal := (ENNReal.ofReal_toReal hne).symm
      _ ≤ ENNReal.ofReal ((n : ℝ) + 1) :=
          ENNReal.ofReal_le_ofReal (by rw [← hfl]; exact (Nat.lt_floor_add_one _).le)
      _ = (n : ℝ≥0∞) + 1 := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one]
  · simp
/-- The window kernel is the sum of its slices. -/
theorem windowKernel_eq_sum : windowKernel μ R hμ = Kernel.sum (windowKernelSlice μ R hμ) := by
  ext ω s hs
  rw [Kernel.sum_apply' _ _ hs, windowKernel_apply]
  simp only [windowKernelSlice_apply]
  by_cases htop : μ ω R = ⊤
  · simp [htop]
  · have hsingle : ∀ n, n ≠ ⌊(μ ω R).toReal⌋₊ →
        (if μ ω R ≠ ⊤ ∧ ⌊(μ ω R).toReal⌋₊ = n then (μ ω).restrict R else (0 : Measure β)) s
          = 0 := by
      intro n hn
      rw [if_neg (fun h => hn h.2.symm)]
      simp
    rw [if_neg htop, tsum_eq_single _ hsingle, if_pos ⟨htop, rfl⟩]
/-- The window kernel is s-finite. -/
instance isSFiniteKernel_windowKernel : IsSFiniteKernel (windowKernel μ R hμ) :=
  ⟨⟨windowKernelSlice μ R hμ, fun _ => inferInstance, windowKernel_eq_sum⟩⟩
/-- The integral of a jointly measurable integrand against the window kernel, read along a
measurable map into the sample space, is measurable. -/
theorem measurable_integral_windowKernel {α : Type*} [MeasurableSpace α] {g : α → Ω}
    (hg : Measurable g) {F : α × β → ℝ} (hF : Measurable F) :
    Measurable fun a => ∫ q, F (a, q) ∂(windowKernel μ R hμ (g a)) := by
  have h := hF.stronglyMeasurable.integral_kernel_prod_right'
    (κ := (windowKernel μ R hμ).comap g hg)
  simpa only [Kernel.comap_apply] using h.measurable
end WindowKernel

section WindowIndicator

variable {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E] {μ : Ω → Measure (ℝ × E)}
  {R : Set (ℝ × E)} {hμ : ∀ ⦃s : Set (ℝ × E)⦄, MeasurableSet s → Measurable fun ω => μ ω (s ∩ R)}

/-- The integral over a measurably varying time–mark window of a jointly measurable integrand
against the window kernel, read along a measurable map into the sample space, is measurable. -/
theorem measurable_integral_windowKernel_indicator {A : Set E} (hA : MeasurableSet A)
    {G : Ω × (ℝ × E) → ℝ} (hG : Measurable G) {α : Type*} [MeasurableSpace α] {g : α → Ω}
    (hg : Measurable g) {r : α → ℝ} (hr : Measurable r) :
    Measurable fun a => ∫ q, (Set.Ioc (0 : ℝ) (r a) ×ˢ A).indicator (fun q => G (g a, q)) q
      ∂(windowKernel μ R hμ (g a)) := by
  have hfun : Measurable fun p : α × (ℝ × E) => G (g p.1, p.2) :=
    hG.comp ((hg.comp measurable_fst).prodMk measurable_snd)
  have hset : MeasurableSet {p : α × (ℝ × E) | p.2 ∈ Set.Ioc (0 : ℝ) (r p.1) ×ˢ A} :=
    ((measurableSet_lt measurable_const measurable_snd.fst).inter
      (measurableSet_le measurable_snd.fst (hr.comp measurable_fst))).inter
      (measurable_snd.snd hA)
  have hF : Measurable fun p : α × (ℝ × E) =>
      (Set.Ioc (0 : ℝ) (r p.1) ×ˢ A).indicator (fun q => G (g p.1, q)) p.2 := by
    have hrw : (fun p : α × (ℝ × E) =>
        (Set.Ioc (0 : ℝ) (r p.1) ×ˢ A).indicator (fun q => G (g p.1, q)) p.2)
        = {p : α × (ℝ × E) | p.2 ∈ Set.Ioc (0 : ℝ) (r p.1) ×ˢ A}.indicator
            fun p => G (g p.1, p.2) := by
      funext p
      by_cases hp : p.2 ∈ Set.Ioc (0 : ℝ) (r p.1) ×ˢ A
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (Set.mem_setOf_eq ▸ hp)]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (Set.mem_setOf_eq ▸ hp)]
    rw [hrw]
    exact hfun.indicator hset
  exact measurable_integral_windowKernel hg hF
end WindowIndicator

end LevyStochCalc.Poisson

namespace LevyStochCalc.Ito.JumpFormula

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
variable {A : Set E}

section Clip

omit [MeasurableSpace Ω] in
/-- The horizon clipped at a time is the time capped at the horizon, read back as a real. -/
theorem clipTime_eq_untopA_min (τ : Ω → WithTop ℝ) (t : ℝ) (ω : Ω) :
    LevyStochCalc.Brownian.Ito.clipTime τ t ω = (min (τ ω) ((t : ℝ) : WithTop ℝ)).untopA := by
  by_cases h : ((t : ℝ) : WithTop ℝ) ≤ τ ω
  · rw [LevyStochCalc.Brownian.Ito.clipTime_of_le h, min_eq_right h]
    rfl
  · have hne : τ ω ≠ ⊤ := fun htop => h (by rw [htop]; exact le_top)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [LevyStochCalc.Brownian.Ito.clipTime_eq_min hr.symm, ← hr, ← WithTop.coe_min]
    exact min_comm t r
/-- The `k`-th arrival time clipped at the horizon is measurable. -/
theorem measurable_clipTime_jumpTime (hA : MeasurableSet A) (T : ℝ) (k : ℕ) :
    Measurable (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T) := by
  have hτ : Measurable (LevyStochCalc.Poisson.jumpTime N A k) :=
    (LevyStochCalc.Poisson.isStoppingTime_jumpTime_rightCont N A
      (LevyStochCalc.Poisson.isPoissonFiltration_natural N) hA k).measurable'
  unfold LevyStochCalc.Brownian.Ito.clipTime
  exact Measurable.ite (hτ measurableSet_Ici) measurable_const (hτ.untopD T)
/-- The arrival times capped at the horizon are stopping times for a filtration for which `N`
is a Poisson random measure, when the count is finite everywhere. -/
theorem isStoppingTime_cappedJumpTime_of_forall_ne_top {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), LevyStochCalc.Poisson.arrivalCount N A t ω ≠ ⊤) (T : ℝ)
    (k : ℕ) : IsStoppingTime ℱ (cappedJumpTime N A T k) :=
  (_root_.Prove2MeSourceProof.h_f0e19fe5080e26942cb86e6b N A hℱ hA hfin k).min_const T
end Clip

section Integrand

variable (X : Setting.JumpDiffusion W N coeffs x₀)

/-- The jump coefficient at the left limits of the path, cut to the positive times up to `t`,
as a function on the sample–time–mark space. -/
noncomputable def leftLimJumpCoeff (t : ℝ) (i : Fin n) (p : Ω × ℝ × E) : ℝ :=
  (Set.Iic t).indicator
    (fun s => if 0 < s then coeffs.γ s (JumpSplitting.leftLimPathPos X s p.1) p.2.2 i else 0)
    p.2.1
/-- On a window of positive times up to `t` the cut jump coefficient is the jump coefficient at
the left limits of the path. -/
theorem leftLimJumpCoeff_of_mem {t : ℝ} {i : Fin n} {ω : Ω} {q : ℝ × E} (h0 : 0 < q.1)
    (ht : q.1 ≤ t) :
    leftLimJumpCoeff X t i (ω, q) = coeffs.γ q.1 (JumpSplitting.leftLimPath X q.1 ω) q.2 i := by
  change (Set.Iic t).indicator
    (fun s => if 0 < s then coeffs.γ s (JumpSplitting.leftLimPathPos X s ω) q.2 i else 0) q.1
      = _
  rw [Set.indicator_of_mem (Set.mem_Iic.mpr ht), if_pos h0, JumpSplitting.leftLimPathPos,
    if_pos h0]
/-- The cut jump coefficient at the left limits of an adapted path is measurable for the
product of the σ-algebra at `t` with the Borel σ-algebra of the time–mark space. -/
theorem measurable_leftLimJumpCoeff (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    {i : Fin n} (hγi : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i)
    (t : ℝ) :
    Measurable[@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance]
      (leftLimJumpCoeff X t i) :=
  ((_root_.Prove2MeSourceProof.h_6bebe70af91e345e56c64c09 (_root_.Prove2MeSourceProof.h_a284e225504f48706843f4e8 (ν := ν)
    (_root_.Prove2MeSourceProof.h_c5cf45bd11a3d53a89dd04c6 X ℱ hXadapt hleft)
    (f := fun s x e => coeffs.γ s x e i) hγi)) t).measurable
/-- The counts of a Poisson random measure on the measurable subsets of a window are measurable
for the σ-algebra at the window's horizon of a filtration for which `N` is a Poisson random
measure. -/
theorem measurable_count_inter_window {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (t : ℝ) :
    ∀ ⦃s : Set (ℝ × E)⦄, MeasurableSet s →
      Measurable[ℱ t] fun ω => N.N ω (s ∩ Set.Ioc (0 : ℝ) t ×ˢ A) :=
  fun _ hs => hℱ.measurable (fun _ hq => ⟨hq.2.1.2, Set.mem_univ _⟩)
    (hs.inter (measurableSet_Ioc.prod hA))
/-- The counts of a Poisson random measure on the measurable subsets of a window are
measurable. -/
theorem measurable_count_inter_window' (hA : MeasurableSet A) (t : ℝ) :
    ∀ ⦃s : Set (ℝ × E)⦄, MeasurableSet s →
      Measurable fun ω => N.N ω (s ∩ Set.Ioc (0 : ℝ) t ×ˢ A) :=
  fun _ hs => N.measurable_eval (hs.inter (measurableSet_Ioc.prod hA))
/-- Where the window count is finite, the left-limit jump sum over a sub-window is the integral
of the cut jump coefficient over that sub-window against the window kernel. -/
theorem jumpSumAt_leftLimPath_eq_integral_windowKernel (hA : MeasurableSet A)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {t : ℝ}
    {hμ : ∀ ⦃s : Set (ℝ × E)⦄, MeasurableSet s →
      Measurable[ℱ t] fun ω => N.N ω (s ∩ Set.Ioc (0 : ℝ) t ×ˢ A)}
    {s : ℝ} (hst : s ≤ t) {ω : Ω} (hω : N.N ω (Set.Ioc (0 : ℝ) t ×ˢ A) ≠ ⊤) (i : Fin n) :
    jumpSumAt X (JumpSplitting.leftLimPath X) A s ω i
      = ∫ q, (Set.Ioc (0 : ℝ) s ×ˢ A).indicator (fun q => leftLimJumpCoeff X t i (ω, q)) q
          ∂(LevyStochCalc.Poisson.windowKernel N.N (Set.Ioc (0 : ℝ) t ×ˢ A) hμ ω) := by
  rw [LevyStochCalc.Poisson.windowKernel_apply_of_ne_top hω,
    integral_indicator (measurableSet_Ioc.prod hA),
    Measure.restrict_restrict (measurableSet_Ioc.prod hA),
    Set.inter_eq_left.mpr (Set.prod_mono (Set.Ioc_subset_Ioc_right hst) le_rfl)]
  unfold jumpSumAt
  refine setIntegral_congr_fun (measurableSet_Ioc.prod hA) fun q hq => ?_
  rw [leftLimJumpCoeff_of_mem X hq.1.1 (hq.1.2.trans hst)]
end Integrand

section Progressive

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- **The left-limit jump sum is progressively measurable**, for a filtration for which `N` is a
Poisson random measure and the path is adapted, when the count is finite everywhere. -/
theorem isStronglyProgressive_jumpSumAt_leftLimPath
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), LevyStochCalc.Poisson.arrivalCount N A t ω ≠ ⊤)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2) :
    IsStronglyProgressive ℱ fun s ω => jumpSumAt X (JumpSplitting.leftLimPath X) A s ω := by
  intro t
  have hμ := measurable_count_inter_window hℱ hA t
  have hG : ∀ i : Fin n, Measurable[@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance]
      (leftLimJumpCoeff X t i) := fun i =>
    measurable_leftLimJumpCoeff X ℱ hXadapt hleft ((measurable_pi_apply i).comp hγ) t
  have hid : ∀ i : Fin n,
      (fun p : Set.Iic t × Ω => jumpSumAt X (JumpSplitting.leftLimPath X) A p.1 p.2 i)
        = fun p => ∫ q, (Set.Ioc (0 : ℝ) (p.1 : ℝ) ×ˢ A).indicator
            (fun q => leftLimJumpCoeff X t i (p.2, q)) q
          ∂(LevyStochCalc.Poisson.windowKernel N.N (Set.Ioc (0 : ℝ) t ×ˢ A) hμ p.2) :=
    fun i => funext fun p =>
      jumpSumAt_leftLimPath_eq_integral_windowKernel X hA ℱ p.1.2 (hfin p.2 t) i
  letI : MeasurableSpace Ω := ℱ t
  refine Measurable.stronglyMeasurable (measurable_pi_iff.mpr fun i => ?_)
  have hkey := LevyStochCalc.Poisson.measurable_integral_windowKernel_indicator (hμ := hμ) hA
    (hG i) (α := Set.Iic t × Ω) (g := Prod.snd) measurable_snd (r := fun p => (p.1 : ℝ))
    (measurable_subtype_coe.comp measurable_fst)
  beta_reduce
  rw [hid i]
  exact hkey
/-- **The coordinates of the left-limit jump sum are progressively measurable**, for a
filtration for which `N` is a Poisson random measure and the path is adapted, when the count is
finite everywhere. -/
theorem progressivelyMeasurable_jumpSumAt_leftLimPath
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), LevyStochCalc.Poisson.arrivalCount N A t ω ≠ ⊤)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2) (i : Fin n) :
    LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      fun ω s => jumpSumAt X (JumpSplitting.leftLimPath X) A s ω i := by
  intro t
  have hμ := measurable_count_inter_window hℱ hA t
  have hG : Measurable[@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance]
      (leftLimJumpCoeff X t i) :=
    measurable_leftLimJumpCoeff X ℱ hXadapt hleft ((measurable_pi_apply i).comp hγ) t
  have hid : (fun p : Ω × ℝ =>
      (Set.Iic t).indicator (fun s => jumpSumAt X (JumpSplitting.leftLimPath X) A s p.1 i) p.2)
      = fun p : Ω × ℝ => if p.2 ≤ t then
          ∫ q, (Set.Ioc (0 : ℝ) p.2 ×ˢ A).indicator (fun q => leftLimJumpCoeff X t i (p.1, q)) q
            ∂(LevyStochCalc.Poisson.windowKernel N.N (Set.Ioc (0 : ℝ) t ×ˢ A) hμ p.1)
        else 0 := by
    funext p
    by_cases hp : p.2 ≤ t
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hp), if_pos hp]
      exact jumpSumAt_leftLimPath_eq_integral_windowKernel X hA ℱ hp (hfin p.1 t) i
    · rw [Set.indicator_of_notMem (fun h => hp (Set.mem_Iic.mp h)), if_neg hp]
  letI : MeasurableSpace Ω := ℱ t
  refine Measurable.stronglyMeasurable ?_
  have hkey := LevyStochCalc.Poisson.measurable_integral_windowKernel_indicator (hμ := hμ) hA hG
    (α := Ω × ℝ) (g := Prod.fst) measurable_fst (r := Prod.snd) measurable_snd
  rw [hid]
  exact Measurable.ite (measurableSet_le measurable_snd measurable_const) hkey measurable_const
end Progressive

section Capped

variable (X : Setting.JumpDiffusion W N coeffs x₀)

end Capped

end LevyStochCalc.Ito.JumpFormula


