-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SmallJumpProcess_F000
-- name    : LevyStochCalc_Ito_SmallJumpProcess_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:09:43.673664+00:00
-- url     : https://prove2.me/theorems/9f2a228d-168e-4368-ae8e-844472501b27
-- title:
--   Source declarations: LevyStochCalc.Ito.SmallJumpProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SmallJumpProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F001
import Definitions.Def_LevyStochCalc_Ito_Setting_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedCadlagMod_F000
import Definitions.Def_LevyStochCalc_Poisson_SmallJump_F000
import Definitions.Def_SourceProof_091ddfc298ddfc0879414135
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Rat.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Removing the small jumps of a jump diffusion

For a jump diffusion `X` and an antitone family `A : ℕ → Set E` of mark sets whose intersection
is `ν`-null, the *big-jump process* is the path with the compensated integral of the jump
coefficient over `A m` subtracted coordinatewise. The subtracted term is the everywhere-càdlàg
modification of the compensated integral of a mark cut, so its `L²` size is the energy carried
by `A m` and vanishes as `m → ∞`; the big-jump processes therefore converge to the path at every
fixed nonnegative time in `L²`, almost surely along a subsequence, at almost every time of a
bounded window along a subsequence, and — after composing with a `C²` function of time and
state — pathwise along that subsequence.

## Main definitions

* `LevyStochCalc.Ito.SmallJump.JumpIntegrand` — the filtration and admissibility data with
  which the coordinates of the jump coefficient along a path are integrated against `Ñ`.
* `LevyStochCalc.Ito.SmallJump.smallJumpIntegral` — the everywhere-càdlàg modification of the
  compensated integral of one coordinate of the jump coefficient, restricted to the marks
  in `A m`.
* `LevyStochCalc.Ito.SmallJump.bigJumpProcess` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.SmallJump.measurable_uncurry_bigJumpProcess` — joint measurability of a
  coordinate of the big-jump process in the sample point and the time.
* `LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub` — `L²` convergence of
  the big-jump processes to the path at a fixed nonnegative time.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors along a subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors at almost every time of a bounded window, along a
  subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_comp` — the same, transported through a
  `C²` function of time and state.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_drift_bigJumpProcess`,
  `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_quadVar_bigJumpProcess` — pathwise
  convergence of the drift and quadratic-variation integrals along the big-jump processes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.SmallJump

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

/-- The `i`-th coordinate of the jump coefficient of a jump diffusion, evaluated along a path
`Xp`, as an integrand in sample point, time and mark. -/
def pathJumpCoeff (coeffs : JumpDiffusionCoeffs n d E) (Xp : ℝ → Ω → (Fin n → ℝ))
    (i : Fin n) : Ω → ℝ → E → ℝ :=
  fun ω s e => coeffs.γ s (Xp s ω) e i
variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
variable {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The data with which the jump coefficient along a path `Xp` is integrated against the
compensated Poisson random measure of `N`. -/
structure JumpIntegrand (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : JumpDiffusionCoeffs n d E) (Xp : ℝ → Ω → (Fin n → ℝ)) where
  /-- The filtration the integrands are progressively measurable for. -/
  ℱ : Filtration ℝ ‹MeasurableSpace Ω›
  /-- `N` is a Poisson random measure for `ℱ`. -/
  isPoisson : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ
  /-- The path is jointly measurable in time and sample point. -/
  measurable_path : Measurable (Function.uncurry Xp)
  /-- Each coordinate of the jump coefficient along the path is jointly measurable. -/
  meas : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => pathJumpCoeff coeffs Xp i p.1 p.2.1 p.2.2
  /-- Each coordinate of the jump coefficient along the path is progressively measurable. -/
  prog : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable ℱ (pathJumpCoeff coeffs Xp i)
  /-- Each coordinate of the jump coefficient along the path has finite energy on every
  bounded window. -/
  sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖pathJumpCoeff coeffs Xp i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤
/-- The integrand data supplied by the SDE that a jump diffusion solves. -/
noncomputable def JumpIntegrand.ofJumpDiffusion (X : JumpDiffusion W N coeffs x₀) :
    JumpIntegrand N coeffs X.X := by
  choose ℱ _hW hN _hσm _hσp _hσq hγm hγp hγq _hsol using X.is_solution
  exact ⟨ℱ, hN, X.measurable_path, hγm, hγp, hγq⟩
variable {Xp : ℝ → Ω → (Fin n → ℝ)} {A : ℕ → Set E}

/-- The everywhere-càdlàg modification of the compensated integral of the `i`-th coordinate of
the jump coefficient along the path, restricted to the marks in `A m`. -/
noncomputable def smallJumpIntegral (G : JumpIntegrand N coeffs Xp)
    (hA : ∀ m, MeasurableSet (A m))
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)
    (m : ℕ) (i : Fin n) : ℝ → Ω → ℝ :=
  cadlagIntegralPi N G.ℱ G.isPoisson hℱ0 hnull0
    (fun j => markCut (A m) (pathJumpCoeff coeffs Xp j))
    (fun j => measurable_markCut (G.meas j) (hA m))
    (fun j => (_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog j)) (hA m))
    (fun j T' hT' => sq_markCut (G.sq j) (A m) T' hT') i
/-- The path of a jump diffusion with the jumps carried by the marks in `A m` removed. -/
noncomputable def bigJumpProcess (G : JumpIntegrand N coeffs Xp)
    (hA : ∀ m, MeasurableSet (A m))
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)
    (m : ℕ) (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => Xp t ω i - smallJumpIntegral G hA hℱ0 hnull0 m i t ω
section Basic

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)

/-- The big-jump process differs from the path by the compensated integral over the small
marks. -/
theorem bigJumpProcess_sub (m : ℕ) (t : ℝ) (ω : Ω) (i : Fin n) :
    bigJumpProcess G hA hℱ0 hnull0 m t ω i - Xp t ω i
      = -smallJumpIntegral G hA hℱ0 hnull0 m i t ω := by
  change Xp t ω i - smallJumpIntegral G hA hℱ0 hnull0 m i t ω - Xp t ω i = _
  ring
/-- A coordinate of a jointly measurable path at a fixed time is measurable. -/
theorem measurable_pathCoord (hXm : Measurable (Function.uncurry Xp)) (t : ℝ) (i : Fin n) :
    Measurable fun ω => Xp t ω i :=
  (measurable_pi_apply i).comp (hXm.comp (measurable_const.prodMk measurable_id))
/-- The compensated integral over the small marks agrees almost surely, at each time, with the
`L²` Itô–Lévy integral of the mark cut. -/
theorem smallJumpIntegral_ae_eq (m : ℕ) (i : Fin n) (t : ℝ) :
    smallJumpIntegral G hA hℱ0 hnull0 m i t
      =ᵐ[P] stochasticIntegral N G.ℱ G.isPoisson (markCut (A m) (pathJumpCoeff coeffs Xp i))
        (measurable_markCut (G.meas i) (hA m)) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
        (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') t :=
  cadlagIntegral_ae_eq N G.ℱ G.isPoisson (markCut (A m) (pathJumpCoeff coeffs Xp i))
    (measurable_markCut (G.meas i) (hA m)) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
    (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') hℱ0 hnull0 t
/-- The compensated integral over the small marks is adapted to the right-continuous
filtration. -/
theorem adapted_smallJumpIntegral (m : ℕ) (i : Fin n) :
    Adapted G.ℱ.rightCont (smallJumpIntegral G hA hℱ0 hnull0 m i) :=
  cadlagIntegral_adapted N G.ℱ G.isPoisson (markCut (A m) (pathJumpCoeff coeffs Xp i))
    (measurable_markCut (G.meas i) (hA m)) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
    (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') hℱ0 hnull0
/-- The compensated integral over the small marks is measurable at each time. -/
theorem measurable_smallJumpIntegral (m : ℕ) (i : Fin n) (t : ℝ) :
    Measurable (smallJumpIntegral G hA hℱ0 hnull0 m i t) :=
  (adapted_smallJumpIntegral G hA hℱ0 hnull0 m i t).mono (G.ℱ.rightCont.le t) le_rfl
/-- A coordinate of the big-jump process at a fixed time is measurable. -/
theorem measurable_bigJumpProcess (m : ℕ) (t : ℝ) (i : Fin n) :
    Measurable fun ω => bigJumpProcess G hA hℱ0 hnull0 m t ω i :=
  (measurable_pathCoord G.measurable_path t i).sub
    (measurable_smallJumpIntegral G hA hℱ0 hnull0 m i t)
/-- Every path of the compensated integral over the small marks is right-continuous. -/
theorem rightContinuous_smallJumpIntegral (m : ℕ) (i : Fin n) (ω : Ω) (t : ℝ) :
    Tendsto (fun s => smallJumpIntegral G hA hℱ0 hnull0 m i s ω) (𝓝[>] t)
      (𝓝 (smallJumpIntegral G hA hℱ0 hnull0 m i t ω)) :=
  cadlagIntegral_rightContinuous N G.ℱ G.isPoisson
    (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
    ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
    (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') hℱ0 hnull0 ω t
/-- Every path of the compensated integral over the small marks has a left limit at every
time. -/
theorem exists_leftLim_smallJumpIntegral (m : ℕ) (i : Fin n) (ω : Ω) (t : ℝ) :
    ∃ L : ℝ, Tendsto (fun s => smallJumpIntegral G hA hℱ0 hnull0 m i s ω) (𝓝[<] t) (𝓝 L) :=
  cadlagIntegral_exists_leftLim N G.ℱ G.isPoisson
    (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
    ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
    (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') hℱ0 hnull0 ω t
/-- The paths of the compensated integral over the small marks are almost surely càdlàg. -/
theorem ae_cadlag_smallJumpIntegral (m : ℕ) (i : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => smallJumpIntegral G hA hℱ0 hnull0 m i s ω) (𝓝[>] t)
          (𝓝 (smallJumpIntegral G hA hℱ0 hnull0 m i t ω))
        ∧ ∃ L : ℝ,
            Tendsto (fun s => smallJumpIntegral G hA hℱ0 hnull0 m i s ω) (𝓝[<] t) (𝓝 L) :=
  Filter.Eventually.of_forall fun ω t =>
    ⟨rightContinuous_smallJumpIntegral G hA hℱ0 hnull0 m i ω t,
      exists_leftLim_smallJumpIntegral G hA hℱ0 hnull0 m i ω t⟩
/-- The compensated integral over the small marks is jointly measurable in the sample point and
the time. -/
theorem measurable_uncurry_smallJumpIntegral (m : ℕ) (i : Fin n) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      smallJumpIntegral G hA hℱ0 hnull0 m i s ω) :=
  measurable_uncurry_cadlagIntegral N G.ℱ G.isPoisson
    (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
    ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
    (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') hℱ0 hnull0
/-- A coordinate of the big-jump process is jointly measurable in the sample point and the
time. -/
theorem measurable_uncurry_bigJumpProcess (m : ℕ) (i : Fin n) :
    Measurable (Function.uncurry fun ω s => bigJumpProcess G hA hℱ0 hnull0 m s ω i) := by
  have hM := measurable_uncurry_smallJumpIntegral G hA hℱ0 hnull0 m i
  have hX : Measurable fun p : Ω × ℝ => Xp p.2 p.1 i :=
    (measurable_pi_apply i).comp (G.measurable_path.comp measurable_swap)
  exact hX.sub hM
/-- The big-jump vectors are jointly measurable in the sample point and the time. -/
theorem measurable_uncurry_bigJumpProcess_pi (m : ℕ) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      bigJumpProcess G hA hℱ0 hnull0 m s ω) :=
  measurable_pi_lambda _ fun i => measurable_uncurry_bigJumpProcess G hA hℱ0 hnull0 m i
/-- The squared compensated integral over the small marks is jointly measurable in the sample
point and the time. -/
theorem measurable_uncurry_sq_smallJumpIntegral (m : ℕ) (i : Fin n) :
    Measurable fun q : Ω × ℝ =>
      (‖smallJumpIntegral G hA hℱ0 hnull0 m i q.2 q.1‖₊ : ℝ≥0∞) ^ 2 :=
  (((measurable_uncurry_smallJumpIntegral G hA hℱ0 hnull0 m
    i).nnnorm).coe_nnreal_ennreal).pow_const 2
/-- The squared error between a coordinate of the big-jump process and the path is jointly
measurable in the sample point and the time. -/
theorem measurable_uncurry_sq_bigJumpProcess_sub (m : ℕ) (i : Fin n) :
    Measurable fun q : Ω × ℝ =>
      (‖bigJumpProcess G hA hℱ0 hnull0 m q.2 q.1 i - Xp q.2 q.1 i‖₊ : ℝ≥0∞) ^ 2 := by
  have hB : Measurable fun q : Ω × ℝ => bigJumpProcess G hA hℱ0 hnull0 m q.2 q.1 i :=
    measurable_uncurry_bigJumpProcess G hA hℱ0 hnull0 m i
  have hX : Measurable fun q : Ω × ℝ => Xp q.2 q.1 i :=
    (measurable_pi_apply i).comp (G.measurable_path.comp measurable_swap)
  exact (((hB.sub hX).nnnorm).coe_nnreal_ennreal).pow_const 2
/-- The squared error between a coordinate of the big-jump process and the path is measurable in
the time, at each sample point. -/
theorem measurable_sq_bigJumpProcess_sub_time (m : ℕ) (i : Fin n) (ω : Ω) :
    Measurable fun s : ℝ =>
      (‖bigJumpProcess G hA hℱ0 hnull0 m s ω i - Xp s ω i‖₊ : ℝ≥0∞) ^ 2 := by
  have hB : Measurable fun s : ℝ => bigJumpProcess G hA hℱ0 hnull0 m s ω i :=
    Measurable.of_uncurry_left (measurable_uncurry_bigJumpProcess G hA hℱ0 hnull0 m i)
  have hX : Measurable fun s : ℝ => Xp s ω i :=
    (measurable_pi_apply i).comp
      (G.measurable_path.comp (measurable_id.prodMk measurable_const))
  exact (((hB.sub hX).nnnorm).coe_nnreal_ennreal).pow_const 2
/-- The energy over a bounded window of the error between a coordinate of the big-jump process
and the path is measurable in the sample point. -/
theorem measurable_lintegral_sq_bigJumpProcess_sub (m : ℕ) (i : Fin n) (T : ℝ) :
    Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bigJumpProcess G hA hℱ0 hnull0 m s ω i - Xp s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
  (measurable_uncurry_sq_bigJumpProcess_sub G hA hℱ0 hnull0 m i).lintegral_prod_right'
/-- At nonpositive times the compensated integral over the small marks vanishes almost
surely. -/
theorem smallJumpIntegral_ae_zero (m : ℕ) (i : Fin n) {t : ℝ} (ht : t ≤ 0) :
    smallJumpIntegral G hA hℱ0 hnull0 m i t =ᵐ[P] 0 :=
  (smallJumpIntegral_ae_eq G hA hℱ0 hnull0 m i t).trans
    ((stochasticIntegral_ae_eq_process N G.ℱ G.isPoisson
          (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
          ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
          (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') t).trans
      (_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N G.ℱ G.isPoisson _ _ _ _ ht))
end Basic

section Limits

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)

/-- The compensated integrals over a shrinking family of marks tend to `0` in `L²`. -/
theorem tendsto_lintegral_sq_smallJumpIntegral (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) (i : Fin n) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun m => ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hrw : ∀ m : ℕ,
      ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖stochasticIntegral N G.ℱ G.isPoisson
            (markCut (A m) (pathJumpCoeff coeffs Xp i))
            (measurable_markCut (G.meas i) (hA m)) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (G.prog i)) (hA m))
            (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro m
    refine lintegral_congr_ae ?_
    filter_upwards [smallJumpIntegral_ae_eq G hA hℱ0 hnull0 m i t] with ω hω
    rw [hω]
  simp_rw [hrw]
  exact _root_.Prove2MeSourceProof.h_091ddfc298ddfc0879414135 N G.ℱ G.isPoisson
    (pathJumpCoeff coeffs Xp i) (G.meas i) (G.prog i) (G.sq i) A hA hanti hnull ht
end Limits

end LevyStochCalc.Ito.SmallJump


