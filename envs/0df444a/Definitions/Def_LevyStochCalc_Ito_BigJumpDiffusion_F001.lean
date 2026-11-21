-- Prove2me | Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F001
-- name    : LevyStochCalc_Ito_BigJumpDiffusion_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:25:51.844073+00:00
-- url     : https://prove2.me/theorems/ea7ad6f4-cb72-48aa-a22c-c773bfd9247c
-- title:
--   Source declarations: LevyStochCalc.Ito.BigJumpDiffusion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.BigJumpDiffusion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncating the jumps of a jump diffusion at one mark set

Restricting the jump coefficient of a jump diffusion to a measurable set of marks `A` splits it
into two coefficient bundles, and the compensated integral of an admissible integrand splits
accordingly. Subtracting the everywhere-càdlàg modification of the compensated integral over `A`
from the path leaves the *big-jump path*, which carries the drift, the diffusion and the jumps
outside `A`.

## Main definitions

* `LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.markCutγ` — the coefficient bundle with the jump
  coefficient restricted to a set of marks.
* `LevyStochCalc.Ito.BigJump.SdeData` — the filtration and admissibility data with which a jump
  diffusion satisfies its SDE.
* `LevyStochCalc.Ito.BigJump.cutJumpIntegral` — the everywhere-càdlàg modification of the
  compensated integral of the jump coefficient restricted to a set of marks.
* `LevyStochCalc.Ito.BigJump.bigJumpPath` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl` — the compensated integral of
  an integrand is the sum of the compensated integrals of its two mark cuts.
* `LevyStochCalc.Ito.BigJump.lintegral_sq_iSup_bigJumpPath_lt_top` — the big-jump path has
  square-integrable supremum over every bounded window.
* `LevyStochCalc.Ito.BigJump.isItoLevyProcess_bigJumpPath` — the big-jump path is an Itô–Lévy
  process whose drift and diffusion are those of the jump diffusion along its own path and whose
  jump integrand is the jump coefficient restricted to the complement of the cut.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.Setting

universe v

variable {n d : ℕ} {E : Type v}

end LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.BigJump

universe u v

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.SmallJump

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

section Split

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)

end Split

section Data

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The filtration and admissibility data with which a jump diffusion satisfies its SDE: the
contents of the `is_solution` field, named. -/
structure SdeData (X : JumpDiffusion W N coeffs x₀) where
  /-- The filtration the integrands are progressively measurable for. -/
  ℱ : Filtration ℝ ‹MeasurableSpace Ω›
  /-- Every coordinate of `W` is a Brownian motion for `ℱ`. -/
  isBrownian : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ
  /-- `N` is a Poisson random measure for `ℱ`. -/
  isPoisson : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ
  /-- The diffusion coefficient along the path is jointly measurable, entrywise. -/
  σ_meas : ∀ i : Fin n, ∀ j : Fin d,
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j)
  /-- The diffusion coefficient along the path is progressively measurable, entrywise. -/
  σ_prog : ∀ i : Fin n, ∀ j : Fin d,
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j
  /-- The diffusion coefficient along the path has finite energy on every bounded window. -/
  σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤
  /-- The jump coefficient along the path is jointly measurable, coordinatewise. -/
  γ_meas : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => pathJumpCoeff coeffs X.X i p.1 p.2.1 p.2.2
  /-- The jump coefficient along the path is marked progressively measurable. -/
  γ_prog : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable ℱ (pathJumpCoeff coeffs X.X i)
  /-- The jump coefficient along the path has finite energy on every bounded window. -/
  γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖pathJumpCoeff coeffs X.X i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤
  /-- The path is progressively measurable for the filtration it solves against.

  This is part of the specification of a solution, not a consequence of the equation: the
  literature (Applebaum 6.2.9, Ikeda–Watanabe IV) asks a solution to be adapted, and the
  equation alone does not give it, since the drift term `∫_0^t μ(s, X_s) ds` is measurable for
  `ℱ t` only once the path already is. -/
  X_prog : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X.X s ω i
  /-- The SDE integral equation, almost surely at every nonnegative time. -/
  sde : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
    X.X t ω i = x₀ i
      + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
      + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
          W ℱ isBrownian (fun s ω => coeffs.σ s (X.X s ω) i)
          (fun j => σ_meas i j) (fun j => σ_prog i j) (fun j => σ_sq i j) t ω
      + stochasticIntegral N ℱ isPoisson (pathJumpCoeff coeffs X.X i)
          (γ_meas i) (γ_prog i) (γ_sq i) t ω
/-! `SdeData` is **not** derivable from `JumpDiffusion` alone: the structure's `is_solution`
field bundles the equation and the integrand admissibility but no adaptedness of the path, and
`X_prog` does not follow from them. It is supplied where a solution is built, by
`LevyStochCalc.Ito.BigJump.SdeData.ofSolvesOn` (`Ito/SdeDataOfSolvesOn.lean`). -/

/-- The jump-integrand data underlying the SDE data. -/
def SdeData.toJumpIntegrand {X : JumpDiffusion W N coeffs x₀} (S : SdeData X) :
    JumpIntegrand N coeffs X.X :=
  ⟨S.ℱ, S.isPoisson, X.measurable_path, S.γ_meas, S.γ_prog, S.γ_sq⟩
end Data

section Path

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

/-- The everywhere-càdlàg modification of the compensated integral of the `i`-th coordinate of
the jump coefficient along the path, restricted to the marks in `A`. -/
noncomputable def cutJumpIntegral (S : SdeData X) {A : Set E} (hA : MeasurableSet A)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (i : Fin n) : ℝ → Ω → ℝ :=
  cadlagIntegralPi N S.ℱ S.isPoisson hℱ0 hnull0
    (fun j => markCut A (pathJumpCoeff coeffs X.X j))
    (fun j => measurable_markCut (S.γ_meas j) hA)
    (fun j => (_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog j)) hA)
    (fun j T' hT' => sq_markCut (S.γ_sq j) A T' hT') i
/-- The path of a jump diffusion with the jumps carried by the marks in `A` removed. -/
noncomputable def bigJumpPath (S : SdeData X) {A : Set E} (hA : MeasurableSet A)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => X.X t ω i - cutJumpIntegral S hA hℱ0 hnull0 i t ω
variable (S : SdeData X) {A : Set E} (hA : MeasurableSet A)
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)

/-- The truncated compensated integral agrees almost surely, at each time, with the `L²`
Itô–Lévy integral of the mark cut. -/
theorem cutJumpIntegral_ae_eq (i : Fin n) (t : ℝ) :
    cutJumpIntegral S hA hℱ0 hnull0 i t
      =ᵐ[P] stochasticIntegral N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
        (measurable_markCut (S.γ_meas i) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA)
        (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') t :=
  cadlagIntegral_ae_eq N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') hℱ0 hnull0 t
/-- The truncated compensated integral is adapted to the right-continuous filtration. -/
theorem adapted_cutJumpIntegral (i : Fin n) :
    Adapted S.ℱ.rightCont (cutJumpIntegral S hA hℱ0 hnull0 i) :=
  cadlagIntegral_adapted N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') hℱ0 hnull0
/-- The truncated compensated integral is measurable at each time. -/
theorem measurable_cutJumpIntegral (i : Fin n) (t : ℝ) :
    Measurable (cutJumpIntegral S hA hℱ0 hnull0 i t) :=
  (adapted_cutJumpIntegral S hA hℱ0 hnull0 i t).mono (S.ℱ.rightCont.le t) le_rfl
/-- Every path of the truncated compensated integral is right-continuous. -/
theorem rightContinuous_cutJumpIntegral (i : Fin n) (ω : Ω) (t : ℝ) :
    Tendsto (fun s => cutJumpIntegral S hA hℱ0 hnull0 i s ω) (𝓝[>] t)
      (𝓝 (cutJumpIntegral S hA hℱ0 hnull0 i t ω)) :=
  cadlagIntegral_rightContinuous N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') hℱ0 hnull0 ω t
/-- Every path of the truncated compensated integral has a left limit at every time. -/
theorem exists_leftLim_cutJumpIntegral (i : Fin n) (ω : Ω) (t : ℝ) :
    ∃ L : ℝ, Tendsto (fun s => cutJumpIntegral S hA hℱ0 hnull0 i s ω) (𝓝[<] t) (𝓝 L) :=
  cadlagIntegral_exists_leftLim N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') hℱ0 hnull0 ω t
/-- The truncated compensated integral is jointly measurable in the sample point and the
time. -/
theorem measurable_uncurry_cutJumpIntegral (i : Fin n) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      cutJumpIntegral S hA hℱ0 hnull0 i s ω) :=
  measurable_uncurry_cadlagIntegral N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') hℱ0 hnull0
/-- The truncated compensated integral is a martingale for the right-continuous filtration. -/
theorem martingale_cutJumpIntegral (i : Fin n) :
    MeasureTheory.Martingale (cutJumpIntegral S hA hℱ0 hnull0 i) S.ℱ.rightCont P :=
  LevyStochCalc.Martingale.martingale_of_ae_eq
    (martingale_stochasticIntegral_rightCont N S.ℱ S.isPoisson
      (markCut A (pathJumpCoeff coeffs X.X i)) (measurable_markCut (S.γ_meas i) hA)
      ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA) (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT'))
    (fun t => (adapted_cutJumpIntegral S hA hℱ0 hnull0 i t).stronglyMeasurable)
    (cutJumpIntegral_ae_eq S hA hℱ0 hnull0 i)
/-- At nonpositive times the truncated compensated integral vanishes almost surely. -/
theorem cutJumpIntegral_ae_zero (i : Fin n) {t : ℝ} (ht : t ≤ 0) :
    cutJumpIntegral S hA hℱ0 hnull0 i t =ᵐ[P] 0 :=
  (cutJumpIntegral_ae_eq S hA hℱ0 hnull0 i t).trans
    ((stochasticIntegral_ae_eq_process N S.ℱ S.isPoisson
        (markCut A (pathJumpCoeff coeffs X.X i)) (measurable_markCut (S.γ_meas i) hA)
        ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA)
        (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') t).trans
      (_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N S.ℱ S.isPoisson _ _ _ _ ht))
/-- A coordinate of the big-jump path is jointly measurable in the time and the sample point. -/
theorem measurable_uncurry_bigJumpPath_coord (i : Fin n) :
    Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) =>
      bigJumpPath S hA hℱ0 hnull0 t ω i) := by
  have hX : Measurable fun q : ℝ × Ω => X.X q.1 q.2 i :=
    (measurable_pi_apply i).comp X.measurable_path
  have hC : Measurable fun q : ℝ × Ω => cutJumpIntegral S hA hℱ0 hnull0 i q.1 q.2 :=
    (measurable_uncurry_cutJumpIntegral S hA hℱ0 hnull0 i).comp measurable_swap
  exact hX.sub hC
/-- The big-jump path is jointly measurable in the time and the sample point. -/
theorem measurable_uncurry_bigJumpPath :
    Measurable (Function.uncurry (bigJumpPath S hA hℱ0 hnull0)) :=
  measurable_pi_lambda _ fun i => measurable_uncurry_bigJumpPath_coord S hA hℱ0 hnull0 i
/-- The big-jump path starts at the initial value of the jump diffusion. -/
theorem bigJumpPath_ae_initial : ∀ᵐ ω ∂P, bigJumpPath S hA hℱ0 hnull0 0 ω = x₀ := by
  filter_upwards [X.initial_value, MeasureTheory.ae_all_iff.mpr
    fun i : Fin n => cutJumpIntegral_ae_zero S hA hℱ0 hnull0 i (le_refl (0 : ℝ))] with ω h0 hc
  funext i
  change X.X 0 ω i - cutJumpIntegral S hA hℱ0 hnull0 i 0 ω = x₀ i
  rw [hc i, h0]
  simp
/-- The big-jump path is almost surely càdlàg on the SDE time domain. -/
theorem bigJumpPath_ae_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    Tendsto (fun s => bigJumpPath S hA hℱ0 hnull0 s ω) (𝓝[>] t)
        (𝓝 (bigJumpPath S hA hℱ0 hnull0 t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ,
          Tendsto (fun s => bigJumpPath S hA hℱ0 hnull0 s ω i) (𝓝[<] t) (𝓝 L) := by
  filter_upwards [X.cadlag_paths] with ω hω t ht
  refine ⟨tendsto_pi_nhds.mpr fun i => ?_, fun i => ?_⟩
  · exact (((continuous_apply i).tendsto _).comp (hω t ht).1).sub
      (rightContinuous_cutJumpIntegral S hA hℱ0 hnull0 i ω t)
  · obtain ⟨L, hL⟩ := (hω t ht).2 i
    obtain ⟨M, hM⟩ := exists_leftLim_cutJumpIntegral S hA hℱ0 hnull0 i ω t
    exact ⟨L - M, hL.sub hM⟩
omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A coordinate of the jump coefficient restricted to a set of marks, along a path, is the
restriction of that coordinate along the path. -/
theorem pathJumpCoeff_markCutγ (A' : Set E) (Xp : ℝ → Ω → (Fin n → ℝ)) (i : Fin n) :
    pathJumpCoeff (coeffs.markCutγ A') Xp i = markCut A' (pathJumpCoeff coeffs Xp i) := by
  funext ω s e
  simpa [pathJumpCoeff, markCut] using
    JumpDiffusionCoeffs.markCutγ_γ_apply coeffs A' s (Xp s ω) e i
include S hA in
/-- The jump coefficient outside the cut, along the path, is jointly measurable. -/
theorem measurable_pathJumpCoeff_markCutγ_compl (i : Fin n) :
    Measurable fun p : Ω × ℝ × E =>
      pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i p.1 p.2.1 p.2.2 := by
  rw [pathJumpCoeff_markCutγ]; exact measurable_markCut (S.γ_meas i) hA.compl
include S hA in
/-- The jump coefficient outside the cut, along the path, is marked progressively
measurable. -/
theorem markedProg_pathJumpCoeff_markCutγ_compl (i : Fin n) :
    Probability.MarkedProgressivelyMeasurable S.ℱ
      (pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i) := by
  rw [pathJumpCoeff_markCutγ]; exact (_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (S.γ_prog i)) hA.compl
include S in
/-- The jump coefficient outside the cut, along the path, has finite energy on every bounded
window. -/
theorem sq_pathJumpCoeff_markCutγ_compl (i : Fin n) : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  rw [pathJumpCoeff_markCutγ]; exact fun T' hT' => sq_markCut (S.γ_sq i) Aᶜ T' hT'
end Path

section Diffusion

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

end Diffusion

end LevyStochCalc.Ito.BigJump


