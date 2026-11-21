-- Prove2me | Definitions.Def_SourceProof_05b52d6373160625930b090a
-- name    : SourceProof_05b52d6373160625930b090a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:47:54.161179+00:00
-- url     : https://prove2.me/theorems/3fa30a96-97d2-472c-8753-08f20d3e491a
-- title:
--   LevyStochCalc source module: SourceProof_05b52d6373160625930b090a
-- statement:
--   The original source theorem `LevyStochCalc.exists_bound_fderiv_fderiv_cutoffFun` comes from the `LevyStochCalc.Brownian.ItoCutoff` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F000
import Definitions.Def_SourceProof_487d91410cc5e15ee891c2c1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a twice continuously differentiable function

Multiplying `f` by a smooth box cutoff leaves it, together with its first two derivatives,
unchanged on a cube and makes them bounded and uniformly continuous. Along a path stopped before
it leaves that cube the two functions therefore give the same integrands, and the local property
of the Itô integral transfers the stochastic terms.

## Main statements

* `LevyStochCalc.cutoffFun` — the cut-off function.
* `LevyStochCalc.fderiv_cutoffFun` — its first two derivatives agree with `f`'s on the cube.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_of_contDiff` — Itô's formula for a
  twice continuously differentiable function, with no bound on its derivatives.
-/

namespace LevyStochCalc

open scoped Topology

section Cutoff

variable {n : ℕ}

theorem _root_.Prove2MeSourceProof.h_05b52d6373160625930b090a {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {k : ℝ}
    (hk : 0 < k) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ (cutoffFun f k)) z‖ ≤ K₂ := by
  obtain ⟨M, hM⟩ := (LevyStochCalc.hasCompactSupport_hessVec f hk).exists_bound_of_continuous
    (LevyStochCalc.continuous_hessVec hf k)
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine ⟨(n : ℝ) * ((n : ℝ) * M), by positivity, fun z => ?_⟩
  refine (_root_.Prove2MeSourceProof.h_487d91410cc5e15ee891c2c1 (fderiv ℝ (fderiv ℝ (LevyStochCalc.cutoffFun f k)) z)).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      (∑ q, |fderiv ℝ (fderiv ℝ (LevyStochCalc.cutoffFun f k)) z (Pi.single p 1) (Pi.single q 1)|)
        ≤ (n : ℝ) * M := by
    intro p _
    have hq : ∀ q ∈ (Finset.univ : Finset (Fin n)),
        |fderiv ℝ (fderiv ℝ (LevyStochCalc.cutoffFun f k)) z (Pi.single p 1) (Pi.single q 1)| ≤ M := by
      intro q _
      have h1 := norm_le_pi_norm (LevyStochCalc.hessVec (LevyStochCalc.cutoffFun f k) z) (p, q)
      have h2 := hM z
      simp only [LevyStochCalc.hessVec, Real.norm_eq_abs] at h1
      linarith
    refine (Finset.sum_le_sum hq).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
end Cutoff

namespace Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Bounded

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Bounded

section Formula

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

end Formula

end Brownian.Ito

end LevyStochCalc


