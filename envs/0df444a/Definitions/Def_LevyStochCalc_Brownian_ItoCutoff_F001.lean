-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001
-- name    : LevyStochCalc_Brownian_ItoCutoff_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:49:46.437452+00:00
-- url     : https://prove2.me/theorems/e678c9ff-f567-4cc5-a877-0c80f9adf138
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoCutoff
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoCutoff. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

theorem exists_delta_fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {k : ℝ}
    (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z w : Fin n → ℝ, ‖z - w‖ < δ →
      ‖fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w‖ ≤ ε := by
  have hpos : (0 : ℝ) < ε / ((n : ℝ) * (n : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := exists_delta_of_hasCompactSupport (continuous_hessVec hf k)
    (hasCompactSupport_hessVec f hk) hpos
  refine ⟨δ, hδ0, fun z w hzw => ?_⟩
  set c : ℝ := ε / ((n : ℝ) * (n : ℝ) + 1) with hc
  have hcnn : (0 : ℝ) ≤ c := hpos.le
  have hcoord : ∀ p q : Fin n,
      |fderiv ℝ (fderiv ℝ (cutoffFun f k)) z (Pi.single p 1) (Pi.single q 1)
        - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w (Pi.single p 1) (Pi.single q 1)| ≤ c := by
    intro p q
    have h1 := norm_le_pi_norm
      (hessVec (cutoffFun f k) z - hessVec (cutoffFun f k) w) (p, q)
    have h2 := hδ z w hzw
    simp only [Pi.sub_apply, hessVec, Real.norm_eq_abs] at h1
    linarith
  have hsub : fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w
      = (fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w) := rfl
  refine (_root_.Prove2MeSourceProof.h_487d91410cc5e15ee891c2c1
    (fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w)).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      (∑ q, |(fderiv ℝ (fderiv ℝ (cutoffFun f k)) z
          - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w) (Pi.single p 1) (Pi.single q 1)|)
        ≤ (n : ℝ) * c := by
    intro p _
    have hq : ∀ q ∈ (Finset.univ : Finset (Fin n)),
        |(fderiv ℝ (fderiv ℝ (cutoffFun f k)) z
          - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w) (Pi.single p 1) (Pi.single q 1)| ≤ c := by
      intro q _
      simpa using hcoord p q
    refine (Finset.sum_le_sum hq).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
  have hd : (0 : ℝ) < (n : ℝ) * (n : ℝ) + 1 := by positivity
  have hrw : (n : ℝ) * ((n : ℝ) * (ε / ((n : ℝ) * (n : ℝ) + 1)))
      = (n : ℝ) * (n : ℝ) * ε / ((n : ℝ) * (n : ℝ) + 1) := by ring
  rw [hrw, div_le_iff₀ hd]
  nlinarith [hε.le]
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


