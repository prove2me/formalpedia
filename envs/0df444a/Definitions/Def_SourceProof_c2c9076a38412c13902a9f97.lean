-- Prove2me | Definitions.Def_SourceProof_c2c9076a38412c13902a9f97
-- name    : SourceProof_c2c9076a38412c13902a9f97
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:21:37.682617+00:00
-- url     : https://prove2.me/theorems/8c7345d0-92b3-4dc9-a3a5-ec37dfbaccae
-- title:
--   LevyStochCalc source module: SourceProof_c2c9076a38412c13902a9f97
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.integral_simpleIntegral_mul_markStep_eq_zero` comes from the `LevyStochCalc.Driver.CrossSimple` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CrossSimple_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Elementary integrals against the two drivers are orthogonal

An elementary Brownian integral and the compensated integral of a mark-step integrand expand
into finite sums of cross terms, one for each pair of cells. Clamping a cell to a running time
either collapses it, killing the term, or leaves its left endpoint alone, where the coefficient
is measurable; so every term has zero mean and the pairing vanishes at any pair of times.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open Brownian.Multidim.MultidimBrownianMotion (min_eq_or_lt_min)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_c2c9076a38412c13902a9f97 (𝒲 : CrossWitness D ℱ) {i : Fin d}
    {TH : ℝ} (H : Brownian.Ito.SimplePredictable Ω TH)
    (hH : ∀ a : Fin H.N, StronglyMeasurable[ℱ (H.partition a.castSucc)] (H.ξ a))
    {g : Poisson.Compensated.TimeGrid} (G : Poisson.Compensated.MarkStep Ω E ν g)
    (hG : G.Adapted ℱ) (t t' : ℝ) :
    ∫ ω, Brownian.Ito.simpleIntegral (D.W.W i) H t ω * G.integral D.N t' ω ∂P = 0 := by
  have hHnn : ∀ a : Fin H.N, 0 ≤ H.partition a.castSucc := fun a => by
    have h := H.partition_strictMono.monotone (Fin.zero_le a.castSucc)
    rwa [H.partition_zero] at h
  have hHlt : ∀ a : Fin H.N, H.partition a.castSucc < H.partition a.succ := fun a =>
    H.partition_strictMono Fin.castSucc_lt_succ
  have key : ∀ (a : Fin H.N) (j : ℕ), j < g.N₀ → ∀ k : Fin G.K,
      Integrable (fun ω => (H.ξ a ω * ((D.W.W i).W (min (H.partition a.succ) t) ω
            - (D.W.W i).W (min (H.partition a.castSucc) t) ω))
          * (G.ξ j k ω * D.N.compensated
            (Set.Ioc (min (g.p j) t') (min (g.p (j + 1)) t') ×ˢ G.B k) ω)) P
        ∧ ∫ ω, (H.ξ a ω * ((D.W.W i).W (min (H.partition a.succ) t) ω
            - (D.W.W i).W (min (H.partition a.castSucc) t) ω))
          * (G.ξ j k ω * D.N.compensated
            (Set.Ioc (min (g.p j) t') (min (g.p (j + 1)) t') ×ˢ G.B k) ω) ∂P = 0 := by
    intro a j hj k
    obtain ⟨Mξ, hMξ⟩ := H.ξ_bounded a
    obtain ⟨Mη, hMη⟩ := G.ξ_bounded j k
    exact LevyStochCalc.Driver.LevyDriver.integrable_and_integral_cross_clamped 𝒲 (hHnn a) (hHlt a) (g.p_nonneg hj.le)
      (g.p_lt j hj) (G.B_measurable k) (G.B_finite k) (hH a) (H.ξ_measurable a) hMξ
      (hG j hj k) (G.ξ_measurable j k) hMη t t'
  have hexp : (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral (D.W.W i) H t ω * G.integral D.N t' ω)
      = fun ω => ∑ a : Fin H.N, ∑ j ∈ Finset.range g.N₀, ∑ k,
        (H.ξ a ω * ((D.W.W i).W (min (H.partition a.succ) t) ω
            - (D.W.W i).W (min (H.partition a.castSucc) t) ω))
          * (G.ξ j k ω * D.N.compensated
            (Set.Ioc (min (g.p j) t') (min (g.p (j + 1)) t') ×ˢ G.B k) ω) := by
    funext ω
    rw [LevyStochCalc.Brownian.Ito.simpleIntegral, LevyStochCalc.Poisson.Compensated.MarkStep.integral,
      Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
      Finset.mul_sum _ _ _
  rw [hexp, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun j hj =>
    integrable_finsetSum _ fun k _ => (key a j (Finset.mem_range.mp hj) k).1]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun j hj => integrable_finsetSum _ fun k _ =>
    (key a j (Finset.mem_range.mp hj) k).1]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [integral_finsetSum _ fun k _ => (key a j (Finset.mem_range.mp hj) k).1]
  exact Finset.sum_eq_zero fun k _ => (key a j (Finset.mem_range.mp hj) k).2
end LevyDriver

end LevyStochCalc.Driver


