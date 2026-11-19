-- Prove2me | Definitions.Def_SourceProof_379d0a4d323e31b94e61b375
-- name    : SourceProof_379d0a4d323e31b94e61b375
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:09:21.321067+00:00
-- url     : https://prove2.me/theorems/6ea94f0e-e6bb-4372-8918-9dca95f9d14b
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.tendsto_starProjection_of_antitone
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ProjectionLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonal projections along a decreasing sequence of subspaces

For nested closed subspaces `W ≤ V` the projections compose, `P_W ∘ P_V = P_W`, and Pythagoras
splits the larger projection, `‖P_V x‖² = ‖P_W x‖² + ‖P_V x − P_W x‖²`. Along an antitone sequence
`V 0 ≥ V 1 ≥ ⋯` that makes `n ↦ ‖P_{V n} x‖²` antitone and bounded below, hence convergent, and the
same identity turns its Cauchy property into the Cauchy property of `(P_{V n} x)` itself. The limit
lies in every `V N` and is orthogonal to `⨅ n, V n`, so it *is* the projection onto the
intersection.

This is the Hilbert-space half of the downward `L²` convergence of conditional expectations that
cited result #13b needs; the measure-theoretic half is
`LevyStochCalc/Probability/AEMeasurableInf.lean`, which identifies the intersection of the
`lpMeas` subspaces.

## Main statements

* `starProjection_starProjection_of_le` — the projections compose on nested subspaces.
* `norm_sq_starProjection_of_le` — Pythagoras for nested projections.
* `norm_starProjection_sub_le_of_le` — `‖P_V x − P_U x‖ ≤ ‖P_W x − P_U x‖` for `U ≤ V ≤ W`.
* `tendsto_starProjection_of_antitone` — `P_{V n} x → P_{⨅ V n} x`.
-/

open Filter Topology Submodule

namespace LevyStochCalc.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Antitone

variable {V : ℕ → Submodule ℝ E} [∀ n, (V n).HasOrthogonalProjection]


theorem _root_.Prove2MeSourceProof.h_379d0a4d323e31b94e61b375 (hV : Antitone V)
    (hclosed : ∀ n, IsClosed ((V n : Set E)))
    [(⨅ n, V n).HasOrthogonalProjection] (x : E) :
    Tendsto (fun n => (V n).starProjection x) atTop (𝓝 ((⨅ n, V n).starProjection x)) := by
  set a : ℕ → ℝ := fun n => ‖(V n).starProjection x‖ ^ 2 with ha
  have ha_anti : Antitone a := LevyStochCalc.Probability.antitone_norm_sq_starProjection hV x
  have ha_bdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; positivity⟩
  have ha_tendsto : Tendsto a atTop (𝓝 (⨅ n, a n)) := tendsto_atTop_ciInf ha_anti ha_bdd
  -- the projections form a Cauchy sequence
  have hcauchy : CauchySeq fun n => (V n).starProjection x := by
    refine cauchySeq_of_le_tendsto_0 (fun N => Real.sqrt (a N - ⨅ n, a n)) ?_ ?_
    · intro n m N hn hm
      have hsplit : ∀ p q : ℕ, p ≤ q →
          ‖(V p).starProjection x - (V q).starProjection x‖ ^ 2 = a p - a q := by
        intro p q hpq
        have := LevyStochCalc.Probability.norm_sq_starProjection_of_le (hV hpq) x
        simp only [ha]
        linarith
      have hle : ∀ p q : ℕ, N ≤ p → N ≤ q → p ≤ q →
          dist ((V p).starProjection x) ((V q).starProjection x)
            ≤ Real.sqrt (a N - ⨅ k, a k) := by
        intro p q hp hq hpq
        have h1 : ‖(V p).starProjection x - (V q).starProjection x‖ ^ 2 = a p - a q :=
          hsplit p q hpq
        have h2 : a p ≤ a N := ha_anti hp
        have h3 : (⨅ k, a k) ≤ a q := ciInf_le ha_bdd q
        have h4 : ‖(V p).starProjection x - (V q).starProjection x‖ ^ 2
            ≤ a N - ⨅ k, a k := by rw [h1]; linarith
        rw [dist_eq_norm]
        have h5 : 0 ≤ ‖(V p).starProjection x - (V q).starProjection x‖ := norm_nonneg _
        nlinarith [Real.sq_sqrt (le_trans (by positivity : (0:ℝ) ≤
            ‖(V p).starProjection x - (V q).starProjection x‖ ^ 2) h4),
          Real.sqrt_nonneg (a N - ⨅ k, a k)]
      rcases le_total n m with hnm | hmn
      · exact hle n m hn hm hnm
      · rw [dist_comm]; exact hle m n hm hn hmn
    · have h1 : Tendsto (fun N => a N - ⨅ n, a n) atTop (𝓝 0) := by
        simpa using ha_tendsto.sub (tendsto_const_nhds (x := ⨅ n, a n))
      have h2 : Tendsto (fun N => Real.sqrt (a N - ⨅ n, a n)) atTop (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp h1
      simpa using h2
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the limit lies in every `V N`, hence in the intersection
  have hyV : ∀ N, y ∈ V N := by
    intro N
    refine (hclosed N).mem_of_tendsto (hy.comp (tendsto_add_atTop_nat N)) ?_
    filter_upwards with n
    exact hV (Nat.le_add_left N n) ((V (n + N)).starProjection_apply_mem x)
  have hymem : y ∈ ⨅ n, V n := (Submodule.mem_iInf _).2 hyV
  -- and `x - y` is orthogonal to the intersection
  have horth : x - y ∈ (⨅ n, V n)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hstep : ∀ n, inner ℝ w (x - (V n).starProjection x) = 0 := by
      intro n
      have hwn : w ∈ V n := (Submodule.mem_iInf _).1 hw n
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal' _ _).1 ((V n).sub_starProjection_mem_orthogonal x) w hwn
    have hlim : Tendsto (fun n => inner ℝ w (x - (V n).starProjection x)) atTop
        (𝓝 (inner ℝ w (x - y))) :=
      Filter.Tendsto.inner tendsto_const_nhds (tendsto_const_nhds.sub hy)
    have hzero : inner ℝ w (x - y) = 0 := by
      refine tendsto_nhds_unique hlim ?_
      simp [hstep]
    simpa [real_inner_comm] using hzero
  have hproj : (⨅ n, V n).starProjection x = y :=
    Submodule.eq_starProjection_of_mem_orthogonal hymem horth
  rw [hproj]
  exact hy
end Antitone

end LevyStochCalc.Probability


