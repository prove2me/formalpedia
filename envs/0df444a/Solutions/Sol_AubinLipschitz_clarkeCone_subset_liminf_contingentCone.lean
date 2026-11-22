-- Prove2me | solution 1 for AubinLipschitz.clarkeCone_subset_liminf_contingentCone
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:18:25.834571+00:00
-- url     : https://prove2.me/submissions/3f110fd5-acbb-488c-b3c4-583df86c69cc

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeCone
import Definitions.Def_AubinLipschitz_contingentCone

set_option autoImplicit false

open AubinLipschitz Metric Filter Topology

set_option linter.unusedVariables false in
theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E) (x₀ : E) (hx₀ : x₀ ∈ K) (v : E) (hv : v ∈ clarkeCone K x₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ x ∈ K, ‖x - x₀‖ ≤ η → ∃ w ∈ contingentCone K x, ‖v - w‖ ≤ ε := by
  obtain ⟨α, hα, β, hβ, H⟩ := hv ε hε
  refine ⟨α, hα, fun x hxK hxn => ?_⟩
  have hx : x ∈ K ∩ closedBall x₀ α := ⟨hxK, by rw [mem_closedBall, dist_eq_norm]; exact hxn⟩
  -- Clarke directions along the steps `β/(n+1) → 0`.
  have hstep : ∀ n : ℕ, 0 < β / ((n : ℝ) + 1) ∧ β / ((n : ℝ) + 1) ≤ β := fun n =>
    ⟨by positivity, div_le_self hβ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])⟩
  choose u hu hxu using fun n : ℕ => H x hx (β / ((n : ℝ) + 1)) (hstep n).1 (hstep n).2
  -- A convergent subsequence in the compact ball `B(v, ε)`.
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_closedBall v ε).tendsto_subseq hu
  refine ⟨w, ?_, ?_⟩
  · intro ε' hε' α' hα'
    have h1 : ∀ᶠ k in atTop, dist (u (φ k)) w < ε' := (Metric.tendsto_nhds.mp hlim) ε' hε'
    obtain ⟨N, hN⟩ := exists_nat_gt (β / α')
    have h2 : ∀ᶠ k in atTop, β / ((φ k : ℝ) + 1) ≤ α' := by
      filter_upwards [eventually_ge_atTop N] with k hk
      have hφk : (N : ℝ) ≤ φ k := by exact_mod_cast hk.trans (hφ.id_le k)
      rw [div_le_iff₀ (by positivity)]
      have : β < α' * N := by rwa [div_lt_iff₀ hα', mul_comm] at hN
      nlinarith
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    exact ⟨u (φ k), by rw [mem_closedBall]; exact hk1.le, β / ((φ k : ℝ) + 1), (hstep (φ k)).1,
      hk2, hxu (φ k)⟩
  · rw [mem_closedBall, dist_eq_norm] at hw
    rwa [norm_sub_rev]
