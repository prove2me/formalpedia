-- Prove2me | Definitions.Def_LevyStochCalc_Probability_ProjectionLimit_F000
-- name    : LevyStochCalc_Probability_ProjectionLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:07:54.630234+00:00
-- url     : https://prove2.me/theorems/9e5866ff-1e76-4c16-9b52-d0fea1d6f855
-- title:
--   Source declarations: LevyStochCalc.Probability.ProjectionLimit
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Probability.ProjectionLimit, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.MonotoneConvergence

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

omit [CompleteSpace E] in
/-- On nested subspaces the orthogonal projections compose: `P_W ∘ P_V = P_W` for `W ≤ V`. -/
theorem starProjection_starProjection_of_le {V W : Submodule ℝ E} [V.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (h : W ≤ V) (x : E) :
    W.starProjection (V.starProjection x) = W.starProjection x := by
  have hx : x - V.starProjection x ∈ Wᗮ :=
    Submodule.orthogonal_le h (V.sub_starProjection_mem_orthogonal x)
  have h0 : W.starProjection (x - V.starProjection x) = 0 :=
    Submodule.eq_starProjection_of_mem_orthogonal W.zero_mem (by simpa using hx)
  rw [map_sub] at h0
  exact (sub_eq_zero.1 h0).symm
omit [CompleteSpace E] in
/-- **Pythagoras for nested projections.** -/
theorem norm_sq_starProjection_of_le {V W : Submodule ℝ E} [V.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (h : W ≤ V) (x : E) :
    ‖V.starProjection x‖ ^ 2
      = ‖W.starProjection x‖ ^ 2 + ‖V.starProjection x - W.starProjection x‖ ^ 2 := by
  have key := W.norm_sq_eq_add_norm_sq_starProjection (V.starProjection x)
  rw [starProjection_starProjection_of_le h x] at key
  have horth : Wᗮ.starProjection (V.starProjection x)
      = V.starProjection x - W.starProjection x := by
    rw [Submodule.starProjection_orthogonal W]
    simp [starProjection_starProjection_of_le h x]
  rwa [horth] at key
omit [CompleteSpace E] in
/-- Equal subspaces have equal orthogonal projections. -/
theorem starProjection_congr {V W : Submodule ℝ E} [V.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (h : V = W) (x : E) :
    V.starProjection x = W.starProjection x := by
  subst h; rfl
omit [CompleteSpace E] in
/-- For nested subspaces `U ≤ V ≤ W` the projection onto the larger of the two outer subspaces is
the further one from `P_U x`. -/
theorem norm_starProjection_sub_le_of_le {U V W : Submodule ℝ E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] (hUV : U ≤ V) (hVW : V ≤ W) (x : E) :
    ‖V.starProjection x - U.starProjection x‖ ≤ ‖W.starProjection x - U.starProjection x‖ := by
  have h₁ := norm_sq_starProjection_of_le hUV x
  have h₂ := norm_sq_starProjection_of_le (hUV.trans hVW) x
  have h₃ := norm_sq_starProjection_of_le hVW x
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  nlinarith [sq_nonneg ‖W.starProjection x - V.starProjection x‖]
section Antitone

variable {V : ℕ → Submodule ℝ E} [∀ n, (V n).HasOrthogonalProjection]

omit [CompleteSpace E] in
/-- Along an antitone sequence the squared norms of the projections are antitone. -/
theorem antitone_norm_sq_starProjection (hV : Antitone V) (x : E) :
    Antitone fun n => ‖(V n).starProjection x‖ ^ 2 := by
  intro a b hab
  have := norm_sq_starProjection_of_le (hV hab) x
  nlinarith [sq_nonneg ‖(V a).starProjection x - (V b).starProjection x‖]
end Antitone

end LevyStochCalc.Probability


