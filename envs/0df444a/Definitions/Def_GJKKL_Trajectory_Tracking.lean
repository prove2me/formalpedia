-- Prove2me | Definitions.Def_GJKKL_Trajectory_Tracking
-- name    : GJKKL_Trajectory_Tracking
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:38:48.168814+00:00
-- url     : https://prove2.me/theorems/eb3c489d-9749-4a0f-9c1b-7b62f0c15e2e
-- title:
--   Tracking
-- statement:
--   Definitions and structural lemmas for Tracking, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Tracking.lean

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (V) in
/-- `aP(t) = (n - kt)/k`, the number of uncovered vertices divided by `k`. -/
noncomputable def aPar (k t : ℕ) : ℝ := ((Fintype.card V : ℝ) - k * t) / k
def GoodState (H : Finset (Finset V)) (dh δ : ℕ → ℝ) (h : List (Finset V)) : Prop :=
  IsGreedySeq H h ∧ Tracked H dh δ h ∧ (avail H h).Nonempty
noncomputable def upperProc (H : Finset (Finset V)) (dh δ : ℕ → ℝ) (v : V) :
    List (Finset V) → ℝ :=
  frozen H (fun t x => 1 * x + (-dh t - δ t)) v
noncomputable def lowerProc (H : Finset (Finset V)) (dh δ : ℕ → ℝ) (v : V) :
    List (Finset V) → ℝ :=
  frozen H (fun t x => (-1) * x + (dh t - δ t)) v
structure TrackHyp (H : Finset (Finset V)) (k c : ℕ) (dh δ : ℕ → ℝ) (T : ℕ)
    (B lam C s : ℝ) : Prop where
  unif : IsUniform H k
  two_le : 2 ≤ k
  codeg : ∀ u w, u ≠ w → codegree H u w ≤ c
  dh_pos : ∀ t < T, 0 < dh t
  δ_nonneg : ∀ t < T, 0 ≤ δ t
  δ_le : ∀ t < T, δ t ≤ dh t / 2
  aP_ge : ∀ t < T, 16 ≤ aPar V k t
  aP_ge_k : ∀ t < T, (k : ℝ) - 2 ≤ aPar V k t
  g_nonneg : ∀ t < T, 0 ≤ dh t - dh (t + 1)
  g_le : ∀ t < T, dh t - dh (t + 1) ≤ ((k : ℝ) - 1) * dh t / aPar V k t
  g_ge : ∀ t < T, ((k : ℝ) - 1) * dh t / aPar V k t -
      ((k : ℝ) - 1) * ((k : ℝ) - 2) * dh t / aPar V k t ^ 2 ≤ dh t - dh (t + 1)
  r_ge : ∀ t < T, B * δ t / aPar V k t ≤ δ (t + 1) - δ t
  B_ge : 32 * ((k : ℝ) - 1) ≤ B
  B_c : ∀ t < T, 8 * ((((k - 1) + (k - 1) * (k - 2) : ℕ) : ℝ)) * c ≤ B * δ t
  B_n : ∀ t < T, 4 * ((k : ℝ) - 1) * (2 + ((k : ℝ) - 2)) * dh t ≤ B * δ t * aPar V k t
  lam_pos : 0 < lam
  init : ∀ v, |(degree H v : ℝ) - dh 0| ≤ δ 0 - lam
  C_pos : 0 < C
  C_ge : ∀ t < T, (k : ℝ) * c + ((dh t - dh (t + 1)) + (δ (t + 1) - δ t)) ≤ C
  s_pos : 0 < s
  s_ge : ∀ t < T, ∑ t' ∈ range (t + 1),
      (((k : ℝ) - 1) * (dh t' + δ t') ^ 2 / (aPar V k t' * (dh t' - δ t')) +
        ((dh t' - dh (t' + 1)) + (δ (t' + 1) - δ t'))) ≤ s
variable (V) in
/-- The per-step bound for the conditional absolute increments. -/
noncomputable def bnd (k : ℕ) (dh δ : ℕ → ℝ) (t : ℕ) : ℝ :=
  ((k : ℝ) - 1) * (dh t + δ t) ^ 2 / (aPar V k t * (dh t - δ t)) +
    ((dh t - dh (t + 1)) + (δ (t + 1) - δ t))
namespace TrackHyp
variable {H : Finset (Finset V)} {k c : ℕ} {dh δ : ℕ → ℝ} {T : ℕ} {B lam C s : ℝ}
  (hyp : TrackHyp H k c dh δ T B lam C s)
include hyp
end TrackHyp
end GJKKL


