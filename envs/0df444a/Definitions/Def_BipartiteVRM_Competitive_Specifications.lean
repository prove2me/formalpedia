-- Prove2me | Definitions.Def_BipartiteVRM_Competitive_Specifications
-- name    : BipartiteVRM_Competitive_Specifications
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:59.267678+00:00
-- url     : https://prove2.me/theorems/9ec24783-4f8b-40f0-b90c-7315e8eb580c
-- title:
--   Explicit completion, feasibility, offline attainment, and competitive coefficient
-- statement:
--   These are conclusion predicates for the operational development. Offline attainment means that the actual timed objective has a finite minimum attained by a feasible perfect matching. Execution correctness means that the explicit run halts, its final output is feasible and perfect, every reachable auxiliary/output pair has the same saturated vertices, cached paths are minimum augmenting paths, output decisions are irrevocable, clocks are nondecreasing, and the transition recurrence has a unique history. The coefficient is
--
--   $$c_\gamma(m)=\left(2+\frac{2\gamma}{\gamma-1}\right)\bigl[1+(\gamma+1)(1+\ln m)\bigr].$$
--
--   These predicates collect conclusions without adding assumptions to the input, states, or tie rules. In particular, no performance bound or execution invariant is a field of the operational records.
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), pp. 2–3, Theorem 1.1; pp. 6–9, §2.1–§3.4

import Definitions.Def_BipartiteVRM_Competitive_Charging

set_option autoImplicit false

namespace BipartiteVRM.Competitive

open Classical

/-! Conclusion predicates, never assumptions on the data or on the execution.
Kuo, §2.1–§3.4, pp. 6–9, §4.2, pp. 10–11. -/

def OfflineAttained {X : Type*} [MetricSpace X] (I : Input X) : Prop :=
  offlineInf I ≠ ⊤ ∧ 0 ≤ OPT I ∧
    ∃ M τ, IsPerfect I M ∧ FeasibleTimes I M τ ∧ totalCost I M τ = OPT I ∧
      ∀ N σ, IsPerfect I N → FeasibleTimes I N σ → OPT I ≤ totalCost I N σ

def StateValid {X : Type*} (I : Input X) (b : View) : Prop :=
  b.inserted ⊆ b.visible ∧ b.visible ⊆ I.items ∧
    IsMatching I.requests I.servers b.off ∧
    (∀ e ∈ b.off, Sum.inl e.1 ∈ b.inserted ∧ Sum.inr e.2 ∈ b.inserted) ∧
    IsMatching I.requests I.servers (eventEdges b.output) ∧
    (b.output.map MatchEvent.request).Nodup ∧ (b.output.map MatchEvent.server).Nodup ∧
    (∀ v, saturated b.off v ↔ saturated (eventEdges b.output) v) ∧
    (∀ e ∈ b.output, max (I.arrival (.inl e.request))
      (I.arrival (.inr e.server)) ≤ e.time)

def CacheValid (γ : ℝ) (b : View) : Prop :=
  ∀ r ∈ b.freeRequests,
    (b.cache r = none ↔ augmentingPaths b.inserted b.off r = ∅) ∧
    ∀ P, b.cache r = some P → P ∈ minimumPaths b.inserted b.edgeTA γ b.off r

def FollowsRun {X : Type*} [MetricSpace X] (I : Input X) (γ : ℝ) (tie : TieRule)
    (H : ℕ → List View) : Prop :=
  H 0 = [initialView] ∧ ∀ n,
    let h := H n
    let b := h.getLastD initialView
    H (n + 1) = if halted I γ b then h else h ++ [step I γ tie h b]

/-- Existence of halting, correctness of the final output, reachable-state invariants,
and uniqueness of the prescribed transition sequence are all *conclusions*. -/
def ExecutionCorrect {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) : Prop :=
  (∃ n, halted I γ (state I γ tie n)) ∧
    FeasibleOutput I (output I γ tie) ∧
    (∀ n, StateValid I (state I γ tie n) ∧ CacheValid γ (state I γ tie n)) ∧
    (∀ n, (state I γ tie n).output.IsPrefix (state I γ tie (n + 1)).output) ∧
    (∀ n, (state I γ tie n).clock ≤ (state I γ tie (n + 1)).clock) ∧
    (∀ H, FollowsRun I γ tie H → H = history I γ tie)

noncomputable def competitiveFactor (γ : ℝ) (m : ℕ) : ℝ :=
  (2 + 2 * γ / (γ - 1)) * (1 + (γ + 1) * (1 + Real.log (m : ℝ)))

end BipartiteVRM.Competitive


