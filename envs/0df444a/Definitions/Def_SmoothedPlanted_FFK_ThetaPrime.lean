-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_ThetaPrime
-- name    : SmoothedPlanted_FFK_ThetaPrime
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:31:51.871733+00:00
-- url     : https://prove2.me/theorems/0c5bccf7-3f48-49c7-a99f-9b365deaa547
-- title:
--   Robust Theta SDP and its optimal value
-- statement:
--   For a finite graph $G$, a Gram matrix $M$ has one distinguished index for the unit vector $u$, and one index per vertex. Feasibility means $M\succeq0$, $M_{00}=1$, $M_{0v}=M_{vv}$, $M_{vw}\ge0$, $\sum_{v\ne w}M_{vw}\le k(k-1)$, and $\frac12\sum_{v,w:\,v\sim w}M_{vw}\le\Delta$. The objective is $\sum_v M_{vv}$ and $\Theta'(G,k,\Delta)$ is its supremum. For $\Delta\ge0$ the zero vertex block is feasible and every diagonal entry lies in $[0,1]$, so the supremum is finite and attained. At negative budgets feasibility is empty and the real supremum takes its default value; no mission theorem uses that case.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Robust Theta SDP and its optimal value, printed p. 27 (PDF p. 29), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Mathlib

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

abbrev Gram (V : Type) := Matrix (Option V) (Option V) ℝ
def mass {V : Type} [Fintype V] (M : Gram V) : ℝ := ∑ v, M (some v) (some v)
def thetaFeasible {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (Δ : ℝ) (M : Gram V) : Prop := by
  classical
  exact M.PosSemidef ∧ M none none = 1 ∧
  (∀ v, M none (some v) = M (some v) (some v)) ∧
  (∀ v w, 0 ≤ M (some v) (some w)) ∧
  (∑ v, ∑ w, if v ≠ w then M (some v) (some w) else 0) ≤ (k : ℝ) * ((k : ℝ) - 1) ∧
  (∑ v, ∑ w, if G.Adj v w then M (some v) (some w) else 0) / 2 ≤ Δ
  -- The division by two counts each unordered edge exactly once.
def thetaPrime {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (Δ : ℝ) : ℝ :=
  sSup {z | ∃ M : Gram V, thetaFeasible G k Δ M ∧ z = mass M}

end SmoothedPlanted.FFK


