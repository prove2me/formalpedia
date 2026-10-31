-- Prove2me | Definitions.Def_LPAllocRM_IsScaledFamily
-- name    : LPAllocRM_IsScaledFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:06:23.882646+00:00
-- url     : https://prove2.me/theorems/3dee4032-c87e-460d-83b9-f874982c0887
-- title:
--   The scaled family of arrival processes $D^{(k)}$, §4
-- statement:
--   A family of problems indexed by $k=1,2,\dots$, each with its own probability space $(\Omega_k,P_k)$ and arrival process $D^{(k)}$, is a **scaled family** with horizon $\tau$ and mean vector $\mu$ if
--
--   1. every count $D^{(k)}_j(t)$ is a random variable;
--   2. almost surely, the path of $D^{(k)}$ is an arrival path on $(0,\tau]$: (a) finitely many arrivals, (b) at most one arrival at any time;
--   3. each $D^{(k)}_j(\tau)$ is integrable and $ED^{(k)}(\tau)=k\mu$.
--
--   This is the paper's §4 set-up: "For the $k$th problem, we replace our initial capacity vector by $kc$, and we assume the arrival process is given by the $n$-vector $D^{(k)}(\cdot)$. For each problem, we assume (as before) that, with probability one, there is (a) a finite number of arrivals and (b) at most one arrival at any point in time. We also will assume that $ED^{(k)}(\tau)=k\mu$."
--
--   **Formalization Note** Problems are indexed by positive integers. The clause at $k=1$ makes $\mu$ the expected demand of the original problem.
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, §4, p.723; §2, p.722; μ from §3, p.723

import Mathlib
import Definitions.Def_LPAllocRM_IsArrivalPath
open MeasureTheory

namespace LPAllocRM

/-- The scaled family of arrival processes of §4: for each `k = 1, 2, …`, the kth problem has its own
probability space `(Ω k, P k)` and arrival process `D^(k)` (a random counting path), such that
(a), (b) with probability one the path has finitely many arrivals, at most one at any time point, all
in `(0, τ]` (`IsArrivalPath`); and `E D^(k)(τ) = k μ` (each `D^(k)_j(τ)` integrable).
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
§4, p.723 (PDF p.4): "For the kth problem, we replace our initial capacity vector by kc, and we assume
the arrival process is given by the n-vector D^(k)(·). For each problem, we assume (as before) that,
with probability one, there is (a) a finite number of arrivals and (b) at most one arrival at any point
in time. We also will assume that ED^(k)(τ) = kμ." With §2, p.722, and μ of §3, p.723.

**Formalization Note** Problems are indexed by `k : ℕ+` (the paper's `k ⩾ 1`; there is no problem
`0`). `μ` is a real parameter (`μ < ∞`); the clause at `k = 1` makes it the expected demand
`E D^(1)(τ)` of the original problem. "A random point process" is rendered as measurability of
every count `ω ↦ D^(k)_j(t)`. The probability-measure property of `P k` is a separate instance
hypothesis of the theorems. -/
structure IsScaledFamily {n : ℕ} (τ : ℝ) (μ : Fin n → ℝ) {Ω : ℕ+ → Type*}
    [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k)) (D : ∀ k, Ω k → ℝ → Fin n → ℕ) :
    Prop where
  measurable : ∀ k t j, Measurable fun ω => D k ω t j
  path : ∀ k, ∀ᵐ ω ∂(P k), IsArrivalPath τ (D k ω)
  integrable : ∀ k j, Integrable (fun ω => (D k ω τ j : ℝ)) (P k)
  mean : ∀ k j, ∫ ω, (D k ω τ j : ℝ) ∂(P k) = ((k : ℕ) : ℝ) * μ j

end LPAllocRM


