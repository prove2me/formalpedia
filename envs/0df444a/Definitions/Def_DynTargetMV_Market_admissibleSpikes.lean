-- Prove2me | Definitions.Def_DynTargetMV_Market_admissibleSpikes
-- name    : DynTargetMV_Market_admissibleSpikes
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:33.418323+00:00
-- url     : https://prove2.me/theorems/01abb8a2-87b0-469a-8164-cfd3f62d8255
-- title:
--   The set $\Pi^{\hat\pi}_{t,x}$ of admissible deviations (corrected: the time-$t$ self\'s set)
-- statement:
--   For a strategy $\hat\pi$, a target $L$, a time $t\in[0,T)$ and a wealth $x$, the set $\Pi^{\hat\pi}_{t,x}$ consists of the $\pi\in\mathbb R^m$ with $Q\pi\ge0$ for which there is $\bar\varepsilon\in(0,T-t)$ such that, for every $\varepsilon\in(0,\bar\varepsilon]$, the wealth equation of $\pi_{t,\varepsilon,\pi}$ from $(t,x)$ has a unique strong solution $X$ with
--   $$
--   E\Bigl[\int_t^T\|\pi_{t,\varepsilon,\pi}(s,X(s))\|^2ds\Bigr]<+\infty,\quad E[X(T)^2]<+\infty,\quad E[X(T)]\ge L(t,x).
--   $$
--   These are the deviations open to the agent at time $t$ with wealth $x$: she must respect her portfolio constraint and her own current target, and she takes no responsibility for the targets of her other selves.
--
--   Differences from the source:
--   - correction: Π^π̂_{t,x} (p.8) asks that π_{t,ε,π} be feasible in the sense of p.7, with all constraints at all times along the path from x₀ → Π requires Qπ ≥ 0 and, for all small ε, a unique solution from (t,x) with square-integrable strategy and terminal value and E[X(T)] ≥ L(t,x); reason: the printed set makes the uniqueness clauses false: with m = d = 1, r = 0, b = σ = 1, Q = 0, T = 1, x₀ = γ = 1, ψ ≡ 1, the strategy π̃ ≡ e − 1 is an equilibrium of (ii) under the printed Π, and it is not (2.12); and the printed Π can be empty for target (2.7). The corrected set is what (C.10), (C.11), p.26, test
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.8, corrected to (C.10), (C.11), p.26

import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_spike
import Definitions.Def_DynTargetMV_Market_IsUniqueWealthFrom

open MeasureTheory Set Matrix

namespace DynTargetMV

/-- The set `Π^π̂_{t,x}`, as corrected: the `π ∈ ℝ^m` with `Qπ ≥ 0` such that there is `ε̄ ∈ (0,T−t)`
with, for every `ε ∈ (0,ε̄]`, a unique strong solution of the wealth equation of `π_{t,ε,π}` (2.4) from
`(t,x)`, with square-integrable strategy and terminal value and `E_t[X(T)] ≥ L(t,x)`.
He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.8, corrected to the set used at (C.10), (C.11), p.26.

**Formalization Note** The printed set asks `π_{t,ε,π}` to be feasible in the sense of p.7: all
constraints at all times, along the path from `x₀`. That set does not depend on `x`, and with it every
uniqueness clause of Theorem 1 is false and `Π` can be empty for target (2.7) (see the mission's
Differences lists). This is the set the proof tests: only `Qπ ≥ 0` and the target at `(t,x)`. Here
`E_t` is the plain expectation of the solution started at `(t,x)` (p.7: the law of `X(T)` given time
`t` "depends on the agent's wealth at time t only"). -/
def Market.admissibleSpikes {m d n : ℕ} (M : Market m d n) {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (F : Filtration ℝ mΩ) (W : Fin d → ℝ → Ω → ℝ)
    (L : ℝ → ℝ → ℝ) (πh : ℝ → ℝ → Fin m → ℝ) (t x : ℝ) : Set (Fin m → ℝ) :=
  {π | 0 ≤ M.Q *ᵥ π ∧ ∃ εbar ∈ Ioo 0 (M.T - t), ∀ ε ∈ Ioc 0 εbar,
    ∃ X : ℝ → Ω → ℝ, M.IsUniqueWealthFrom P F W (spike t ε (fun _ _ => π) πh) t x X ∧
      MemLp (X M.T) 2 P ∧
      (∫⁻ ω, (∫⁻ s in Ico t M.T,
        ENNReal.ofReal (sqNorm (spike t ε (fun _ _ => π) πh s (X s ω)))) ∂P) ≠ ⊤ ∧
      L t x ≤ ∫ ω, X M.T ω ∂P}

end DynTargetMV


