-- Prove2me | Definitions.Def_StateIndepNRM_IsDetOptimal
-- name    : StateIndepNRM_IsDetOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:36:49.68675+00:00
-- url     : https://prove2.me/theorems/eb4df87d-2276-4440-9139-ca7df92b9203
-- title:
--   The deterministic problem $\mathbb P_{\mathrm{Det}}$
-- statement:
--   The deterministic problem $\mathbb P_{\mathrm{Det}}$ of an instance is
--
--   $$
--   \max_{(\lambda_t\in\Lambda_t:\,t\in[0,T])}\int_0^TR_t(\lambda_t)\,dt\quad\text{s.t.}\quad A\cdot\int_0^T\lambda_t\,dt\le b.
--   $$
--
--   A **feasible** solution is a measurable function $l$ with $l(t)\in\Lambda_t$ on $[0,T]$, integrable coordinates and integrable revenue rate, satisfying the capacity constraint; an **optimal** solution attains the largest objective among feasible ones. `detValue` is the objective, which is $\int_0^Tr^*_t\,dt$ at an optimal solution with $r^*_t=R_t(\lambda^*_t)$. `scaledRate k l` is the rate function $k\,l$ of $\mathbb P_{C,k}$.
--
--   The optimal solution is the fluid plan that the make-to-stock policy follows.
--
--   **Formalization Note** Integrability is part of feasibility so that the integrals of the problem are true integrals rather than Lean's default $0$.
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, §3, p.6 (P_Det, r*_t) and p.8

import Mathlib
import Definitions.Def_StateIndepNRM_Instance

open MeasureTheory Set

namespace StateIndepNRM

variable {M N : ℕ}

/-- `l` is a feasible solution of the deterministic problem `P_Det`
(Manchiraju–Dawande–Janakiraman, SSRN 3831496, §3, p.6): a measurable rate function with
`l t ∈ Λ_t` on `[0, T]` and `A · ∫₀ᵀ l t dt ≤ b`.

**Formalization Note.** Each coordinate and the revenue rate are integrable on `[0, T]`, so that
the integrals of `P_Det` are true integrals rather than the default `0`. -/
structure IsDetFeasible (I : Instance M N) (l : ℝ → Fin N → ℝ) : Prop where
  measurable : Measurable l
  mem : ∀ t ∈ Icc 0 I.T, l t ∈ I.rateSet t
  integrable : ∀ n, IntervalIntegrable (fun t => l t n) volume 0 I.T
  rev_integrable : IntervalIntegrable (fun t => I.revRate t (l t)) volume 0 I.T
  capacity : ∀ m, ∑ n, I.a m n * ∫ t in (0 : ℝ)..I.T, l t n ≤ I.b m

/-- The objective `∫₀ᵀ R_t(l t) dt` of `P_Det` (SSRN 3831496, §3, p.6); for an optimal `l` it is
`∫₀ᵀ r*_t dt`. -/
noncomputable def detValue (I : Instance M N) (l : ℝ → Fin N → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..I.T, I.revRate t (l t)

/-- `l` is an optimal solution `(λ*_t : t ∈ [0, T])` of `P_Det` (SSRN 3831496, §3, p.6). -/
structure IsDetOptimal (I : Instance M N) (l : ℝ → Fin N → ℝ) : Prop where
  feasible : IsDetFeasible I l
  optimal : ∀ l', IsDetFeasible I l' → detValue I l' ≤ detValue I l

/-- The rate function `k • l` used in the `k`-scaled problem `P_{C,k}` (SSRN 3831496, §3, p.8). -/
noncomputable def scaledRate (k : ℕ) (l : ℝ → Fin N → ℝ) : ℝ → Fin N → ℝ :=
  fun t => (k : ℝ) • l t

end StateIndepNRM


