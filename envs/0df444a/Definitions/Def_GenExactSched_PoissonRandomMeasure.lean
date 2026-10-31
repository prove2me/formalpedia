-- Prove2me | Definitions.Def_GenExactSched_PoissonRandomMeasure
-- name    : GenExactSched_PoissonRandomMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:16.012881+00:00
-- url     : https://prove2.me/theorems/4fa35a77-655c-430f-a94c-62e0e3b08c91
-- title:
--   Poisson random measure (the marked Poisson arrival process)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $(E,\mathcal E)$ a measurable space and $\nu$ a measure on $E$. A family $N=(N_\omega)_{\omega\in\Omega}$ of measures on $E$ is a **Poisson random measure with intensity $\nu$** if
--
--   1. for every measurable $A\subseteq E$, the count $\omega\mapsto N_\omega(A)$ is measurable;
--   2. for every measurable $A$ with $\nu(A)<\infty$, $N(A)$ has the Poisson law with mean $\nu(A)$;
--   3. for pairwise disjoint measurable $A_1,\dots,A_n$ of finite intensity, $N(A_1),\dots,N(A_n)$ are independent.
--
--   A sum $\sum_k g(x_k)$ over the points of the process is the integral $\int g\,dN_\omega$. In the scheduling model, $E=\mathbb R\times\mathbb R^2$ carries the jobs $(a_k;\sigma_k,\tau_k)$ (arrival time, demand, sojourn time), and the independently marked stationary Poisson arrival process of the paper is a Poisson random measure with intensity $\Lambda\,da\otimes f(\sigma,\tau)\,d\sigma\,d\tau$.
--
--   **Formalization Note** Only the three defining properties are required (no atomicity, no filtration). Independence is stated for finite families, which is equivalent to independence of countable families. The Poisson law is Mathlib's `poissonMeasure`, pushed to $[0,\infty]$. Existence of a Poisson random measure for a σ-finite intensity is classical (Kingman) but not in Mathlib.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, §2 p. 4 (marked Poisson point process on T × S), §3.1 p. 7 (intensity Λf(σ, τ)), Appendix A, Theorem 7, p. 38

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Poisson random measure** with intensity `ν` on a measurable space `E`, over a probability
space `(Ω, P)`. This is the object behind the independently marked Poisson point process of
Nakahira–Ferragut–Wierman, arXiv:2004.12280v2, §2 p. 4 ("{(a_k; σ_k, τ_k)} is a Poisson point
process on T × S") and Theorem 7, p. 38.

`N ω` is the counting measure of the realized points; a sum `Σ_k g(x_k)` over the points is the
integral `∫ g dN(ω)`. The three fields are the standard defining properties:

1. for every measurable `A`, `ω ↦ N ω A` is measurable;
2. for every measurable `A` with `ν A < ∞`, the law of `N(·)(A)` is Poisson with mean `ν A`
   (Mathlib's `poissonMeasure`, pushed to `ℝ≥0∞` by the cast `ℕ → ℝ≥0∞`);
3. for finitely many pairwise disjoint measurable sets of finite intensity, the counts are
   independent.

**Formalization Note.** Only these three properties are required: no atomicity, no filtration,
no past/future independence. Independence is stated for finite families (`Fin n`), which is
equivalent to independence of countable families. Existence of such an `N` for a σ-finite `ν`
is classical (Kingman) but not in Mathlib. -/
structure IsPoissonRandomMeasure {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E) (N : Ω → Measure E) : Prop where
  measurable_eval : ∀ A : Set E, MeasurableSet A → Measurable (fun ω => N ω A)
  poisson_law : ∀ A : Set E, MeasurableSet A → ν A ≠ ∞ →
    P.map (fun ω => N ω A) = (poissonMeasure (ν A).toNNReal).map (fun n : ℕ => (n : ℝ≥0∞))
  indep_disjoint : ∀ (n : ℕ) (A : Fin n → Set E), (∀ i, MeasurableSet (A i)) →
    (∀ i, ν (A i) ≠ ∞) → Pairwise (fun i j => Disjoint (A i) (A j)) →
    iIndepFun (fun i ω => N ω (A i)) P

end GenExactSched


