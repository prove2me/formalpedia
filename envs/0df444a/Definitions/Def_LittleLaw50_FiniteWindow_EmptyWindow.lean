-- Prove2me | Definitions.Def_LittleLaw50_FiniteWindow_EmptyWindow
-- name    : LittleLaw50_FiniteWindow_EmptyWindow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:15.705318+00:00
-- url     : https://prove2.me/theorems/d6ac2b24-c180-4bbe-8e7d-7ad63f6af8f6
-- title:
--   §2.1.2, p. 537 — N, A, L, λ and W of Theorem LL.1 for a sample path observed over [0, T]
-- statement:
--   These are the quantities of Theorem LL.1 in Little's *Little's Law as Viewed on Its 50th Anniversary*. There is no probability: the object is one deterministic **sample path** of a queuing system, observed over a finite window $[0, T]$.
--
--   The sample path consists of finitely many items $i = 1, \dots, M$. Item $i$ arrives at time $a_i$ and leaves at time $d_i$, and is in the system at time $t$ exactly when $a_i \le t < d_i$. Its wait in the system is $W_i = d_i - a_i$. The number of items in the system at time $t$ is
--
--   $$n(t) = \#\{\, i : a_i \le t < d_i \,\},$$
--
--   the published function `KellyStochasticNetworks.occupancy`. From the path one computes:
--
--   1. the set of items arriving in $[0, T]$, namely those with $0 \le a_i \le T$, and their number $N$;
--   2. the area under $n(t)$ over $[0, T]$, $A = \int_0^T n(t)\,dt$;
--   3. $L = A/T$, the average number of items in the system during $[0, T]$ (a time average);
--   4. $\lambda = N/T$, the average arrival rate in $[0, T]$;
--   5. $W$, the sample average of the waits $W_i = d_i - a_i$ of the $N$ items arriving in $[0, T]$:
--   $$W = \frac{1}{N} \sum_{i:\ 0 \le a_i \le T} (d_i - a_i).$$
--
--   These three averages are the parameters $\{L, \lambda, W\}$ of Little's Law for a window that is empty at its two ends; each has its own dimension (items, items per unit time, time units), as the paper stresses in §2.1.4.
--
--   **Formalization Note** Items are indexed by `Fin M` with real arrival and departure epochs. $W$ is defined as the average of the individual waits, never as $A/N$; the equality of the two is the content of Theorem LL.1. When $N = 0$ the paper's $W$ is undefined, and Lean's division gives $W = 0$; when $T = 0$ the definitions give $L = \lambda = 0$, but every theorem using them assumes $T > 0$.
-- source:
--   Little, Little's Law as Viewed on Its 50th Anniversary, Oper. Res. 59(3) (2011), DOI 10.1287/opre.1110.0940, p. 537, §2.1.2 (definitions of n(t), λ, N, L, W, A before Theorem LL.1); p. 538, §2.1.4 ("What kind of averages?")

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration

namespace LittleLaw50.FiniteWindow

open KellyStochasticNetworks

/-! # The LL parameters of Theorem LL.1 (Little 2011, §2.1.2, p. 537)

A sample path has `M` items; item `i` arrives at `a i` and leaves at `d i`, and is in the system
at time `t` iff `a i ≤ t < d i`.  The number in the system at `t` is
`KellyStochasticNetworks.occupancy a d t`. -/

/-- The items arriving in `[0, T]`: those with `0 ≤ a i ≤ T`. -/
noncomputable def arrivalsIn {M : ℕ} (a : Fin M → ℝ) (T : ℝ) : Finset (Fin M) :=
  Finset.univ.filter fun i => 0 ≤ a i ∧ a i ≤ T

/-- `N`, the number of items arriving in `[0, T]`. -/
noncomputable def numArrivals {M : ℕ} (a : Fin M → ℝ) (T : ℝ) : ℝ :=
  ((arrivalsIn a T).card : ℝ)

/-- `A = ∫₀ᵀ n(t) dt`, the area under `n(t)` over `[0, T]`. -/
noncomputable def areaLL1 {M : ℕ} (a d : Fin M → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..T, occupancy a d t

/-- `L`, the time average of the number of items in the system during `[0, T]`: `A / T`. -/
noncomputable def L_LL1 {M : ℕ} (a d : Fin M → ℝ) (T : ℝ) : ℝ :=
  areaLL1 a d T / T

/-- `λ`, the average arrival rate in `[0, T]`: the number of arrivals in `[0, T]` divided by `T`. -/
noncomputable def lam_LL1 {M : ℕ} (a : Fin M → ℝ) (T : ℝ) : ℝ :=
  numArrivals a T / T

/-- `W`, the sample average of the waiting times `Wᵢ = dᵢ − aᵢ` of the items arriving in
`[0, T]`. -/
noncomputable def W_LL1 {M : ℕ} (a d : Fin M → ℝ) (T : ℝ) : ℝ :=
  (∑ i ∈ arrivalsIn a T, (d i - a i)) / numArrivals a T

end LittleLaw50.FiniteWindow


