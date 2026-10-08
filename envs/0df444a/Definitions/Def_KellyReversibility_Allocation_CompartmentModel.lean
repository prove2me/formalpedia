-- Prove2me | Definitions.Def_KellyReversibility_Allocation_CompartmentModel
-- name    : KellyReversibility_Allocation_CompartmentModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:50:04.296956+00:00
-- url     : https://prove2.me/theorems/83a61dd8-4722-4829-9ea9-9fa3cfed4a51
-- title:
--   §4.5 — the compartmental model with Poisson arrivals observed at time t; counts n_j(t) and α_j(t)
-- statement:
--   Particles (individuals) arrive at a system of $J$ compartments in a Poisson stream of rate $\nu > 0$, the system being empty at time $0$, and after arrival move through the compartments independently of one another. Let $p_j(s)$ be the probability that an individual is in compartment $j$ a time $s$ after its arrival; $p_j$ is measurable, $p_j(s) \ge 0$, and $\sum_j p_j(s) \le 1$ (the remainder have left the system).
--
--   Fix a time $t > 0$ and a probability space $(\Omega, P)$. The model at time $t$ consists of:
--
--   1. $M$, the number of arrivals in $(0, t)$, with the Poisson law of mean $\nu t$:
--   $$P(M = n) = e^{-\nu t}\frac{(\nu t)^n}{n!}, \qquad n = 0, 1, 2, \dots$$
--   2. For $r = 0, 1, 2, \dots$, the arrival instant $T_r$ of the $r$-th individual and its location $L_r$ at time $t$, which is either a compartment $j$ or "has left".
--   3. The pairs $(T_r, L_r)$ are independent and identically distributed and independent of $M$; $T_r$ is uniform on $(0, t)$, and for every measurable $B \subseteq \mathbb{R}$
--   $$P(T_r \in B,\ L_r = j) = \frac1t\int_{B\cap(0,t)} p_j(t-u)\,du,$$
--   that is, an individual arriving at instant $u$ is in compartment $j$ at time $t$ with probability $p_j(t-u)$.
--
--   Only the individuals $r < M$ exist. The **number in compartment $j$ at time $t$** is
--   $$n_j(t) = \#\{r < M : L_r = j\},$$
--   and
--   $$\alpha_j(t) = \int_0^t p_j(u)\,du.$$
--
--   This is the setting of Theorem 4.2: given $M$, the arrival instants are independent and uniform on $(0,t)$ and the individuals move independently.
--
--   **Formalization Note** "Given $M$, the arrival instants $t_1,\dots,t_M$ are independent uniform and the individuals move independently" is formalized by an infinite i.i.d. sequence of (instant, location) pairs independent of $M$, of which the first $M$ are used; this has the same conditional law. The location is a value of `Fin J ⊕ Unit`, with `Sum.inr ()` meaning the individual has left. The hypotheses on $p_j$ are imposed for $s \ge 0$ only.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 113–115, §4.5 and the proof of Theorem 4.2

import Mathlib

open MeasureTheory

namespace KellyReversibility.Allocation

/-- **The compartmental model observed at time `t`** (Kelly 1979, §4.5, pp. 113–115), on a
probability space `(Ω, P)`.

* `M ω` is the number of arrivals in the interval `(0, t)`; the arrival stream is Poisson of
  rate `ν`, so `M` has the Poisson law of mean `ν t`.
* For `r : ℕ`, `T r ω` is the arrival instant of the `r`-th arriving individual and `Loc r ω`
  is where that individual is at time `t`: `Sum.inl j` means compartment `j`,
  `Sum.inr ()` means it has left the system.  Only the individuals `r < M ω` exist.
* The pairs `(T r, Loc r)` are independent and identically distributed, and independent of
  `M`; `T r` is uniform on `(0, t)`, and an individual arriving at instant `u` is in
  compartment `j` at time `t` with probability `p j (t - u)`.  Thus, conditionally on `M`,
  the arrival instants are independent uniform on `(0, t)` and the individuals move
  independently, as in the proof of Theorem 4.2.
* `p j s` is the probability that an individual is in compartment `j` a time `s` after its
  arrival: measurable, nonnegative, and `∑ j, p j s ≤ 1` (the remainder have left). -/
structure IsCompartmentModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {J : ℕ} (ν t : ℝ) (p : Fin J → ℝ → ℝ)
    (M : Ω → ℕ) (T : ℕ → Ω → ℝ) (Loc : ℕ → Ω → Fin J ⊕ Unit) : Prop where
  isProb : IsProbabilityMeasure P
  rate_pos : 0 < ν
  time_pos : 0 < t
  p_meas : ∀ j, Measurable (p j)
  p_nonneg : ∀ j s, 0 ≤ s → 0 ≤ p j s
  p_sum_le : ∀ s, 0 ≤ s → ∑ j, p j s ≤ 1
  M_meas : Measurable M
  T_meas : ∀ r, Measurable (T r)
  Loc_meas : ∀ r, Measurable (Loc r)
  M_poisson : ∀ n : ℕ,
    P {ω | M ω = n} = ENNReal.ofReal (Real.exp (-(ν * t)) * (ν * t) ^ n / n.factorial)
  T_uniform : ∀ r (B : Set ℝ), MeasurableSet B →
    P {ω | T r ω ∈ B} = volume (B ∩ Set.Ioo 0 t) / ENNReal.ofReal t
  Loc_law : ∀ r (B : Set ℝ), MeasurableSet B → ∀ j : Fin J,
    P {ω | T r ω ∈ B ∧ Loc r ω = Sum.inl j}
      = ENNReal.ofReal ((1 / t) * ∫ u in B ∩ Set.Ioo 0 t, p j (t - u))
  indep_pairs : ProbabilityTheory.iIndepFun (fun r ω => (T r ω, Loc r ω)) P
  indep_M : ProbabilityTheory.IndepFun M (fun ω r => (T r ω, Loc r ω)) P

/-- **`n_j(t)`**, the number of individuals in compartment `j` at time `t`: the number of the
`M ω` arrivals in `(0, t)` that are in compartment `j` at time `t`. -/
def compartmentCount {Ω : Type*} {J : ℕ} (M : Ω → ℕ) (Loc : ℕ → Ω → Fin J ⊕ Unit)
    (j : Fin J) (ω : Ω) : ℕ :=
  ((Finset.range (M ω)).filter (fun r => Loc r ω = Sum.inl j)).card

/-- **`α_j(t) = ∫₀ᵗ p_j(u) du`** (Kelly 1979, Theorem 4.2, p. 115). -/
noncomputable def alpha {J : ℕ} (p : Fin J → ℝ → ℝ) (j : Fin J) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, p j u

end KellyReversibility.Allocation


