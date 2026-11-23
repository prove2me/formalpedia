-- Prove2me | Definitions.Def_RelaxedEqMDP_Discrete_Supplement_Discretization
-- name    : RelaxedEqMDP_Discrete_Supplement_Discretization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:05:05.713752+00:00
-- url     : https://prove2.me/theorems/65bbc7bb-9d76-4cf2-90e4-b0c0836be1db
-- title:
--   (5.1)–(5.4), pp. 17–18 — step-h discretization of the continuous-time MDP, with the discount sampled as δ(kh), and uniform Riemann tails
-- statement:
--   Discretization of the continuous-time model of §3 with step $h>0$. The discrete-time chain has transition matrices and rewards
--   $$(p_h)^u_i:=h\,q^u_i+e_i,\qquad f_h(k,i,u):=f(kh,i,u)\,h\qquad(k\in\mathbb N_0),$$
--   where $e_i$ is the $i$-th standard basis vector, as in (5.1)–(5.2). For small $h$ the matrix $p_h^u=hq^u+I$ is stochastic. Applying the base mission's discrete-time objects to $(p_h,f_h)$ gives the value $J^{h,\pi}$ of (5.3) and the relaxed equilibria for it. For the regularized problem (5.4) the base value $J^\pi_{h\lambda}$ is used with the discount sampled on the grid,
--   $$\delta_h(k):=\delta(kh),$$
--   so that $h\lambda\sum_k\delta(kh)\mathcal H(\cdot)$ is the Riemann sum of $\lambda\int_0^\infty\delta(s)\mathcal H(\cdot)\,ds$ in (3.2).
--
--   The file also defines **uniform Riemann tails** along a sequence of steps $h_n$: there is a majorant $b(s)\ge\sup_{i,u\in U}|f(s,i,u)|$ on $[0,\infty)$ such that each series $\sum_kb(kh_n)$ converges and
--   $$\lim_{T\to\infty}\ \sup_n\ h_n\sum_{k:\,kh_n\ge T}b(kh_n)=0 .$$
--   This holds, for example, when $\sup_{i,u}|f(s,i,u)|$ has a nonincreasing integrable majorant.
--
--   These objects state the convergence Theorem 5.1 from discrete to continuous time.
--
--   **Formalization Note** The page prints $\delta(k)$ in (5.4); the definition uses $\delta(kh)$, which is what the proof of Theorem 5.1 (p. 26) needs (see that theorem). The tail condition is the repair of the Riemann-tail step (A.21) in the proof of Lemma 5.1; the series are required to converge so that the tail sums are genuine sums.
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, pp. 17–18, (5.1)–(5.4); p. 25, (A.20)–(A.21)

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete.Supplement

/-- (5.1) (p. 17): the transition matrices of the step-`h` discretization, `(p_h)^u_i := h q^u_i + e_i`,
i.e. `(p_h)^u = h q^u + 1`. -/
def ph {d ℓ : ℕ} (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (h : ℝ) : A ℓ → Matrix (Fin d) (Fin d) ℝ :=
  fun u => h • q u + 1

/-- (5.2) (p. 17): the step-`h` reward `f_h(k,i,u) := f(kh,i,u) h` for `k ∈ ℕ₀`. -/
def fh {d ℓ : ℕ} (f : ℝ → Fin d → A ℓ → ℝ) (h : ℝ) : ℕ → Fin d → A ℓ → ℝ :=
  fun k i u => f ((k : ℝ) * h) i u * h

/-- The discount sampled on the grid, `δ_h(k) := δ(kh)`: the Riemann-sum analogue of `δ(s)` in
(3.2), used in the regularized discretization (5.4) (where the page prints `δ(k)`). -/
def deltah (δ : ℝ → ℝ) (h : ℝ) : ℕ → ℝ :=
  fun k => δ ((k : ℝ) * h)

/-- Uniform Riemann tails of the reward along the step sizes `h_n`:
there is a majorant `b(s) ≥ sup_{i,u∈U} |f(s,i,u)|` on `[0,∞)` such that every series
`∑_k b(k h_n)` converges and
`lim_{T→∞} sup_n h_n ∑_{k : k h_n ≥ T} b(k h_n) = 0`. -/
def UniformRiemannTail {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℝ → Fin d → A ℓ → ℝ) (h : ℕ → ℝ) : Prop :=
  ∃ b : ℝ → ℝ, (∀ s, 0 ≤ s → ∀ i, ∀ u ∈ U, |f s i u| ≤ b s) ∧
    (∀ n, Summable (fun k : ℕ => b ((k : ℝ) * h n))) ∧
    ∀ η > 0, ∃ T : ℝ, ∀ n, h n * ∑' k : ℕ,
      Set.indicator {k : ℕ | T ≤ (k : ℝ) * h n} (fun k : ℕ => b ((k : ℝ) * h n)) k ≤ η

end RelaxedEqMDP.Discrete.Supplement


