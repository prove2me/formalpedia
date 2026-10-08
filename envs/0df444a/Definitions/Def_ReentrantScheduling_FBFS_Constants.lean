-- Prove2me | Definitions.Def_ReentrantScheduling_FBFS_Constants
-- name    : ReentrantScheduling_FBFS_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:42.328167+00:00
-- url     : https://prove2.me/theorems/fe9c9761-4d1a-435c-92ca-f0b275f7982a
-- title:
--   Proof of Theorem 1, pp. 1409–1410 — the busy-period constants Γ^(i), Γ̄ and the i-busy predicate
-- statement:
--   This file defines the explicit constants and the busy-period notion of the proof of Theorem 1 of Lu and Kumar (1991), for a line with data $m_\sigma,\sigma_i,\tau_i$ and arrival constants $\lambda,\gamma$.
--
--   **Busy periods.** At time $t$, buffer $b_i$ is *busy* if some part waits for service in some buffer $b_j$ with $j\le i$ located at the same center $\sigma_i$, that is,
--   $$\sum_{j:\ \sigma_j=\sigma_i,\ j\le i}x_j(t)>0 ,$$
--   where $x_j(t)$ is the number of parts waiting in $b_j$, not counting any in service. An interval $[T_1,T_2]$ is an **$i$-busy period** if $b_i$ is busy at every instant of it.
--
--   **The constants.** With $\bar\tau=\max_j\tau_j$, define recursively for $i=1,\dots,l$
--   $$\bar\Gamma_i=\sum_{j=1}^{i-1}\big(\Gamma^{(j)}+\tau_j\big),\qquad
--   \Gamma^{(i)}=\frac{2\bar\tau+\sum_{j:\ \sigma_j=\sigma_i,\ j\le i}\dfrac{\lambda\tau_j\bar\Gamma_i+\gamma\tau_j}{m_{\sigma_i}}}{1-\sum_{j:\ \sigma_j=\sigma_i,\ j\le i}\dfrac{\lambda\tau_j}{m_{\sigma_i}}} .$$
--   For $i=1$ this is $\Gamma^{(1)}=(2\bar\tau+\gamma\tau_1/m_{\sigma_1})(1-\lambda\tau_1/m_{\sigma_1})^{-1}$, the constant of p. 1409. Under the load condition (3) every denominator is at least $1-\rho>0$.
--
--   These constants bound the lengths of $i$-busy periods and the delays of parts in the proof of Theorem 1; $\sum_{j=1}^{l}(\Gamma^{(j)}+\tau_j)$ bounds the delay of every part released after a finite transient.
--
--   **Formalization Note** Buffers are 0-based, so `Gamma lam γ i` is the paper's $\Gamma^{(i+1)}$ and `GammaBar lam γ i` is the $\bar\Gamma$ used for it. The page (p. 1410) prints $\Gamma^{(i)}$ as a *product* of the two brackets, and the second sum's index set as "$\sigma_j=\sigma,$ and $j\le i$". The inequality it is solved from, $(T_2-T_1-2\bar\tau)m_{\sigma_i}\le\sum[\lambda\tau_j(T_2-T_1)+\lambda\tau_j\bar\Gamma+\gamma\tau_j]$, gives the quotient, which is also the form of $\Gamma^{(1)}$ on p. 1409; the Lean uses the quotient over $\sigma_j=\sigma_i$. The recursion is a well-founded definition; `Gamma_eq` unfolds it in terms of `GammaBar`. When (3) fails the denominator may be $\le 0$; the constants are only used under (3).
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1409 (i-busy period; Γ^(1)) and p. 1410 (Γ̄, Γ^(i)), proof of Theorem 1

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model

namespace ReentrantScheduling.FBFS

open Finset

namespace Line

variable (L : Line)

/-- The busy-period constants `Γ^(i)` of the proof of Theorem 1 (p. 1409 for `i = 1`, p. 1410 in
general), by strong recursion on the 0-based buffer index `i` (the paper's `i + 1`):

`Γ^(i) = [2 τ̄ + ∑_{j ≤ i, σ_j = σ_i} (λ τ_j Γ̄ + γ τ_j) / m_{σ_i}] / [1 - ∑_{j ≤ i, σ_j = σ_i} λ τ_j / m_{σ_i}]`

with `Γ̄ = ∑_{j < i} (Γ^(j) + τ_j)`. The page prints the second bracket as a factor; the
inequality it is solved from gives the quotient, which is also the form of `Γ^(1)` on p. 1409. -/
noncomputable def Gamma (lam γ : ℝ) (i : Fin L.l) : ℝ :=
  (2 * L.τbar +
      ∑ j ∈ univ.filter (fun j => j ≤ i ∧ L.center j = L.center i),
        (lam * L.τ j *
            (∑ k ∈ (univ.filter (fun k : Fin L.l => k < i)).attach,
              (Gamma lam γ k.1 + L.τ k.1)) +
          γ * L.τ j) / (L.m (L.center i) : ℝ)) /
    (1 - ∑ j ∈ univ.filter (fun j => j ≤ i ∧ L.center j = L.center i),
      lam * L.τ j / (L.m (L.center i) : ℝ))
termination_by i.val
decreasing_by exact (mem_filter.mp k.2).2

/-- `Γ̄ = ∑_{j < i} (Γ^(j) + τ_j)` (p. 1410, first line), the bound on the time a part released
after `T̄` takes to reach buffer `b_i`. -/
noncomputable def GammaBar (lam γ : ℝ) (i : Fin L.l) : ℝ :=
  ∑ j ∈ univ.filter (fun j => j < i), (L.Gamma lam γ j + L.τ j)

/-- Unfolding of `Γ^(i)` in terms of `Γ̄`. -/
theorem Gamma_eq (lam γ : ℝ) (i : Fin L.l) :
    L.Gamma lam γ i =
      (2 * L.τbar +
          ∑ j ∈ univ.filter (fun j => j ≤ i ∧ L.center j = L.center i),
            (lam * L.τ j * L.GammaBar lam γ i + γ * L.τ j) / (L.m (L.center i) : ℝ)) /
        (1 - ∑ j ∈ univ.filter (fun j => j ≤ i ∧ L.center j = L.center i),
          lam * L.τ j / (L.m (L.center i) : ℝ)) := by
  rw [Gamma]
  simp only [GammaBar]
  congr 2
  refine sum_congr rfl fun j _ => ?_
  rw [sum_attach _ (fun k => L.Gamma lam γ k + L.τ k)]

end Line

namespace Run

variable {L : Line} (R : Run L)

/-- `R.Busy i t`: some part is waiting at time `t` in some buffer `b_j` with `j ≤ i` at the
center `σ_i` (p. 1409: `∑_{j : σ_j = σ_i, j ≤ i} x_j(t) > 0`). An interval `[T₁, T₂]` is an
`i`-busy period when this holds at every `t` in it. -/
def Busy (i : Fin L.l) (t : ℝ) : Prop :=
  ∃ q j, L.center j = L.center i ∧ j ≤ i ∧ R.Waiting q j t

end Run

end ReentrantScheduling.FBFS


