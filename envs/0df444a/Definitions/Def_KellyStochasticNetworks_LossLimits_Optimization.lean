-- Prove2me | Definitions.Def_KellyStochasticNetworks_LossLimits_Optimization
-- name    : KellyStochasticNetworks_LossLimits_Optimization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:46:21.525538+00:00
-- url     : https://prove2.me/theorems/f9ef60a3-c7f5-49fc-956d-c47f7f97af70
-- title:
--   Loss-network optimization and the scaling regime
-- statement:
--   Let $J$ and $R$ be finite numbers of links and routes, and let $A\in\mathbb N^{J\times R}$ record the circuits needed by each route. For offered rates $\nu\in\mathbb R^R$ and real capacities $C\in\mathbb R^J$, define the primal feasible region and objective by
--   $$\mathcal F(C)=\{x\ge0:Ax\le C\},\qquad F_\nu(x)=\sum_r(x_r\log\nu_r-x_r\log x_r+x_r).$$
--   The dual objective is $D_{\nu,C}(y)=\sum_r\nu_r\exp(-\sum_jy_jA_{jr})+\sum_jy_jC_j$, minimized over $y\ge0$. For a blocking vector $B$, put $x_r(B)=\nu_r\prod_j(1-B_j)^{A_{jr}}$. The blocking conditions mean $0\le B_j<1$, $Ax(B)\le C$, and equality at every link with $B_j>0$. Select a solution when one exists and call it $B(A,\nu,C)$; define $x(A,\nu,C)=x(B(A,\nu,C))$.
--
--   The scaling data consist of a fixed full-row-rank matrix $A$, positive rates $\nu(N)$ and positive integer capacities $C(N)$ for $N\ge1$, positive real vectors $\nu,C$, and coordinatewise limits $\nu(N)/N\to\nu$, $C(N)/N\to C$. Strict slack is the separate condition $(Ax)_j<C_j$ whenever the limiting selected $B_j=0$.
--
--   These objects specify both the finite-network centers and the parameters of the Gaussian limit. Existence and characterization are theorem obligations, not assumptions hidden in the selector.
--
--   **Formalization Note** Finite indices start at zero. The selector is zero if no blocking solution exists; this branch is irrelevant for positive data. The continuous extension uses $0\log0=0$. Network zero is unused. Real capacities are needed only in optimization and the limit; the stochastic networks retain natural capacities.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 57 (PDF p. 65), Eqs. (3.4)–(3.6), §3.5.1 (printed pp. 57–63 / PDF pp. 65–71); DOI 10.1017/cbo9781139565363.

import Mathlib

namespace KellyStochasticNetworks.LossLimits

/-- Real-capacity version of (3.4), with `0 log 0 = 0`. -/
noncomputable def entropyObjective {R : ℕ} (ν x : Fin R → ℝ) : ℝ :=
  ∑ r, (x r * Real.log (ν r) - x r * Real.log (x r) + x r)

def feasibleReal {J R : ℕ} (A : Fin J → Fin R → ℕ) (C : Fin J → ℝ) : Set (Fin R → ℝ) :=
  {x | (∀ r, 0 ≤ x r) ∧ ∀ j, ∑ r, (A j r : ℝ) * x r ≤ C j}

/-- (3.5) extended to positive real capacities. -/
noncomputable def dualReal {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C y : Fin J → ℝ) : ℝ :=
  (∑ r, ν r * Real.exp (-∑ j, y j * (A j r : ℝ))) + ∑ j, y j * C j

def dualOptReal {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C y : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ ∀ z : Fin J → ℝ, (∀ j, 0 ≤ z j) → dualReal A ν C y ≤ dualReal A ν C z

/-- The carried traffic associated with a blocking vector. -/
noncomputable def carried {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (B : Fin J → ℝ) : Fin R → ℝ :=
  fun r => ν r * ∏ j, (1 - B j) ^ A j r

/-- (3.6), allowing the real capacities that occur in the scaling limit. -/
def blockingConditions {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C B : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ B j ∧ B j < 1) ∧
  (∀ j, ∑ r, (A j r : ℝ) * carried A ν B r ≤ C j) ∧
  (∀ j, 0 < B j → ∑ r, (A j r : ℝ) * carried A ν B r = C j)

/-- Select the solution of (3.6); use zero off the domain of existence.
Under positive data and full row rank the solution exists and is unique.
This definition assumes neither existence nor any asymptotic property. -/
noncomputable def blocking {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ) : Fin J → ℝ := by
  classical
  exact if h : ∃ B, blockingConditions A ν C B then Classical.choose h else 0

/-- The continuous mode of (3.4), via its (3.6) characterization. -/
noncomputable def mode {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ) : Fin R → ℝ :=
  carried A ν (blocking A ν C)

/-- All standing scaling assumptions of §3.5.1 except strict slack, stated separately.
Index `N=0` is unused; network numbers are `N ≥ 1`. -/
structure Scaling {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ) : Prop where
  rank_full : (Matrix.of fun j r => (A j r : ℝ)).rank = J
  rates_pos : ∀ N, 0 < N → ∀ r, 0 < νN N r
  capacities_pos : ∀ N, 0 < N → ∀ j, 0 < CN N j
  limit_rates_pos : ∀ r, 0 < ν r
  limit_capacities_pos : ∀ j, 0 < C j
  rates_limit : ∀ r, Filter.Tendsto (fun N : ℕ => νN N r / N) Filter.atTop (nhds (ν r))
  capacities_limit : ∀ j, Filter.Tendsto (fun N : ℕ => (CN N j : ℝ) / N)
    Filter.atTop (nhds (C j))

def strictSlack {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ) : Prop :=
  ∀ j, blocking A ν C j = 0 → ∑ r, (A j r : ℝ) * mode A ν C r < C j

end KellyStochasticNetworks.LossLimits


