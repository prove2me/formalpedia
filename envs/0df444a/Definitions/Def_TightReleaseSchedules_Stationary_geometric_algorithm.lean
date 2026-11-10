-- Prove2me | Definitions.Def_TightReleaseSchedules_Stationary_geometric_algorithm
-- name    : TightReleaseSchedules_Stationary_geometric_algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:44:47.275191+00:00
-- url     : https://prove2.me/theorems/83b3bde2-65d1-4757-8027-811d80882d8b
-- title:
--   Effective horizon, exact release rate and Algorithm 1
-- statement:
--   Let $T,d\ge1$, $B\ge0$, $0<\Delta\le1$, and let $\theta_0\in\mathbb R^d$ be known. Put $m=T\Delta^2/d$ and $\alpha=d/\Delta^2$. The release rate is
--
--   $$
--   \Lambda_B(m)=\begin{cases}m,&m<1,\\1+(B+1)(m^{1/(B+1)}-1),&m\ge1.\end{cases}
--   $$
--   Algorithm 1 initially serves $\theta_0$. It chooses $J=0$ when $B=0$ or $m\le e$, $J=B$ when $m>e$ and $B+1<\log m$, and $J=\lceil\log m\rceil-1$ otherwise. For $J\ge1$, put $r=m^{1/(J+1)}$ and form the distinct dates $N=\{\lceil\alpha r^j\rceil<T:1\le j\le J\}$. At date $n\in N$, after observing row $n$, it replaces the head by
--
--   $$
--   \theta_0+\Pi_{B_d(\Delta)}\!\left(\frac1n\sum_{i=1}^nX_i(Y_i-X_i^\top\theta_0)\right).
--   $$
--   Here $B_d(\Delta)$ is the closed Euclidean ball centered at zero. Dates are deduplicated and sorted, with unused slots padded at $T$. The chosen head is retained until the next release. The lower-bound regime is $m<256$ or $m\ge256$ together with $B+1\ge\log m$ or $d\ge1+2\log_2\log_2m$. This module defines the actual policy and rate used in the goal.
--
--   **Formalization Note** Powers in the rate use a real reciprocal exponent; $\log$ is natural and $\log_2x=\log x/\log2$. Natural ceilings agree with the source's integer ceilings on the positive inputs in use. At unused slots, or at an impossible zero date, the head is assigned $\theta_0$.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), equation (1), printed p.1, PDF p.2; Theorem 4.1 and Algorithm 1, printed p.8, PDF p.9

import Definitions.Def_TightReleaseSchedules_Stationary_release_policy

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace TightReleaseSchedules.Stationary

def effectiveHorizon (T d : ℕ) (Δ : ℝ) : ℝ := T * Δ ^ 2 / d

def releaseRate (B : ℕ) (m : ℝ) : ℝ :=
  if m < 1 then m else 1 + (B + 1 : ℝ) * (m ^ (1 / (B + 1 : ℝ)) - 1)

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

def geometricCount (T d B : ℕ) (Δ : ℝ) : ℕ :=
  let m := effectiveHorizon T d Δ
  if B = 0 ∨ m ≤ Real.exp 1 then 0
  else if (B + 1 : ℝ) < Real.log m then B else ⌈Real.log m⌉₊ - 1

def geometricGrid (T d B : ℕ) (Δ : ℝ) : Finset ℕ :=
  let J := geometricCount T d B Δ
  let α : ℝ := d / Δ ^ 2
  let r : ℝ := effectiveHorizon T d Δ ^ (1 / (J + 1 : ℝ))
  ((Finset.Icc 1 J).image (fun j => ⌈α * r ^ j⌉₊)).filter (fun n => n < T)

/-- Deduplicate before sorting. All unused slots are at T. -/
def geometricDate (T d B : ℕ) (Δ : ℝ) (j : Fin B) : ℕ :=
  ((geometricGrid T d B Δ).sort (· ≤ ·))[j.val]?.getD T

def geometricPolicy (T d B : ℕ) (θ₀ : Vector d) (Δ : ℝ) : ReleasePolicy unitSeed T d B where
  date := fun j _ => geometricDate T d B Δ j
  head := fun j ω =>
    let n := geometricDate T d B Δ j
    if n = 0 ∨ T ≤ n then θ₀ else
      θ₀ + convexProjection (Metric.closedBall (0 : Vector d) Δ)
        (anchoredAverage θ₀ (Finset.univ.filter (fun i : Fin T => i.val < n)) ω.2)

def lowerBoundRegime (T d B : ℕ) (Δ : ℝ) : Prop :=
  let m := effectiveHorizon T d Δ
  m < 256 ∨ (256 ≤ m ∧
    (Real.log m ≤ (B + 1 : ℝ) ∨ 1 + 2 * logTwo (logTwo m) ≤ (d : ℝ)))

end TightReleaseSchedules.Stationary


