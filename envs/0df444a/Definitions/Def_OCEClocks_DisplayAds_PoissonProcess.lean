-- Prove2me | Definitions.Def_OCEClocks_DisplayAds_PoissonProcess
-- name    : OCEClocks_DisplayAds_PoissonProcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:20:42.754945+00:00
-- url     : https://prove2.me/theorems/ba621119-040c-42e0-9db2-3f5a14fc445b
-- title:
--   The stationary Poisson process on $\mathbb R$, first ages $\widehat A(I)$ and their distribution functions $F_x$ (§3.2)
-- statement:
--   Fix a rate $\lambda>0$. The **stationary Poisson process of rate $\lambda$ on $\mathbb R$** has arrivals $(T_k)_{k\in\mathbb Z}$ in increasing order with $T_0\le 0<T_1$. As on p. 8 of the paper, it is built from i.i.d. $\mathrm{Exp}(\lambda)$ variables $(G_k)_{k\in\mathbb Z}$:
--
--   $$T_k=G_1+\dots+G_k\ (k\ge1),\qquad T_k=-(G_k+\dots+G_0)\ (k\le0).$$
--
--   So $-T_0$ and $T_1$ are independent $\mathrm{Exp}(\lambda)$, and all other gaps are i.i.d. $\mathrm{Exp}(\lambda)$, in both directions.
--
--   The **age of an arrival** $T_k$ is $T_k-T_{k-1}$, the age just before it. For a bounded interval $I$, the **first age** $\widehat A(I)$ is the age of the first arrival in $I$, or $0$ if $I$ contains no arrival.
--
--   For $x>0$, $F_x$ is the cumulative distribution function of the first age of an interval of length $x$. By stationarity this law depends only on $x$; here it is taken for $I=[0,x)$:
--
--   $$F_x(a)=\Pr\big[\widehat A([0,x))\le a\big].$$
--
--   The First-Age Poisson generator turns first ages into exponential clocks through $F_x$. Lemma 7 computes $F_x$, and Lemma 8 shows that first ages of disjoint intervals are negatively associated.
--
--   **Formalization Note** The sample space is `ℤ → ℝ` with the product measure `Measure.infinitePi` of `expMeasure λ`. `arrival G k` is $T_k$. `firstAge G I` is $t-\sup\{T_k: T_k<t\}$, where $t=\inf\{T_k : T_k\in I\}$ is the first arrival in $I$, and $0$ when no $T_k$ lies in $I$. On the probability-one event that all gaps are positive (so arrivals are increasing and locally finite), this is the paper's first age. `firstAgeCDF λ x a` is $F_x(a)$.
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), pp. 7–8, §3.2 (stationary Poisson process, age, first age, F_x; construction from Exp(λ) gaps on p. 8)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace OCEClocks.DisplayAds

/-!
# The stationary Poisson process on `ℝ`, first ages and `F_x` (§3.2)

Huang, Patton, Yang, Zhao, *Online Correlated Exponential Clocks*, STOC 2027 submission
(manuscript of November 3, 2026), pp. 7–8, §3.2.

A stationary Poisson process of rate `λ` on `ℝ` has arrivals `(T_k)_{k ∈ ℤ}` in increasing order
with `T_0 ≤ 0 < T_1`. As on p. 8, it is realised from i.i.d. `Exp(λ)` variables `G_k`, `k ∈ ℤ`:
`T_1 = G_1` and `-T_0 = G_0` are independent `Exp(λ)`, later gaps `T_{k+1} - T_k = G_{k+1}`
(`k ≥ 1`) and earlier gaps `T_k - T_{k-1} = G_{k-1}` (`k ≤ 0`) are i.i.d. `Exp(λ)`.
-/

/-- The law of the gap sequence `G = (G_k)_{k ∈ ℤ}`: i.i.d. `Exp(λ)` (a probability measure for
`λ > 0`). -/
noncomputable def gapLaw (lam : ℝ) : Measure (ℤ → ℝ) :=
  Measure.infinitePi (fun _ : ℤ => expMeasure lam)

/-- The arrival times built from the gaps: `T_k = G_1 + ⋯ + G_k` for `k ≥ 1` and
`T_k = -(G_k + ⋯ + G_0)` for `k ≤ 0`; so `T_1 = G_1`, `T_0 = -G_0`. -/
noncomputable def arrival (G : ℤ → ℝ) (k : ℤ) : ℝ :=
  if 0 < k then ∑ i ∈ Finset.Ioc 0 k, G i else -∑ i ∈ Finset.Icc k 0, G i

open Classical in
/-- The first age `Â(I)` of a set `I ⊆ ℝ` (p. 7): the age of the first arrival in `I`, i.e.
`t - max {T_k : T_k < t}` where `t` is the first arrival in `I`, or `0` if `I` contains no
arrival. -/
noncomputable def firstAge (G : ℤ → ℝ) (I : Set ℝ) : ℝ :=
  if ∃ k, arrival G k ∈ I then
    sInf {s | ∃ k, arrival G k = s ∧ s ∈ I} -
      sSup {s | ∃ k, arrival G k = s ∧ s < sInf {s' | ∃ k', arrival G k' = s' ∧ s' ∈ I}}
  else 0

/-- `F_x`, the cumulative distribution function of the first age of an interval of length `x`
(p. 7), taken for `I = [0, x)`: `F_x(a) = P[Â([0, x)) ≤ a]`. -/
noncomputable def firstAgeCDF (lam x a : ℝ) : ℝ :=
  (gapLaw lam {G | firstAge G (Set.Ico 0 x) ≤ a}).toReal

end OCEClocks.DisplayAds


