-- Prove2me | Definitions.Def_TightReleaseSchedules_Stationary_Supplement_drift_class
-- name    : TightReleaseSchedules_Stationary_Supplement_drift_class
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:18:58.816967+00:00
-- url     : https://prove2.me/theorems/a3bf83a3-e524-4c7c-931c-db542c32f549
-- title:
--   Drift class P(Δ, η), the program F(τ), the rate ϕ and Algorithm 2
-- statement:
--   For a pretrained vector $\theta_0\in\mathbb R^d$, a known initial shift $\Delta>0$ and a drift bound $\eta\ge0$, the **drift class** is
--
--   $$
--   \mathcal P(\Delta,\eta)=\big\{\theta_{1:T}:\|\theta_1-\theta_0\|_2\le\Delta,\ \|\theta_t-\theta_{t-1}\|_2\le\eta\ (2\le t\le T)\big\}.
--   $$
--
--   The worst-case risk of a policy is the supremum over $\mathcal P(\Delta,\eta)$ of $R_T(\pi;\theta_{1:T})=\tfrac12\mathbb E\sum_{t=1}^T\|w_t-\theta_t\|_2^2$, measured against the current target, and
--
--   $$
--   R^*_T(B;\Delta,\eta)=\inf_{\pi\in\Pi_B}\ \sup_{\theta_{1:T}\in\mathcal P(\Delta,\eta)}R_T(\pi;\theta_{1:T}),
--   $$
--
--   the infimum over all randomized causal policies with at most $B$ releases and adaptively chosen release times.
--
--   For an integer schedule $\tau$ with phase lengths $L_j$, put $x_0=d/\Delta^2$ and $x_j=\max\{\tau_j,d/\Delta^2\}$ for $j\ge1$. The **release-design program** and the **tracking rate** are
--
--   $$
--   F(\tau)=\sum_{j=0}^{B}\Big(L_j\frac{d}{x_j}+\eta^2L_j^3\Big),\qquad F^*_B=\min_\tau F(\tau),\qquad \phi=\min\{(d\eta)^{2/3},\eta^2T^2\}.
--   $$
--
--   **Algorithm 2** on a deterministic schedule $\tau$: set $w_0=\lceil(d/\eta^2)^{1/3}\rceil$ if $\eta>0$ and $w_0=\infty$ if $\eta=0$. At each scheduled date $n\in\{1,\dots,T-1\}$ put $w=\min\{n,w_0\}$ and release
--
--   $$
--   \theta_0+\Pi_{B_d(\Delta+\eta n)}(Z),\qquad Z=\frac1w\sum_{i=n-w+1}^{n}X_i(Y_i-X_i^\top\theta_0),
--   $$
--
--   where $B_d(r)$ is the closed Euclidean ball of radius $r$ about the origin. Scheduled dates $0$ and $T$ keep $\theta_0$.
--
--   **Formalization Note** Round $t$ is index $t-1$ of `Fin T`. The minimum $F^*_B$ is the real `sInf` over the finite nonempty set of schedules. The power $2/3$ is the real power of a nonnegative base. The infinite window at $\eta=0$ is encoded by the window length $n$ itself.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), §3.2, printed p.6, PDF p.7; §5 program (2), Theorem 5.1 and Algorithm 2, printed pp.15–16, PDF pp.16–17

import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_schedules

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace TightReleaseSchedules.Stationary.Supplement

open TightReleaseSchedules.Stationary

/-- The path class `P(Δ, η)`: `‖θ₁ − θ₀‖₂ ≤ Δ` and `‖θ_t − θ_{t−1}‖₂ ≤ η` for `2 ≤ t ≤ T`.
Index `i : Fin T` is round `i + 1`. -/
def driftClass {T d : ℕ} (θ₀ : Vector d) (Δ η : ℝ) : Set (Fin T → Vector d) :=
  {θ | (∀ i : Fin T, i.val = 0 → ‖θ i - θ₀‖ ≤ Δ) ∧
    ∀ i j : Fin T, j.val = i.val + 1 → ‖θ j - θ i‖ ≤ η}

/-- Worst-case risk `sup_{θ_{1:T} ∈ P(Δ,η)} R_T(π; θ_{1:T})`, against the current target. -/
def driftWorstRisk {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (Δ η : ℝ)
    (π : ReleasePolicy s T d B) : ℝ≥0∞ :=
  ⨆ θ : (driftClass (T := T) θ₀ Δ η : Set (Fin T → Vector d)), policyRisk θ₀ π θ.val

/-- `R*_T(B; Δ, η)`: infimum over every seed space and every causal policy with at most `B`
releases (adaptive dates allowed), outside the supremum over `P(Δ, η)`. -/
def driftMinimaxRisk (T d B : ℕ) (θ₀ : Vector d) (Δ η : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ (s : RandomSeed) (π : ReleasePolicy s T d B),
    IsCausal π ∧ v = driftWorstRisk θ₀ Δ η π}

/-- The clamped dates of program (2): `x₀ = d/Δ²` and `x_j = max{τ_j, d/Δ²}` for `j ≥ 1`. -/
def clampedDate {B : ℕ} (d : ℕ) (Δ : ℝ) (τ : Fin (B + 2) → ℕ) (j : Fin (B + 1)) : ℝ :=
  if j.val = 0 then (d : ℝ) / Δ ^ 2 else max (phaseStart τ j : ℝ) ((d : ℝ) / Δ ^ 2)

/-- The release-design program `F(τ) = ∑_{j=0}^{B} (L_j d / x_j + η² L_j³)`. -/
def driftProgram {B : ℕ} (d : ℕ) (Δ η : ℝ) (τ : Fin (B + 2) → ℕ) : ℝ :=
  ∑ j : Fin (B + 1),
    (phaseLength τ j * (d : ℝ) / clampedDate d Δ τ j + η ^ 2 * phaseLength τ j ^ 3)

/-- `F*_B`, the minimum of `F` over integer schedules. -/
def driftOptimum (T d B : ℕ) (Δ η : ℝ) : ℝ := scheduleMin T B (driftProgram d Δ η)

/-- The tracking rate `ϕ = min{(dη)^{2/3}, η²T²}`. -/
def trackingRate (T d : ℕ) (η : ℝ) : ℝ :=
  min (((d : ℝ) * η) ^ (2 / 3 : ℝ)) (η ^ 2 * (T : ℝ) ^ 2)

/-- The window `w = min{τ, w₀}` of Algorithm 2: `w₀ = ⌈(d/η²)^{1/3}⌉` if `η > 0` and
`w₀ = ∞` (all `τ` labels) if `η = 0`. -/
def windowLength (d : ℕ) (η : ℝ) (n : ℕ) : ℕ :=
  if η = 0 then n else min n ⌈((d : ℝ) / η ^ 2) ^ (1 / 3 : ℝ)⌉₊

/-- The `w` most recent labelled rounds before date `n`: rounds `n − w + 1, …, n`, i.e.
indices `n − w ≤ i < n`. -/
def recentWindow (T d : ℕ) (η : ℝ) (n : ℕ) : Finset (Fin T) :=
  Finset.univ.filter (fun i : Fin T => n - windowLength d η n ≤ i.val ∧ i.val < n)

/-- Algorithm 2 on the deterministic schedule `τ`: at a scheduled date `1 ≤ n ≤ T − 1`
release `θ₀ + Π_{B_d(Δ + ηn)}(Z)`, with `Z` the anchored average of the recent window;
scheduled dates `0` and `T` keep `θ₀` (they change no served prediction). -/
def windowedPolicy (T d B : ℕ) (θ₀ : Vector d) (Δ η : ℝ) (τ : Fin (B + 2) → ℕ) :
    ReleasePolicy unitSeed T d B where
  date := fun j _ => slotDate τ j
  head := fun j ω =>
    let n := slotDate τ j
    if n = 0 ∨ T ≤ n then θ₀ else
      θ₀ + convexProjection (Metric.closedBall (0 : Vector d) (Δ + η * n))
        (anchoredAverage θ₀ (recentWindow T d η n) ω.2)

end TightReleaseSchedules.Stationary.Supplement


