-- Prove2me | Definitions.Def_TightReleaseSchedules_Stationary_Supplement_block_class
-- name    : TightReleaseSchedules_Stationary_Supplement_block_class
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:18:20.999998+00:00
-- url     : https://prove2.me/theorems/38a1f31c-84d3-4f2c-813e-170587619988
-- title:
--   Known-block shift class, the program E(τ) and the block-projected grid
-- statement:
--   Let the coordinates $\{1,\dots,d\}$ be partitioned into known nonempty blocks $S_1,\dots,S_K$ of sizes $d_i=|S_i|$, with radii $\Delta_i>0$, and let $P_{S}$ denote coordinate projection onto $S$. Given a pretrained vector $\theta_0\in\mathbb R^d$, the **block class** consists of the constant targets $\theta$ with
--
--   $$
--   \|P_{S_i}(\theta-\theta_0)\|_2\le\Delta_i\qquad(i=1,\dots,K).
--   $$
--
--   For an integer schedule $\tau$ with phase lengths $L_j$, the **block program** and its optimum are
--
--   $$
--   E(\tau)=\sum_{j=0}^{B}L_j\sum_{i=1}^{K}\min\Big\{\frac{d_i}{\tau_j},\Delta_i^2\Big\},\qquad E^*_B=\min_\tau E(\tau),
--   $$
--
--   with the convention $d_i/0=\infty$, so the coefficient at $\tau_j=0$ is $\Delta_i^2$. The worst-case risk of a policy $\pi$ is the supremum over the block class of the cumulative half-squared risk $R_T(\pi;\theta)=\tfrac12\mathbb E\sum_{t=1}^T\|w_t-\theta\|_2^2$ of the base mission, and the **block minimax risk** is its infimum over all randomized causal policies with at most $B$ releases (adaptive release times allowed), for every seed space.
--
--   The **block-projected grid** on a schedule $\tau$ releases at the fixed dates $\tau_1,\dots,\tau_B$. At a date $1\le n<T$ it releases
--
--   $$
--   \theta_0+\Pi_{\mathcal K}\Big(\frac1n\sum_{t\le n}X_t(Y_t-X_t^\top\theta_0)\Big),\qquad \mathcal K=\{\beta:\|P_{S_i}\beta\|_2\le\Delta_i\text{ for every }i\},
--   $$
--
--   the Euclidean projection of the anchored average onto the product of block balls; a release at date $0$ keeps $\theta_0$, and a release at date $T$ serves no round.
--
--   **Formalization Note** The convention $d_i/0=\infty$ is encoded by the explicit case `if τ = 0 then Δᵢ² else min (dᵢ/τ) Δᵢ²`; Lean's `x/0 = 0` is never used. The minimum $E^*_B$ is the real `sInf` over the finite nonempty set of schedules. Risks are extended nonnegative reals; the minimax value is a set infimum over seed spaces to avoid a universe restriction, as for the base `minimaxRisk`. The projection set $\mathcal K$ is nonempty, closed and convex, so the base `convexProjection` is the true projection there.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), §4.4 and Theorem 4.3 with its proof, printed pp.13–14, PDF pp.14–15; risk and policy class §3, printed pp.5–6, PDF pp.6–7

import Definitions.Def_TightReleaseSchedules_Stationary_multiscale_prior
import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_schedules

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace TightReleaseSchedules.Stationary.Supplement

open TightReleaseSchedules.Stationary

/-- The known blocks `S_1, …, S_K` form a partition of the coordinates: nonempty, pairwise
disjoint, and covering `Fin d`. -/
def IsBlockPartition {d K : ℕ} (S : Fin K → Finset (Fin d)) : Prop :=
  (∀ i, (S i).Nonempty) ∧ Pairwise (fun i j => Disjoint (S i) (S j)) ∧ ∀ c, ∃ i, c ∈ S i

/-- `min{d_i/τ, Δ_i²}` with the source's convention `d_i/0 = ∞`, so the value at `τ = 0`
is `Δ_i²` (Lean's `d_i/0 = 0` is never used). -/
def blockCoeff (dᵢ : ℕ) (Δᵢ : ℝ) (τ : ℕ) : ℝ :=
  if τ = 0 then Δᵢ ^ 2 else min ((dᵢ : ℝ) / τ) (Δᵢ ^ 2)

/-- The block program `E(τ) = ∑_{j=0}^{B} L_j ∑_{i=1}^{K} min{d_i/τ_j, Δ_i²}`. -/
def blockProgram {d K B : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ)
    (τ : Fin (B + 2) → ℕ) : ℝ :=
  ∑ j : Fin (B + 1), phaseLength τ j * ∑ i : Fin K, blockCoeff (S i).card (Δ i) (phaseStart τ j)

/-- `E*_B`, the minimum of `E` over integer schedules. -/
def blockOptimum (T B : ℕ) {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) : ℝ :=
  scheduleMin T B (blockProgram S Δ)

/-- The product of block balls `{β : ‖P_{S_i} β‖₂ ≤ Δ_i for every i}`. -/
def blockBall {d K : ℕ} (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) : Set (Vector d) :=
  {β | ∀ i, ‖blockProjection (S i) β‖ ≤ Δ i}

/-- Worst-case risk over constant targets `θ` with `‖P_{S_i}(θ − θ₀)‖₂ ≤ Δ_i` for all `i`. -/
def blockWorstRisk {s : RandomSeed} {T d B K : ℕ} (θ₀ : Vector d)
    (S : Fin K → Finset (Fin d)) (Δ : Fin K → ℝ) (π : ReleasePolicy s T d B) : ℝ≥0∞ :=
  ⨆ θ : {θ : Vector d // θ - θ₀ ∈ blockBall S Δ}, policyRisk θ₀ π (fun _ => θ.val)

/-- Minimax risk over the block class: infimum over every seed space and every causal
budgeted policy (adaptive dates allowed), outside the supremum over the class. -/
def blockMinimaxRisk (T d B K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (Δ : Fin K → ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ (s : RandomSeed) (π : ReleasePolicy s T d B),
    IsCausal π ∧ v = blockWorstRisk θ₀ S Δ π}

/-- The deterministic grid of block-projected anchored averages on schedule `τ`: at a date
`1 ≤ n < T` release `θ₀ + Π_K(n⁻¹ ∑_{t ≤ n} X_t(Y_t − X_tᵀθ₀))` with `K` the product of
block balls; a release at date `0` keeps `θ₀` (a release at `T` serves no round). -/
def blockGridPolicy (T d B K : ℕ) (θ₀ : Vector d) (S : Fin K → Finset (Fin d))
    (Δ : Fin K → ℝ) (τ : Fin (B + 2) → ℕ) : ReleasePolicy unitSeed T d B where
  date := fun j _ => slotDate τ j
  head := fun j ω =>
    let n := slotDate τ j
    if n = 0 ∨ T ≤ n then θ₀ else
      θ₀ + convexProjection (blockBall S Δ)
        (anchoredAverage θ₀ (Finset.univ.filter (fun i : Fin T => i.val < n)) ω.2)

end TightReleaseSchedules.Stationary.Supplement


