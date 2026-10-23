-- Prove2me | Definitions.Def_PoolOrNot_Moderate_Fluid
-- name    : PoolOrNot_Moderate_Fluid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:36.814449+00:00
-- url     : https://prove2.me/theorems/2765dc0d-ef63-4d30-ac34-9ff964718c4e
-- title:
--   (11)–(16), p. 6, and §4.2, p. 7 — the fluid model of the DQ–JSQ system, the sets 𝕊 and 𝕊_N, and invariant states
-- statement:
--   The **fluid model** of the DQ–JSQ system with traffic intensity $\rho$, service rate $\mu$ and patience rate $\theta$.
--
--   1. **State sets.** $\mathbb S$ is the set of sequences $(x_i)_{i \ge 1}$ with $0 \le x_i \le 1$ and $x_{i+1} \le x_i$, and for $N \in \mathbb N$, $\mathbb S_N = \{x \in \mathbb S : x_i = 0 \text{ for } i \ge N\}$.
--
--   2. **Fluid solution.** A pair $(\bar Q, \bar U)$ of families of real functions on $[0, \infty)$, $\bar Q_i$ for $i \ge 1$ (the fraction of servers with at least $i$ customers) and $\bar U_i$ for $i \ge 0$ (the normalized cumulative number of arrivals that found every server with at least $i$ customers), is a fluid solution if for every $i \ge 1$ and $t \ge 0$
--   $$\bar Q_i(t) = \bar Q_i(0) + \bar U_{i-1}(t) - \bar U_i(t) - \bigl(\mu + \theta(i-1)\bigr)\int_0^t \bigl(\bar Q_i(u) - \bar Q_{i+1}(u)\bigr)\,du, \tag{11}$$
--   $\bar U_0(t) = \rho\mu t$ (12), $\bar U_i(0) = 0$ (13), $\int_0^\infty \mathbf 1\{\bar Q_i(t-) < 1\}\,d\bar U_i(t) = 0$ (14), $0 \le \bar Q_{i+1}(t) \le \bar Q_i(t) \le 1$ (15), and $0 \le \bar U_i'(t) \le \bar U_{i-1}'(t)$ (16).
--
--   3. **Invariant state.** $x$ is an invariant state if the constant path $\bar Q(t) \equiv x$ is (the queue-length part of) a fluid solution.
--
--   The fluid model is the deterministic approximation of $Q/n$ for many servers; its invariant state $q^*$ is the limit of the stationary laws (Theorem 3(ii)), from which the performance formulas of Theorems 4 and 5 are read off.
--
--   **Formalization Note** Indices are the paper's: `Q i` for $i \ge 1$ is $\bar Q_i$ and `U i` is $\bar U_i$; `Q 0` and all values at $t < 0$ are unconstrained. (11), (12), (13) and (15) are required for every $t \ge 0$ (not only almost every $t$), and (11) requires the integrand to be integrable on $[0, t]$, so that the integral is a genuine Lebesgue integral rather than Lean's default $0$. (16) is stated in integrated form, $0 \le \bar U_i(t) - \bar U_i(s) \le \bar U_{i-1}(t) - \bar U_{i-1}(s)$ for $0 \le s \le t$, which is its meaning for absolutely continuous $\bar U$ (by (12) this makes every $\bar U_i$ Lipschitz); the literal almost-everywhere-derivative reading would allow singular increments of $\bar U_i$. Given Lipschitz $\bar U_i$, (14) is stated as: for almost every $t > 0$ with $\bar Q_i(t) < 1$, $\bar U_i$ has derivative $0$ at $t$ ($\bar Q_i$ is then continuous, so $t-$ may be replaced by $t$).
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, pp. 6–7 (PDF 7–8), §4.1 (11)–(16), 𝕊 and 𝕊_N before (19), §4.2 (invariant state)

import Mathlib

open MeasureTheory

namespace PoolOrNot.Moderate

/-- `x ∈ 𝕊` (p. 7): `0 ≤ x_i ≤ 1` and `x_{i+1} ≤ x_i` for `i ∈ ℕ = {1, 2, …}` (paper indices;
the value `x 0` is not constrained). -/
def InS (x : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → 0 ≤ x i ∧ x i ≤ 1 ∧ x (i + 1) ≤ x i

/-- `x ∈ 𝕊_N` (p. 7): `x ∈ 𝕊` and `x_i = 0` for `i ≥ N`. -/
def InSN (N : ℕ) (x : ℕ → ℝ) : Prop :=
  InS x ∧ ∀ i : ℕ, N ≤ i → x i = 0

/-- `(Q̄, Ū)` is a fluid solution (§4.1, p. 6, (11)–(16)) with traffic intensity `ρ`, service rate
`μ` and patience rate `θ`. Paper indices: `Q i` for `i ≥ 1` is `Q̄_i`, `U i` for `i ≥ 0` is `Ū_i`;
`Q 0` and all values at `t < 0` are not paper objects and are unconstrained.
* (11) for every `t ≥ 0` and `i ≥ 1`, with the integrand integrable on `[0, t]`;
* (12) `Ū_0(t) = ρμt` for `t ≥ 0`; (13) `Ū_i(0) = 0` for `i ≥ 1`;
* (14) for almost every `t > 0` with `Q̄_i(t) < 1`, `Ū_i` has derivative `0` at `t`
  (the meaning of `∫_0^∞ 1{Q̄_i(t−) < 1} dŪ_i(t) = 0` for the Lipschitz `Ū_i` forced by (16));
* (15) `0 ≤ Q̄_{i+1}(t) ≤ Q̄_i(t) ≤ 1` for `t ≥ 0`, `i ≥ 1`;
* (16) in integrated form: `0 ≤ Ū_i(t) − Ū_i(s) ≤ Ū_{i−1}(t) − Ū_{i−1}(s)` for `0 ≤ s ≤ t`,
  `i ≥ 1` (the meaning of `0 ≤ Ū_i' ≤ Ū_{i−1}'` for absolutely continuous `Ū`). -/
def IsFluidSolution (ρ μ θ : ℝ) (Q U : ℕ → ℝ → ℝ) : Prop :=
  (∀ i : ℕ, 1 ≤ i → ∀ t : ℝ, 0 ≤ t →
      IntervalIntegrable (fun u => Q i u - Q (i + 1) u) volume 0 t ∧
      Q i t = Q i 0 + U (i - 1) t - U i t -
        (μ + θ * ((i : ℝ) - 1)) * ∫ u in (0 : ℝ)..t, (Q i u - Q (i + 1) u)) ∧
  (∀ t : ℝ, 0 ≤ t → U 0 t = ρ * μ * t) ∧
  (∀ i : ℕ, 1 ≤ i → U i 0 = 0) ∧
  (∀ i : ℕ, 1 ≤ i → ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), Q i t < 1 → HasDerivAt (U i) 0 t) ∧
  (∀ i : ℕ, 1 ≤ i → ∀ t : ℝ, 0 ≤ t → 0 ≤ Q (i + 1) t ∧ Q (i + 1) t ≤ Q i t ∧ Q i t ≤ 1) ∧
  (∀ i : ℕ, 1 ≤ i → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      0 ≤ U i t - U i s ∧ U i t - U i s ≤ U (i - 1) t - U (i - 1) s)

/-- `x` is an invariant state of the fluid model (§4.2, p. 7): the constant path `Q̄(t) = x`
is (the queue-length part of) a fluid solution. -/
def IsInvariantState (ρ μ θ : ℝ) (x : ℕ → ℝ) : Prop :=
  ∃ U : ℕ → ℝ → ℝ, IsFluidSolution ρ μ θ (fun i _ => x i) U

end PoolOrNot.Moderate


