-- Prove2me | Definitions.Def_MitigateSupplyRisk_Improvement_Model
-- name    : MitigateSupplyRisk_Improvement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:13.863472+00:00
-- url     : https://prove2.me/theorems/66914a05-265e-4cde-9406-c0457b9d2d93
-- title:
--   §3 and §4.2.1, pp. 492–493, 496 — one unreliable supplier: delivered quantity min{q, (K − ξ)⁺}, single-sourcing profit Π₂(q; a) and its optimal value Π₂*(a)
-- statement:
--   This file fixes the single-sourcing model of Wang, Gilland and Tomlin (2010) for one supplier.
--
--   **Data.** A firm sells one product over one season at unit revenue $r$, salvages leftover units at $v$ and pays a penalty $p$ per unit of unmet demand. It orders $q \ge 0$ units from a supplier with unit cost $c$, committed cost $\eta \in [0,1]$ and design capacity $K > 0$. The supplier suffers a random capacity loss $\xi \ge 0$, so that its effective capacity is $(K-\xi)^+$ and it delivers
--   $$y = \min\{q,\ (K-\xi)^+\}.$$
--   The firm pays $(\eta q + (1-\eta) y)\,c$ for the order. The law of $\xi$ depends on the supplier's **reliability index** $a \in \mathbb R$; its distribution function is $G(\cdot, a)$. Demand $X$ is independent of $\xi$ and has distribution function $F$.
--
--   **Standing assumptions** (§3, pp. 492–493), collected as `Model.Assumptions`:
--   1. $0 \le \eta \le 1$, $K > 0$ and $v < r + p$;
--   2. $X$ is a nonnegative random variable with finite mean;
--   3. for every $a$, $\xi$ is nonnegative and its distribution is continuous (no atoms);
--   4. an increase of the reliability index makes the loss stochastically smaller: $a \le a'$ implies $G(t, a) \le G(t, a')$ for all $t$.
--
--   **Profit.** With $\psi = -\eta c/(r+p-v)$ and $\varphi = (r+p-(1-\eta)c)/(r+p-v)$, the second-stage expected profit at index $a$ is
--   $$\Pi_2(q; a) = (r+p-v)\Big(\psi q + \varphi\, \mathsf E_{\xi(a)}[y] - \mathsf E_{\xi(a),X}\big[(y-X)^+\big]\Big) - p\,\mathsf E_X[X],$$
--   the expectation of the realized profit $-(\eta q + (1-\eta)y)c + r\min\{X, y\} + v(y-X)^+ - p(X-y)^+$ of Eq. (1). The optimal second-stage profit is
--   $$\Pi_2^*(a) = \sup_{q \ge 0} \Pi_2(q; a).$$
--
--   These objects are the second stage of the paper's two-stage improvement model; every theorem of this mission is about them.
--
--   **Formalization Note** The demand law $\mu$ and the loss laws $\nu(a)$ are measures on $\mathbb R$; $F$ and $G(\cdot, a)$ are their `ProbabilityTheory.cdf`, and $\mathsf E_{\xi(a),X}$ integrates over the product measure $\nu(a) \otimes \mu$ (independence). The paper also gives demand a density; no statement here needs it, so it is not assumed. The hypothesis $v < r+p$ is implicit in the paper's division by $r+p-v$. All integrands are integrable under the assumptions ($0 \le y \le \max(q,0)$, $(y-X)^+ \le \max(q,0)$ for $X \ge 0$, $\mathsf E|X| < \infty$). $\Pi_2^*$ is a real `sSup`; the set is nonempty, and it is bounded above when $\eta = 0$ (then $\Pi_2(q;a) = \Pi_2(K;a)$ for $q \ge K$) or when $c \ge 0$ (then $\psi \le 0$). Every theorem about $\Pi_2^*$ assumes one of the two.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), pp. 492–493 (PDF 4–5), §3.1–3.3, Eqs. (1)–(3); p. 496 (PDF 8), §4.2.1, single-sourcing Π₂

import Mathlib

open MeasureTheory ProbabilityTheory Set

namespace MitigateSupplyRisk.Improvement

/-- Data of the single-sourcing model of Wang, Gilland and Tomlin (2010), §3 and §4.2.1
(pp. 492–493, 496): unit revenue `r`, salvage value `v`, penalty cost `p`; the chosen supplier's
unit cost `c`, committed cost `η` and design capacity `K`; the demand law `μ` (distribution `F`);
and the family `ν a` of capacity-loss laws indexed by the reliability index `a`
(distribution `G(·, a)`). -/
structure Model where
  r : ℝ
  v : ℝ
  p : ℝ
  c : ℝ
  η : ℝ
  K : ℝ
  μ : Measure ℝ
  ν : ℝ → Measure ℝ

namespace Model

variable (M : Model)

/-- The standing assumptions of §3 (pp. 492–493) for one supplier.
* `0 ≤ η ≤ 1` and `0 < K`;
* `v < r + p`, so that the divisions by `r + p − v` in `ψ` and `φ` (Eq. (2)) are legitimate;
* demand `X ~ μ` is a nonnegative random variable with finite mean (`E[X]` appears in (3));
* for every index `a`, the capacity loss `ξ ~ ν a` is nonnegative with a continuous distribution;
* an increase of the index makes the loss stochastically smaller:
  `a ≤ a' → G(·, a) ≤ G(·, a')`. -/
structure Assumptions : Prop where
  η_nonneg : 0 ≤ M.η
  η_le_one : M.η ≤ 1
  K_pos : 0 < M.K
  v_lt : M.v < M.r + M.p
  μ_prob : IsProbabilityMeasure M.μ
  μ_nonneg : M.μ (Iio 0) = 0
  μ_integrable : Integrable id M.μ
  ν_prob : ∀ a, IsProbabilityMeasure (M.ν a)
  ν_nonneg : ∀ a, M.ν a (Iio 0) = 0
  ν_noAtoms : ∀ a, NullSingletonClass (M.ν a)
  stochOrder : ∀ a a' : ℝ, a ≤ a' → ∀ t : ℝ, cdf (M.ν a) t ≤ cdf (M.ν a') t

/-- Demand distribution `F(t) = P(X ≤ t)`. -/
noncomputable def F (t : ℝ) : ℝ := cdf M.μ t

/-- Capacity-loss distribution `G(ξ, a) = P(ξ_a ≤ ξ)` at reliability index `a`. -/
noncomputable def G (ξ a : ℝ) : ℝ := cdf (M.ν a) ξ

/-- `ψ = −η c / (r + p − v)` (p. 493). -/
noncomputable def ψ : ℝ := -(M.η * M.c) / (M.r + M.p - M.v)

/-- `φ = (r + p − (1 − η) c) / (r + p − v)` (p. 493). -/
noncomputable def φ : ℝ := (M.r + M.p - (1 - M.η) * M.c) / (M.r + M.p - M.v)

/-- Delivered quantity `y = min{q, (K − ξ)⁺}` for order `q` and realized loss `ξ` (p. 492). -/
noncomputable def y (q ξ : ℝ) : ℝ := min q (max (M.K - ξ) 0)

/-- Single-sourcing second-stage expected profit (p. 496):
`Π₂(q; a) = (r+p−v)(ψ q + φ E_{ξ(a)}[y] − E_{ξ(a),X}[(y − X)⁺]) − p E[X]`,
with `ξ ~ ν a` and `X ~ μ` independent. All integrands are integrable under `Assumptions`
(`0 ≤ y ≤ max q 0`, `(y − X)⁺ ≤ max q 0` for `X ≥ 0`, and `E|X| < ∞`). -/
noncomputable def Pi2 (q a : ℝ) : ℝ :=
  (M.r + M.p - M.v) *
      (M.ψ * q + M.φ * ∫ ξ, M.y q ξ ∂(M.ν a)
        - ∫ ω, max (M.y q ω.1 - ω.2) 0 ∂((M.ν a).prod M.μ))
    - M.p * ∫ x, x ∂M.μ

/-- Optimal second-stage profit `Π₂*(a) = sup_{q ≥ 0} Π₂(q; a)`. The set is nonempty; it is bounded
above when `η = 0` (then `Π₂(q; a) = Π₂(K; a)` for `q ≥ K`) or when `c ≥ 0`
(then `ψ ≤ 0`); results about `Π₂*` carry one of these. -/
noncomputable def Pi2star (a : ℝ) : ℝ := sSup ((fun q => M.Pi2 q a) '' Ici 0)

end Model

end MitigateSupplyRisk.Improvement


