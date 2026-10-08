-- Prove2me | Definitions.Def_MitigateSupplyRisk_Heterogeneity_Model
-- name    : MitigateSupplyRisk_Heterogeneity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:01.735831+00:00
-- url     : https://prove2.me/theorems/963c3372-0170-4329-8d86-ec05a6fe3522
-- title:
--   §3, Eqs. (1), (3), (5), (7), §5.1 — two unreliable suppliers with random capacity; optimal dual-sourcing value Π*_DS, single-sourcing-with-improvement value Π*_SSI, heterogeneity parameters Δ_c, Δ_η
-- statement:
--   A firm sells one product over one season and can source from two suppliers $i = 1, 2$. The data are: unit revenue $r$, salvage value $v$, penalty cost $p$ for unfilled demand; for each supplier a unit cost $c_i$, a **committed-cost fraction** $\eta_i \in [0,1]$ and a design capacity $K_i > 0$; the law of the demand $X \ge 0$; and, for each supplier and each value $a$ of its **reliability index**, the law $G_i(\cdot, a)$ of its realized capacity loss $\xi_i \ge 0$.
--
--   If the firm orders $q_i \ge 0$ from supplier $i$, it receives
--   $$y_i = \min\{q_i, (K_i - \xi_i)^+\},$$
--   pays $(\eta_i q_i + (1-\eta_i) y_i)\, c_i$ to that supplier, and for realized demand $x$ earns the profit (Eq. (1))
--   $$\pi(q) = -\sum_i (\eta_i q_i + (1-\eta_i) y_i)\, c_i + r \min\Big\{x, \sum_i y_i\Big\} + v \Big(\sum_i y_i - x\Big)^+ - p \Big(x - \sum_i y_i\Big)^+ .$$
--   With independent capacity losses $\xi_i \sim G_i(\cdot, a_i)$, independent of $X$, the **second-stage expected profit** is $\Pi_2(q; a) = \mathbb E[\pi(q)]$ (Eq. (3)) and the optimal second-stage profit is $\Pi_2^*(a) = \sup_{q \ge 0} \Pi_2(q; a)$.
--
--   1. **Dual sourcing (DS)** orders from both suppliers at their initial indices $a^0 = (a_1^0, a_2^0)$; its optimal profit is $\Pi^*_{DS} = \Pi_2^*(a_1^0, a_2^0)$.
--   2. **Single sourcing** from supplier $i$ alone has second-stage profit $\Pi_2(q_i; a_i)$ (the case $q_j = 0$) and optimal value $\Pi_2^*(a_i) = \sup_{q_i \ge 0} \Pi_2(q_i; a_i)$. Effort $z_i(a)$ raises the index to $a \ge a_i^0$ at cost $m_i z_i(a)$; it succeeds with probability $\theta_i$, otherwise the index stays $a_i^0$. Under early commitment the first-stage profit is (Eq. (7))
--   $$\Pi_1(a_i) = -m_i z_i(a_i) + \theta_i \Pi_2^*(a_i) + (1-\theta_i)\Pi_2^*(a_i^0),$$
--   and **single sourcing with improvement (SSI)** has optimal profit $\Pi^*_{SSI} = \max_{i} \sup_{a \ge a_i^0} \Pi_1(a)$.
--   3. The **combined strategy** improves one or both suppliers and then dual sources; its first-stage profit (Eq. (5)) is
--   $$\Pi_1(a) = \sum_i -m_i z_i(a_i) + \theta_1\theta_2 \Pi_2^*(a_1,a_2) + \theta_1(1-\theta_2)\Pi_2^*(a_1,a_2^0) + (1-\theta_1)\theta_2\Pi_2^*(a_1^0,a_2) + (1-\theta_1)(1-\theta_2)\Pi_2^*(a_1^0,a_2^0).$$
--   4. **Heterogeneity.** When the two suppliers share every attribute, a common cost $c$ is split as $c_1 = c - \Delta_c$, $c_2 = c + \Delta_c$ (the **cost heterogeneity parameter** $\Delta_c$), and a common committed cost as $\eta_1 = \eta - \Delta_\eta$, $\eta_2 = \eta + \Delta_\eta$.
--
--   The **standing assumptions** of the model are: $0 \le \eta_i \le 1$; $K_i > 0$; the demand is a probability law on $[0, \infty)$ with finite mean; each $G_i(\cdot, a)$ is a continuous distribution on $[0, \infty)$; a larger index means a stochastically smaller loss, $a \le a' \Rightarrow G_i(t, a) \le G_i(t, a')$ for all $t$; $\theta_i \in [0,1]$; $m_i \ge 0$; $z_i$ is convex and nondecreasing on $[a_i^0, \infty)$ with $z_i(a_i^0) = 0$; and $v < r + p$, $r \ge 0$, $p \ge 0$, $c_i \ge 0$.
--
--   These objects are shared by every statement of the mission, which compares the two strategies as the suppliers become more heterogeneous.
--
--   **Formalization Note** Suppliers are indexed by `Fin 2` (index `0` is supplier 1). $G_i(\cdot, a)$ is the cumulative distribution function of a measure `ν i a`, so the expectations in (3) are Bochner integrals against the product of the two loss laws and the demand law; under the standing assumptions the integrand is bounded by a constant times $1 + |x|$, so these integrals are genuine. Optimal values are real suprema (`sSup`) over $q \ge 0$ and $a \ge a_i^0$; under the standing assumptions each set is nonempty and bounded above by $(r + |v|)(K_1 + K_2)$, so no supremum takes a default value. The effort function $z_i$ of the index (the paper's reframing on p. 493) is taken as the primitive, which presumes $a_i(\cdot)$ unbounded so that every $a \ge a_i^0$ is reachable. The sign conditions $r, p, c_i \ge 0$ and $v < r + p$ are readings of the paper's revenue, penalty and cost (the latter is implicit in its Eq. (2)), stated as the fields of `Model.Standing` and `SymData.Standing`. `SymData` holds the common data of two identical suppliers; `costModel Δ` and `etaModel Δ` introduce heterogeneity in exactly one attribute.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), pp. 492–493 (PDF 4–5), §3, Eqs. (1), (3), (5); p. 494 (PDF 6), §4.1; p. 496 (PDF 8), §4.2.1, Eq. (7); p. 500 (PDF 12), §5 (definition of Π*_SSI, Π*_DS); p. 501 (PDF 13), §5.1 (Δ_c, Δ_η)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_LateCommit_Model

open MeasureTheory ProbabilityTheory

namespace MitigateSupplyRisk.Heterogeneity

/-- Data of the two-supplier model of §3 (pp. 492–493). Suppliers are indexed by `Fin 2`
(`0` is the paper's supplier 1, `1` its supplier 2).
* `r`, `v`, `p`: unit revenue, salvage value, penalty cost for unfilled demand;
* `c i`, `η i`, `K i`: unit cost, committed-cost fraction, design capacity of supplier `i`;
* `ν i a`: law of supplier `i`'s capacity loss `ξ_i` when its reliability index is `a`
  (so `G_i(t, a) = cdf (ν i a) t`);
* `μ`: law of the demand `X`;
* `a0 i`: initial reliability index; `θ i`: success probability of improvement;
* `m i`: unit effort cost; `z i a`: effort needed to raise supplier `i`'s index to `a`.
No assumption is bundled here; the standing assumptions are `Model.Standing` (general suppliers)
and `SymData.Standing` (identical suppliers). -/
structure Model where
  r : ℝ
  v : ℝ
  p : ℝ
  c : Fin 2 → ℝ
  η : Fin 2 → ℝ
  K : Fin 2 → ℝ
  ν : Fin 2 → ℝ → Measure ℝ
  μ : Measure ℝ
  a0 : Fin 2 → ℝ
  θ : Fin 2 → ℝ
  m : Fin 2 → ℝ
  z : Fin 2 → ℝ → ℝ

namespace Model

variable (M : Model)

/-- Realized dual-sourcing profit, Eq. (1) (p. 493), for orders `q`, capacity losses `ξ` and
realized demand `x`:
`π(q) = −Σ_i (η_i q_i + (1 − η_i) y_i) c_i + r min{x, Σ_i y_i} + v (Σ_i y_i − x)⁺ − p (x − Σ_i y_i)⁺`. -/
noncomputable def profit (q ξ : Fin 2 → ℝ) (x : ℝ) : ℝ :=
  -(∑ i, (M.η i * q i + (1 - M.η i) * MitigateSupplyRisk.LateCommit.delivered (M.K i) (q i) (ξ i)) * M.c i)
    + M.r * min x (∑ i, MitigateSupplyRisk.LateCommit.delivered (M.K i) (q i) (ξ i))
    + M.v * max ((∑ i, MitigateSupplyRisk.LateCommit.delivered (M.K i) (q i) (ξ i)) - x) 0
    - M.p * max (x - ∑ i, MitigateSupplyRisk.LateCommit.delivered (M.K i) (q i) (ξ i)) 0

/-- Second-stage expected dual-sourcing profit `Π₂(q; a) = E_{ξ(a), X}[π(q)]`, Eq. (3) (p. 493):
the capacity losses are independent with laws `ν 0 (a 0)`, `ν 1 (a 1)`, independent of the demand. -/
noncomputable def Pi2 (q a : Fin 2 → ℝ) : ℝ :=
  ∫ ω, M.profit q ![ω.1.1, ω.1.2] ω.2 ∂(((M.ν 0 (a 0)).prod (M.ν 1 (a 1))).prod M.μ)

/-- Optimal second-stage profit `Π₂*(a) = max_{q ≥ 0} Π₂(q; a)` (p. 493), as a supremum over
nonnegative order vectors. -/
noncomputable def Pi2star (a : Fin 2 → ℝ) : ℝ :=
  sSup ((fun q => M.Pi2 q a) '' {q : Fin 2 → ℝ | ∀ i, 0 ≤ q i})

/-- Optimal expected profit of dual sourcing without improvement,
`Π*_DS = Π₂*(a₁⁰, a₂⁰)` (§4.1, p. 494; §5, p. 500). -/
noncomputable def PiDS : ℝ := M.Pi2star M.a0

/-- Realized single-sourcing profit when only supplier `i` is used (Eq. (1) with `q_j = 0`). -/
noncomputable def profitSingle (i : Fin 2) (q ξ x : ℝ) : ℝ :=
  -((M.η i * q + (1 - M.η i) * MitigateSupplyRisk.LateCommit.delivered (M.K i) q ξ) * M.c i)
    + M.r * min x (MitigateSupplyRisk.LateCommit.delivered (M.K i) q ξ)
    + M.v * max (MitigateSupplyRisk.LateCommit.delivered (M.K i) q ξ - x) 0
    - M.p * max (x - MitigateSupplyRisk.LateCommit.delivered (M.K i) q ξ) 0

/-- Single-sourcing second-stage expected profit `Π₂(q_i; a_i)` of §4.2.1 (p. 496). -/
noncomputable def Pi2single (i : Fin 2) (q a : ℝ) : ℝ :=
  ∫ ω, M.profitSingle i q ω.1 ω.2 ∂((M.ν i a).prod M.μ)

/-- `Π₂*(a_i) = max_{q_i ≥ 0} Π₂(q_i; a_i)` (p. 496). -/
noncomputable def Pi2singleStar (i : Fin 2) (a : ℝ) : ℝ :=
  sSup ((fun q => M.Pi2single i q a) '' Set.Ici 0)

/-- Early-commitment single-sourcing-with-improvement profit, Eq. (7) (p. 496):
`Π₁(a_i) = −m_i z_i(a_i) + θ_i Π₂*(a_i) + (1 − θ_i) Π₂*(a_i⁰)`. -/
noncomputable def Pi1single (i : Fin 2) (a : ℝ) : ℝ :=
  -(M.m i * M.z i a) + M.θ i * M.Pi2singleStar i a + (1 - M.θ i) * M.Pi2singleStar i (M.a0 i)

/-- Optimal SSI profit when supplier `i` is the chosen single source: `sup_{a ≥ a_i⁰} Π₁(a)`. -/
noncomputable def PiSSIof (i : Fin 2) : ℝ :=
  sSup (M.Pi1single i '' Set.Ici (M.a0 i))

/-- Optimal expected profit of single sourcing with improvement under early commitment,
`Π*_SSI` (§5, p. 500): the better of the two possible single sources. -/
noncomputable def PiSSI : ℝ := max (M.PiSSIof 0) (M.PiSSIof 1)

/-- First-stage expected profit of the combined strategy (dual sourcing with improvement of one or both
suppliers), Eq. (5) (p. 493), as a function of the target reliability indices `a = (a₁, a₂)`:
`Π₁(a) = Σ_i −m_i z_i(a_i) + θ₁θ₂ Π₂*(a₁, a₂) + θ₁(1 − θ₂) Π₂*(a₁, a₂⁰)
  + (1 − θ₁)θ₂ Π₂*(a₁⁰, a₂) + (1 − θ₁)(1 − θ₂) Π₂*(a₁⁰, a₂⁰)`. -/
noncomputable def Pi1 (a : Fin 2 → ℝ) : ℝ :=
  (∑ i, -(M.m i * M.z i (a i)))
    + M.θ 0 * M.θ 1 * M.Pi2star a
    + M.θ 0 * (1 - M.θ 1) * M.Pi2star ![a 0, M.a0 1]
    + (1 - M.θ 0) * M.θ 1 * M.Pi2star ![M.a0 0, a 1]
    + (1 - M.θ 0) * (1 - M.θ 1) * M.Pi2star M.a0

/-- Standing assumptions of §3 (pp. 492–493) on a two-supplier model, plus the sign conditions
`0 ≤ r`, `0 ≤ p`, `0 ≤ c_i` under which the optimal values are finite suprema (disclosed readings). -/
structure Standing : Prop where
  r_nonneg : 0 ≤ M.r
  p_nonneg : 0 ≤ M.p
  v_lt : M.v < M.r + M.p
  c_nonneg : ∀ i, 0 ≤ M.c i
  η_mem : ∀ i, M.η i ∈ Set.Icc (0 : ℝ) 1
  K_pos : ∀ i, 0 < M.K i
  μ_prob : IsProbabilityMeasure M.μ
  μ_nonneg : M.μ (Set.Iio 0) = 0
  μ_integrable : Integrable id M.μ
  ν_prob : ∀ i a, IsProbabilityMeasure (M.ν i a)
  ν_nonneg : ∀ i a, M.ν i a (Set.Iio 0) = 0
  ν_continuous : ∀ i a t, M.ν i a {t} = 0
  ν_mono : ∀ i a a', a ≤ a' → ∀ t, cdf (M.ν i a) t ≤ cdf (M.ν i a') t
  θ_mem : ∀ i, M.θ i ∈ Set.Icc (0 : ℝ) 1
  m_nonneg : ∀ i, 0 ≤ M.m i
  z_convex : ∀ i, ConvexOn ℝ (Set.Ici (M.a0 i)) (M.z i)
  z_mono : ∀ i, MonotoneOn (M.z i) (Set.Ici (M.a0 i))
  z_zero : ∀ i, M.z i (M.a0 i) = 0

end Model

/-- Common data of two suppliers that are identical in every attribute (§5.1, p. 501);
heterogeneity is then introduced in one attribute by `costModel` or `etaModel`. -/
structure SymData where
  r : ℝ
  v : ℝ
  p : ℝ
  c : ℝ
  η : ℝ
  K : ℝ
  ν : ℝ → Measure ℝ
  μ : Measure ℝ
  a0 : ℝ
  θ : ℝ
  m : ℝ
  z : ℝ → ℝ

namespace SymData

variable (S : SymData)

/-- The two-supplier model in which the suppliers are identical except in unit cost:
`c₁ = c − Δ_c`, `c₂ = c + Δ_c` (cost heterogeneity parameter `Δ_c`, p. 501). -/
noncomputable def costModel (Δ : ℝ) : Model where
  r := S.r
  v := S.v
  p := S.p
  c := ![S.c - Δ, S.c + Δ]
  η := fun _ => S.η
  K := fun _ => S.K
  ν := fun _ => S.ν
  μ := S.μ
  a0 := fun _ => S.a0
  θ := fun _ => S.θ
  m := fun _ => S.m
  z := fun _ => S.z

/-- The two-supplier model in which the suppliers are identical except in committed cost:
`η₁ = η − Δ_η`, `η₂ = η + Δ_η` (committed-cost heterogeneity parameter `Δ_η`, p. 501). -/
noncomputable def etaModel (Δ : ℝ) : Model where
  r := S.r
  v := S.v
  p := S.p
  c := fun _ => S.c
  η := ![S.η - Δ, S.η + Δ]
  K := fun _ => S.K
  ν := fun _ => S.ν
  μ := S.μ
  a0 := fun _ => S.a0
  θ := fun _ => S.θ
  m := fun _ => S.m
  z := fun _ => S.z

/-- Standing assumptions of §3 (pp. 492–493) on the common data, plus the sign conditions
`0 ≤ r`, `0 ≤ p`, `0 < c` under which the optimal values are finite suprema (disclosed readings). -/
structure Standing : Prop where
  r_nonneg : 0 ≤ S.r
  p_nonneg : 0 ≤ S.p
  v_lt : S.v < S.r + S.p
  c_pos : 0 < S.c
  η_mem : S.η ∈ Set.Icc (0 : ℝ) 1
  K_pos : 0 < S.K
  μ_prob : IsProbabilityMeasure S.μ
  μ_nonneg : S.μ (Set.Iio 0) = 0
  μ_integrable : Integrable id S.μ
  ν_prob : ∀ a, IsProbabilityMeasure (S.ν a)
  ν_nonneg : ∀ a, S.ν a (Set.Iio 0) = 0
  ν_continuous : ∀ a t, S.ν a {t} = 0
  ν_mono : ∀ a a', a ≤ a' → ∀ t, cdf (S.ν a) t ≤ cdf (S.ν a') t
  θ_mem : S.θ ∈ Set.Icc (0 : ℝ) 1
  m_nonneg : 0 ≤ S.m
  z_convex : ConvexOn ℝ (Set.Ici S.a0) S.z
  z_mono : MonotoneOn S.z (Set.Ici S.a0)
  z_zero : S.z S.a0 = 0

end SymData

end MitigateSupplyRisk.Heterogeneity


