-- Prove2me | Definitions.Def_MitigateSupplyRisk_DualSourcing_Model
-- name    : MitigateSupplyRisk_DualSourcing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:11.999633+00:00
-- url     : https://prove2.me/theorems/e0e7de06-f346-4eda-aeda-cf6d0f94d0ef
-- title:
--   §3.1–3.3, Eqs. (1)–(3) — two unreliable suppliers: delivered quantity min{q_i, (K_i − ξ_i)⁺}, realized profit π(q), second-stage expected profit Π₂(q; a), optimal value Π₂*(a)
-- statement:
--   This file sets up the single-season, two-supplier newsvendor with random supplier capacity of Wang, Gilland and Tomlin (2010), without process improvement.
--
--   **Data.** A product sells at unit revenue $r$, leftover units are salvaged at $v$, and unmet demand costs a penalty $p$ per unit. The firm can order from two suppliers $i = 1, 2$. Supplier $i$ has unit cost $c_i$, committed-cost fraction $\eta_i \in [0,1]$ and design capacity $K_i > 0$. Its realized capacity loss $\xi_i \ge 0$ has law $\nu_i(a)$ when its reliability index is $a$, with distribution function $G_i(t, a) = \mathbb P(\xi_i \le t)$. The laws are continuous (no atoms), and a larger index means a stochastically smaller loss:
--   $$a \le \hat a \implies G_i(t, a) \le G_i(t, \hat a) \quad \text{for all } t.$$
--
--   **Delivery and profit.** For an order vector $q = (q_1, q_2)$, supplier $i$ delivers $y_i = \min\{q_i, (K_i - \xi_i)^+\}$. With realized demand $x$, the realized profit (Eq. (1)) is
--   $$\pi(q) = -\sum_i (\eta_i q_i + (1-\eta_i) y_i) c_i + r \min\Big\{x, \sum_i y_i\Big\} + v \Big(\sum_i y_i - x\Big)^+ - p \Big(x - \sum_i y_i\Big)^+.$$
--   The firm pays $\eta_i c_i$ per unit ordered and $(1-\eta_i) c_i$ per unit delivered. The abbreviations of Eq. (2) are
--   $$\psi_i = -\frac{\eta_i c_i}{r+p-v}, \qquad \phi_i = \frac{r + p - (1-\eta_i) c_i}{r+p-v}.$$
--
--   **Expected profit.** For reliability indices $a = (a_1, a_2)$ and a demand law $\mu$, the second-stage expected profit is
--   $$\Pi_2(q; a) = \mathbb E_{\xi(a), X}[\pi(q)],$$
--   where $\xi_1, \xi_2, X$ are independent with laws $\nu_1(a_1), \nu_2(a_2), \mu$; this equals the compact form (3). The optimal second-stage profit is $\Pi_2^*(a) = \sup_{q \ge 0} \Pi_2(q; a)$, and $q$ is *optimal* when $q \ge 0$ and $\Pi_2(q'; a) \le \Pi_2(q; a)$ for every $q' \ge 0$.
--
--   These objects are shared by every statement of the mission: the random-demand results (Lemma 1, Theorem 1, Eq. (6), Lemma 2) and the deterministic-demand results (Theorem 2, Corollary 1, with $\mu$ a point mass).
--
--   **Formalization Note.** Suppliers are indexed by `Fin 2`: index `0` is the paper's supplier 1, index `1` its supplier 2. The demand law $\mu$ is a parameter of $\Pi_2$, not part of the model. Added standing hypotheses, all disclosed: $K_i > 0$; $v < r + p$ (the denominator of $\psi_i, \phi_i$); and $r, p, c_i \ge 0$, so that $\pi \le (r + |v|)(K_1 + K_2)$ for nonnegative demand and $\Pi_2^*$ is a genuine supremum of a set bounded above (it is nonempty since $q = 0$ is feasible). $\Pi_2$ is a Bochner integral over the product law; for a demand law with finite mean the integrand is integrable ($|\pi| \le C_q(1 + |x|)$), and every theorem of the mission assumes that.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), pp. 492–493 (PDF pp. 4–5), §3.1–3.3, Eqs. (1)–(3)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MitigateSupplyRisk.DualSourcing

/-- The two-supplier random-capacity newsvendor of Wang, Gilland and Tomlin (2010), §3.1–3.2,
without process improvement. Suppliers are indexed by `Fin 2`: index `0` is the paper's supplier 1
and index `1` is its supplier 2.

* `r`, `v`, `p`: unit revenue, salvage value and penalty cost for unfilled demand.
* `c i`, `η i`, `K i`: unit cost, committed-cost fraction and design capacity of supplier `i`.
* `ν i a`: the law of supplier `i`'s capacity loss `ξ_i` when its reliability index is `a`.

Standing assumptions of §3: `0 ≤ η i ≤ 1`; capacity losses are nonnegative and continuously
distributed; a larger reliability index makes the capacity-loss CDF pointwise larger
(`G_i(·, a) ≤ G_i(·, â)` for `a ≤ â`). Added and disclosed: `0 < K i`, `v < r + p` (the
denominator of `ψ`, `φ` in Eq. (2)), and `r, p, c i ≥ 0` (revenue, penalty and cost are
nonnegative amounts), which keep the profit bounded above in the order quantities. -/
structure Model where
  r : ℝ
  v : ℝ
  p : ℝ
  c : Fin 2 → ℝ
  η : Fin 2 → ℝ
  K : Fin 2 → ℝ
  ν : Fin 2 → ℝ → Measure ℝ
  ν_prob : ∀ i a, IsProbabilityMeasure (ν i a)
  ν_nonneg : ∀ i a, ν i a (Set.Iio 0) = 0
  ν_noAtoms : ∀ i a t, ν i a {t} = 0
  ν_mono : ∀ i a a', a ≤ a' → ∀ t, cdf (ν i a) t ≤ cdf (ν i a') t
  η_nonneg : ∀ i, 0 ≤ η i
  η_le_one : ∀ i, η i ≤ 1
  K_pos : ∀ i, 0 < K i
  r_nonneg : 0 ≤ r
  p_nonneg : 0 ≤ p
  c_nonneg : ∀ i, 0 ≤ c i
  v_lt : v < r + p

namespace Model

instance (M : Model) (i : Fin 2) (a : ℝ) : IsProbabilityMeasure (M.ν i a) := M.ν_prob i a

/-- `G_i(t, a)`: the distribution function of supplier `i`'s capacity loss at reliability index `a`. -/
noncomputable def G (M : Model) (i : Fin 2) (t a : ℝ) : ℝ := cdf (M.ν i a) t

/-- `ψ_i = −η_i c_i / (r + p − v)` (§3.3, before Eq. (2)). -/
noncomputable def psi (M : Model) (i : Fin 2) : ℝ := -(M.η i * M.c i) / (M.r + M.p - M.v)

/-- `φ_i = (r + p − (1 − η_i) c_i) / (r + p − v)` (§3.3, before Eq. (2)). -/
noncomputable def phi (M : Model) (i : Fin 2) : ℝ :=
  (M.r + M.p - (1 - M.η i) * M.c i) / (M.r + M.p - M.v)

/-- Delivered quantity `y_i = min{q_i, (K_i − ξ_i)⁺}` (§3.2). -/
def deliv (K q ξ : ℝ) : ℝ := min q (max (K - ξ) 0)

/-- Realized profit `π(q)` of Eq. (1), for order vector `q`, capacity losses `ξ` and realized
demand `x`. -/
noncomputable def profit (M : Model) (q ξ : Fin 2 → ℝ) (x : ℝ) : ℝ :=
  -(∑ i, (M.η i * q i + (1 - M.η i) * deliv (M.K i) (q i) (ξ i)) * M.c i)
    + M.r * min x (∑ i, deliv (M.K i) (q i) (ξ i))
    + M.v * max ((∑ i, deliv (M.K i) (q i) (ξ i)) - x) 0
    - M.p * max (x - ∑ i, deliv (M.K i) (q i) (ξ i)) 0

/-- Second-stage expected profit `Π₂(q; a) = E_{ξ(a), X}[π(q)]` (Eq. (3)), with the capacity
losses independent with laws `ν i (a i)` and independent of the demand `X ~ μ`. For a demand law
with finite mean the integrand is integrable for every `q` (`|π| ≤ C_q (1 + |x|)`), so the
Bochner integral is the genuine expectation. -/
noncomputable def Pi2 (M : Model) (μ : Measure ℝ) (q a : Fin 2 → ℝ) : ℝ :=
  ∫ ω, M.profit q ω.1 ω.2 ∂((Measure.pi fun i => M.ν i (a i)).prod μ)

/-- The feasible order vectors `q ≥ 0`. -/
def orders : Set (Fin 2 → ℝ) := {q | ∀ i, 0 ≤ q i}

/-- Optimal second-stage profit `Π₂*(a) = max_{q ≥ 0} Π₂(q; a)` (§3.3). The image is nonempty and,
since `r, p, c i ≥ 0`, `y_i ≤ K_i` and demand is nonnegative, bounded above by
`(r + |v|)(K₁ + K₂)`; so the supremum is not a junk value. -/
noncomputable def Pi2star (M : Model) (μ : Measure ℝ) (a : Fin 2 → ℝ) : ℝ :=
  sSup ((fun q => M.Pi2 μ q a) '' orders)

/-- `q` is an optimal procurement vector at reliability indices `a` and demand law `μ`: it is
feasible (`q ≥ 0`) and maximizes `Π₂(·; a)` over all feasible order vectors. -/
def IsOptimal (M : Model) (μ : Measure ℝ) (a q : Fin 2 → ℝ) : Prop :=
  q ∈ orders ∧ ∀ q' ∈ orders, M.Pi2 μ q' a ≤ M.Pi2 μ q a

end Model

end MitigateSupplyRisk.DualSourcing


