-- Prove2me | Definitions.Def_CalendarDependentRM_Instance_IsFeasible12
-- name    : CalendarDependentRM_Instance_IsFeasible12
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:53.862852+00:00
-- url     : https://prove2.me/theorems/e39fc85f-a17c-4856-ac75-2220b7cf108f
-- title:
--   The set W and feasibility in the linear program (12)
-- statement:
--   The set $\mathcal W$ consists of the $w=(w^k_t(q))$ with
--
--   $$
--   w^k_t(q)=\theta^k_{t-1}(q)w^k_{t-1}(q)\ (t\ne1),\qquad w^k_1(q)=\sum_p(1-\theta^{k-1}_q(p))w^{k-1}_q(p)\ (k\ne1),\qquad w^1_1(q)=\mathbf 1(\hat D^0=q).
--   $$
--
--   A triple $(y,u,w)$ with $y,u\ge0$ and $w\in\mathcal W$ is **feasible for the linear program (12)**, the dual of (11), when $u^k_{jt}(q)\le\lambda^k_{jt}w^k_t(q)$ and
--
--   $$
--   y^k_{it}(q)+\sum_ja_{ij}u^k_{jt}(q)=\theta^k_{t-1}(q)y^k_{i,t-1}(q)\ (t\ne1),
--   $$
--
--   $$
--   y^k_{i1}(q)+\sum_ja_{ij}u^k_{j1}(q)=\sum_p(1-\theta^{k-1}_q(p))y^{k-1}_{iq}(p)\ (k\ne1),
--   $$
--
--   $$
--   y^1_{i1}(q)+\sum_ja_{ij}u^1_{j1}(q)=\mathbf 1(\hat D^0=q)c_i.
--   $$
--
--   The change of variables $u=P\{D^k\ge t,D^{k-1}=q\}\,x$ turns (12) into a relaxation of the same form as the fluid approximation (2), which is how the paper derives (2).
--
--   **Formalization Note** Periods and stages are 0-based, and the demand value $q$ of stage $k-1$ serves as the period index in the stage recursion.
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, §B, ER pp.5–6 (PDF 27–28), display (12)

import Mathlib
import Definitions.Def_CalendarDependentRM_Instance

open scoped Classical

namespace CalendarDependentRM

namespace DemandChain

variable {K T : ℕ} (C : DemandChain K T)

/-- **The set `𝒲`**, Li, Rusmevichientong & Topaloglu, *Revenue Management with Calendar-Aware and Dependent
Demands*, arXiv:2409.02637v2, Extended Results p. 5:
`w^k_t(q) = θ^k_{t−1}(q) w^k_{t−1}(q)` for `t ≠ 1`,
`w^k_1(q) = Σ_p (1 − θ^{k−1}_q(p)) w^{k−1}_q(p)` for `k ≠ 1`, and `w^1_1(q) = 1(D̂⁰ = q)`.

**Formalization Note** `w k t q` is `w^k_t(q)`, 0-based. In the stage recursion the demand value `q` of stage
`k − 1` serves as the period index of `θ` and `w`. -/
structure IsW (w : Fin K → Fin T → Fin T → ℝ) : Prop where
  period : ∀ (k : Fin K) (q : Fin T) (t : ℕ) (h : t + 1 < T),
    w k ⟨t + 1, h⟩ q = C.theta k t q * w k ⟨t, by omega⟩ q
  stage : ∀ (k : ℕ) (h : k + 1 < K) (q : Fin T),
    w ⟨k + 1, h⟩ ⟨0, q.pos⟩ q =
      ∑ p, (1 - C.theta ⟨k, by omega⟩ (q : ℕ) p) * w ⟨k, by omega⟩ q p
  init : ∀ (h : 0 < K) (q : Fin T), w ⟨0, h⟩ ⟨0, q.pos⟩ q = if C.D0 = q then 1 else 0

end DemandChain

namespace Instance

variable {R J : Type*} [Fintype J] {K T : ℕ} (I : Instance R J K T)

/-- **Feasibility in the linear program (12)**, the dual of problem (11), Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, display (12), Extended Results p. 6: `(y, u) ≥ 0`, `w ∈ 𝒲`,
`y^k_it(q) + Σ_j a_ij u^k_jt(q) = θ^k_{t−1}(q) y^k_{i,t−1}(q)` for `t ≠ 1`,
`y^k_i1(q) + Σ_j a_ij u^k_j1(q) = Σ_p (1 − θ^{k−1}_q(p)) y^{k−1}_iq(p)` for `k ≠ 1`,
`y^1_i1(q) + Σ_j a_ij u^1_j1(q) = 1(D̂⁰ = q) c_i`, and `u^k_jt(q) ≤ λ^k_jt w^k_t(q)`.

**Formalization Note** `y k i t q` is `y^k_it(q)` and `u k j t q` is `u^k_jt(q)`, 0-based. -/
structure IsFeasible12 (y : Fin K → R → Fin T → Fin T → ℝ) (u : Fin K → J → Fin T → Fin T → ℝ)
    (w : Fin K → Fin T → Fin T → ℝ) : Prop where
  y_nonneg : ∀ k i t q, 0 ≤ y k i t q
  u_nonneg : ∀ k j t q, 0 ≤ u k j t q
  mem_W : I.chain.IsW w
  period : ∀ (i : R) (k : Fin K) (q : Fin T) (t : ℕ) (h : t + 1 < T),
    y k i ⟨t + 1, h⟩ q + ∑ j, (I.a i j : ℝ) * u k j ⟨t + 1, h⟩ q =
      I.chain.theta k t q * y k i ⟨t, by omega⟩ q
  stage : ∀ (i : R) (k : ℕ) (h : k + 1 < K) (q : Fin T),
    y ⟨k + 1, h⟩ i ⟨0, q.pos⟩ q + ∑ j, (I.a i j : ℝ) * u ⟨k + 1, h⟩ j ⟨0, q.pos⟩ q =
      ∑ p, (1 - I.chain.theta ⟨k, by omega⟩ (q : ℕ) p) * y ⟨k, by omega⟩ i q p
  init : ∀ (i : R) (h : 0 < K) (q : Fin T),
    y ⟨0, h⟩ i ⟨0, q.pos⟩ q + ∑ j, (I.a i j : ℝ) * u ⟨0, h⟩ j ⟨0, q.pos⟩ q =
      (if I.chain.D0 = q then 1 else 0) * (I.c i : ℝ)
  u_le : ∀ k j t q, u k j t q ≤ I.lam k t j * w k t q

end Instance

end CalendarDependentRM


