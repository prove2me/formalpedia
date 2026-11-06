-- Prove2me | Definitions.Def_FlexibleNRM_IsCalibration
-- name    : FlexibleNRM_IsCalibration
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:25:05.140562+00:00
-- url     : https://prove2.me/theorems/3dba57fe-8fb0-4507-9fb4-759f75ff8de4
-- title:
--   The calibration algorithm (4)–(6)
-- statement:
--   Let $\theta\ge1$ be a tuning parameter, and for a route $p$ and a period $t$ write the opportunity cost
--   $$\mathrm{oc}_{pt}=\sum_{i\in A_p}\frac1{c_i}\sum_{k\in\mathcal J}\sum_{q\in\mathcal R_k}a_{iq}\,\hat\gamma_{kqt}.$$
--   The triple $(\hat\gamma,\hat p,\hat S)$ is an output of the algorithm if $\hat\gamma_{jp,T+1}=0$ and, for $t=T,\dots,1$,
--
--   1. $\hat p_{jt}\in\arg\max_{p\in\mathcal R_j}\{f_j-\theta\,\mathrm{oc}_{p,t+1}\}$ for each $j$;
--   2. $\hat S_t\in\arg\max_{S\subseteq\mathcal J}\sum_{j}\phi_{jt}(S)\big(f_j-\theta\,\mathrm{oc}_{\hat p_{jt},t+1}\big)$;
--   3. $\hat\gamma_{jpt}=\phi_{jt}(\hat S_t)\,\mathbf 1_{(\hat p_{jt}=p)}\big(f_j-\theta\,\mathrm{oc}_{p,t+1}\big)+\hat\gamma_{jp,t+1}$ for $j\in\mathcal J$, $p\in\mathcal R_j$.
--
--   The algorithm calibrates the parameters of $\hat\Psi_t$ backwards in time.
--
--   **Formalization Note** This is a relation, so it covers every tie-break in the two $\arg\max$. The tuning condition $\theta\ge1$ is a separate hypothesis of each theorem.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Eqs. (4)–(6), p.10

import Mathlib
import Definitions.Def_FlexibleNRM_Network

namespace FlexibleNRM

/-- The state-independent opportunity cost of route `p` at period `t`,
`∑_{i ∈ A_p} (1 / c_i) ∑_k ∑_{q ∈ R_k} a_iq γ̂_kqt`.

Zhu, Topaloglu, manuscript of November 16, 2022, §3, p.10, and Lemma 5.2, p.15. -/
noncomputable def opportunityCost {n m r : ℕ} (N : Network n m r) (γ : Fin n → Fin r → ℕ → ℝ)
    (p : Fin r) (t : ℕ) : ℝ :=
  ∑ i ∈ N.A p, (1 / (N.c i : ℝ)) * ∑ k, ∑ q ∈ N.R k, (N.a i q : ℝ) * γ k q t

/-- The net revenue that appears in (4)–(6),
`f_j − θ ∑_{i ∈ A_p} (1 / c_i) ∑_k ∑_{q ∈ R_k} a_iq γ̂_kq,t+1`.

Zhu, Topaloglu, manuscript of November 16, 2022, Eqs. (4)–(6), p.10. -/
noncomputable def netRevenue {n m r : ℕ} (N : Network n m r) (θ : ℝ)
    (γ : Fin n → Fin r → ℕ → ℝ) (j : Fin n) (p : Fin r) (t : ℕ) : ℝ :=
  N.f j - θ * opportunityCost N γ p (t + 1)

/-- `(γ̂, p̂, Ŝ)` is an output of the **calibration algorithm** (4)–(6) with tuning parameter `θ`:
`γ̂_jp,T+1 = 0`, and for each period `t = T, …, 1`,
(4) `p̂_jt` maximizes the net revenue of product `j` over `R_j`;
(5) `Ŝ_t` maximizes `∑_j φ_jt(S) (net revenue of j on p̂_jt)` over `S ⊆ J`;
(6) `γ̂_jpt = φ_jt(Ŝ_t) 1(p̂_jt = p) (net revenue of j on p) + γ̂_jp,t+1` for `p ∈ R_j`.

Zhu, Topaloglu, manuscript of November 16, 2022, Eqs. (4)–(6), p.10.

**Formalization Note** This is a relation, not a function, so every tie-break in the two `arg max`
is an instance of it. The values of `γ` at `p ∉ R j` are never read. -/
structure IsCalibration {n m r : ℕ} (N : Network n m r) (θ : ℝ) (γ : Fin n → Fin r → ℕ → ℝ)
    (phat : Fin n → ℕ → Fin r) (Shat : ℕ → Finset (Fin n)) : Prop where
  /-- The boundary condition `γ̂_jp,T+1 = 0`. -/
  boundary : ∀ j, ∀ p ∈ N.R j, γ j p (N.T + 1) = 0
  /-- The ideal route is a route of the product. -/
  phat_mem : ∀ t ∈ Finset.Icc 1 N.T, ∀ j, phat j t ∈ N.R j
  /-- Eq. (4). -/
  phat_max : ∀ t ∈ Finset.Icc 1 N.T, ∀ j, ∀ p ∈ N.R j,
    netRevenue N θ γ j p t ≤ netRevenue N θ γ j (phat j t) t
  /-- Eq. (5). -/
  Shat_max : ∀ t ∈ Finset.Icc 1 N.T, ∀ S : Finset (Fin n),
    ∑ j, (N.φ t).prob S j * netRevenue N θ γ j (phat j t) t ≤
      ∑ j, (N.φ t).prob (Shat t) j * netRevenue N θ γ j (phat j t) t
  /-- Eq. (6). -/
  gamma_step : ∀ t ∈ Finset.Icc 1 N.T, ∀ j, ∀ p ∈ N.R j,
    γ j p t = (N.φ t).prob (Shat t) j * (if phat j t = p then 1 else 0) *
      netRevenue N θ γ j p t + γ j p (t + 1)

end FlexibleNRM


