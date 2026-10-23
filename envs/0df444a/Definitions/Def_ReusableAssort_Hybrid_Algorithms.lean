-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_Algorithms
-- name    : ReusableAssort_Hybrid_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:20.693697+00:00
-- url     : https://prove2.me/theorems/75714dc0-d7c6-4551-92d7-7e16564b8ffe
-- title:
--   (3), (4), Algorithms 2–3 and Sim+Hybrid(i), pp. 15–20 — the optimistic DP, thresholds and hybrid rule
-- statement:
--   This file defines the algorithms of §3 as assignments of discarding rules to products, for a given LP solution $y$.
--
--   Let $X_{S,t,z} = y_{S,t,z} F_t(z)$. The *optimistic per-unit DP* (3) is, with $\mathcal V_{i,T+1} = 0$,
--   $$\mathcal V_{i,t} = \sum_{z} \sum_{S \in \mathcal S} X_{S,t,z} \max\Big\{ \mathcal V_{i,t+1},\ (1 - \phi^{z}(S,i))\, \mathcal V_{i,t+1} + \phi^{z}(S,i)\Big( \frac{1}{c_i} \sum_d g^{z}_i(d)\,(r^{z}_i + \mathcal V_{i,t+d}) + \frac{c_i - 1}{c_i}\, \mathcal V_{i,t+1}\Big)\Big\},$$
--   and the revenue thresholds of (4) are $P^{z}_{i,t} = \mathcal V_{i,t+1} - \sum_d g^{z}_i(d)\, \mathcal V_{i,t+d}$.
--
--   * **Algorithm 2** discards every product at random with the same probability $\gamma$.
--   * **Algorithm 3** keeps product $i$ at time $t$ for type $z$ only if $r^{z}_i \ge P^{z}_{i,t}$.
--   * **Sim+Hybrid(i)** computes $\mathcal R_i = c_i \mathcal V_{i,1} / \big(\sum_{t}\sum_{z}\sum_{S} X_{S,t,z}\, \phi^{z}(S,i)\, r^{z}_i\big)$. A product with $\mathcal R_i + \varepsilon^*(c_i) < 1$ is labelled "large inventory" and discarded at random with probability $\gamma^*(c_i)$; every other product uses the thresholds of Algorithm 3.
--
--   **Formalization Note** $\mathcal V_{i,s}$ is $0$ for every $s > T$, so the terms $\mathcal V_{i,t+d}$ with $t + d > T + 1$ (a unit back after the horizon) vanish. $\mathcal R_i$ uses Lean's $x/0 = 0$: a product with zero LP contribution gets $\mathcal R_i = 0$; it contributes $0$ to both sides of every guarantee. The page does not specify the discarding probability of a large product; it is a minimizer $\gamma^*(c_i)$ of (1) at $x = c_i$, supplied as `gam (c i)` (with $\gamma^*(c_{\min})$ a large product could earn less than half of its contribution, and Theorem 3 would fail).
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, pp. 16–17 (X_{S,t,z_t}, eq. (3), eq. (4)), p. 15 (Algorithm 2), p. 18 (Algorithm 3), pp. 19–20 (R_i and Sim+Hybrid(i))

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Process

namespace ReusableAssort.Hybrid

variable {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]

/-- `X_{S,t,z} = y_{S,t,z} F_t(z)` (§3.3.1, p. 16). -/
noncomputable def X (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (t : ℕ) (z : Z) (S : Finset (Fin n)) : ℝ :=
  y t z S * I.F t z

/-- The optimistic per-unit DP (3), p. 17: `V I y i t = 𝒱_{i,t}` for `t ≤ T`, and `0` for
`t > T` (the boundary `𝒱_{i,T+1} = 0`, and a unit back after `T` earns nothing). -/
noncomputable def V (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n)
    (t : ℕ) : ℝ :=
  if _h : T < t then 0 else
  ∑ z, ∑ S ∈ I.feas, X I y t z S *
    max (V I y i (t + 1))
      ((1 - I.phi z S i) * V I y i (t + 1)
        + I.phi z S i *
          ((1 / (I.c i : ℝ)) * ∑ d ∈ (Finset.Icc 1 T).attach,
              I.g z i d.1 * (I.r z i + V I y i (t + d.1))
            + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * V I y i (t + 1)))
termination_by T + 1 - t
decreasing_by
  all_goals first
    | omega
    | (have hd := d.2; simp only [Finset.mem_Icc] at hd; omega)

/-- The revenue thresholds `P^{z}_{i,t} = 𝒱_{i,t+1} - Σ_d g^{z}_i(d) 𝒱_{i,t+d}` of (4) and
Algorithm 3, line 1. -/
noncomputable def P (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n)
    (t : ℕ) (z : Z) : ℝ :=
  V I y i (t + 1) - ∑ d ∈ Finset.Icc 1 T, I.g z i d * V I y i (t + d)

/-- Algorithm 2 (p. 15): every product is discarded at random with probability `γ`. -/
def alg2 (γ : ℝ) : Fin n → Rule Z := fun _ => Rule.random γ

/-- Algorithm 3 (p. 18): product `i` is kept only if `r^{z_t}_i ≥ P^{z_t}_{i,t}`. -/
noncomputable def alg3 (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) :
    Fin n → Rule Z :=
  fun i => Rule.threshold (P I y i)

/-- `ℛ_i = c_i 𝒱_{i,1} / Σ_t Σ_z Σ_S X_{S,t,z} ϕ^z(S, i) r^z_i` (p. 19). -/
noncomputable def R (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n) : ℝ :=
  (I.c i : ℝ) * V I y i 1 / contrib I y i

/-- Sim+Hybrid(i) (§3.4, pp. 19–20): product `i` is "large inventory" when
`ℛ_i + ε*(c_i) < 1` and is then discarded at random with probability `gam c_i`
(a minimizer `γ*(c_i)` of (1)); otherwise it is discarded by the thresholds of Algorithm 3. -/
noncomputable def hybrid (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (gam : ℕ → ℝ) : Fin n → Rule Z :=
  fun i => if R I y i + epsStar (I.c i : ℝ) < 1 then Rule.random (gam (I.c i))
    else Rule.threshold (P I y i)

end ReusableAssort.Hybrid


