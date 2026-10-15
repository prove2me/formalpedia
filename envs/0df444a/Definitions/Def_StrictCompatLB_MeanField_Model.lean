-- Prove2me | Definitions.Def_StrictCompatLB_MeanField_Model
-- name    : StrictCompatLB_MeanField_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:50.846078+00:00
-- url     : https://prove2.me/theorems/638de846-f790-4e88-b102-60d94c0ce7db
-- title:
--   The load-balancing Markov process Φ(G_N, ·) as a uniformised chain, and tightness in ℓ^ω_1
-- statement:
--   The system on $G_N$ (§2, p. 8): each dispatcher $w\in W_N$ receives a Poisson stream of tasks of rate $\lambda N/M(N)$, independently, so the total arrival rate is $\lambda N$; each server has its own queue with unit-rate exponential services; an arriving task is routed by a **routing law** $\rho_w(z,\cdot)$, a probability vector on $V_N$ supported on $\mathcal N_w$.
--
--   All rates are bounded by $(\lambda+1)N$, so the process $\Phi(G_N,\cdot)$ is the uniformised chain run at the epochs of a Poisson clock of rate $(\lambda+1)N$ (App. H). Its jump kernel is
--   $$K_N(z,z')=\frac{\lambda}{\lambda+1}\cdot\frac1{M(N)}\sum_{w\in W_N}\sum_{v\in V_N}\rho_w(z,v)\,\mathbb 1\{z'=z+e_v\}+\frac1{\lambda+1}\cdot\frac1N\sum_{v\in V_N}\mathbb 1\{z'=z-e_v\mathbb 1\{z_v\ge1\}\}:$$
--   with probability $\lambda/(\lambda+1)$ an arrival at a uniformly chosen dispatcher, and with probability $1/(\lambda+1)$ a potential departure at a uniformly chosen server, which is a dummy event when that server is idle. This gives rate $\lambda N/M(N)$ per dispatcher and rate $1$ per busy server. For JSQ(d), $\rho$ is the JSQ(d) routing law.
--
--   The occupancy process is $q(\Phi(G_N,t))$. The steady state $\Phi(G_N,\infty)$ is distributed according to a stationary distribution $\pi_N$ of $K_N$.
--
--   **Tightness in $\ell^\omega_1$.** For positive weights $\omega=(\omega_1,\omega_2,\dots)$, the norm $\|q\|^\omega_1=\sum_{i\ge1}\omega_i|q_i|$ makes $q\mapsto(\omega_iq_i)_{i\ge1}$ an isometry of $\ell^\omega_1$ onto $\ell_1$ (App. I). The laws of $q(\Phi(G_N,\infty))$, $N\ge N_0$, are tight in $\ell^\omega_1$ if for every $\eta>0$ there is a compact $K\subseteq\ell_1$ with
--   $$\pi_N\big(\{z:(\omega_iq_i(z))_{i\ge1}\notin K\}\big)\le\eta\qquad\text{for all }N\ge N_0 .$$
--
--   **Formalization Note** A process realisation is a pair $(Y,\tau)$ on a probability space as in `IsUniformizedProcess`, with clock rate $(\lambda+1)N$; theorems quantify over every such realisation, so nothing depends on a particular construction. The rate is positive only for $N\ge1$, and theorems require the realisation only for $N\ge1$. The departure uses natural-number subtraction, which is exactly the dummy event at an idle server. Routing laws are required to be nonnegative, supported on $\mathcal N_w$ and to sum to one, which forces nonempty neighbourhoods; otherwise $K_N$ would not be stochastic and no process could exist. "$\notin K$" includes the case where $(\omega_iq_i)$ is not summable.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, pp. 8–9, §2 (model, Φ(G_N, t), S_N); p. 46, App. H (uniformised chain); p. 7, §1.4 and pp. 50–51, App. I, (I.1)–(I.2) (ℓ^ω_1)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_CountableChain
import Definitions.Def_StrictCompatLB_MeanField_Policy

open Finset MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-! The load-balancing Markov process `Φ(G_N, ·)` of Rutten & Mukherjee, arXiv:2008.07562v2
(§2, pp. 8–9; App. H, p. 46): dispatchers `w ∈ W_N` receive Poisson arrivals of rate
`λN/M(N)` each, servers serve at rate `1`, and an arrival at `w` is routed by a routing law.
All rates are bounded (total `(λ + 1)N`), so the process is the uniformised chain at the epochs
of a Poisson clock of rate `(λ + 1)N`. -/

/-- The state after an arrival at server `v`: `z + e_v`. -/
def arrive {N : ℕ} (z : Fin N → ℕ) (v : Fin N) : Fin N → ℕ :=
  Function.update z v (z v + 1)

/-- The state after a potential departure at server `v`: `z − e_v` if `z_v ≥ 1`, and `z`
itself (a dummy event) if `z_v = 0` (natural-number subtraction). -/
def depart {N : ℕ} (z : Fin N → ℕ) (v : Fin N) : Fin N → ℕ :=
  Function.update z v (z v - 1)

/-- A **routing law** on `G_N`: `route w z v` is the probability that a task arriving at
dispatcher `w` in state `z` joins server `v`. It is nonnegative, vanishes off `𝒩_w`, and sums to
one over `v` (so every dispatcher has a nonempty neighbourhood). -/
def IsRoutingRule (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ) : Prop :=
  (∀ w z v, 0 ≤ route w z v) ∧ (∀ w z v, v ∉ nbrW M G N w → route w z v = 0) ∧
    ∀ w z, ∑ v, route w z v = 1

/-- The jump kernel of the uniformised chain (App. H, p. 46): at each epoch, with probability
`λ/(λ + 1)` a task arrives at a dispatcher `w` chosen uniformly from `W_N` and joins server `v`
with probability `route w z v`; with probability `1/(λ + 1)` a server `v` chosen uniformly from
`V_N` completes a service if busy (otherwise nothing happens). This gives rate `λN/M(N)` per
dispatcher and rate `1` per busy server. -/
noncomputable def lbKernel (lam : ℝ) (M : ℕ → ℕ) (N : ℕ)
    (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ) (z z' : Fin N → ℕ) : ℝ :=
  lam / (lam + 1) * (1 / (M N : ℝ)) *
      ∑ w : Fin (M N), ∑ v : Fin N, route w z v * (if z' = arrive z v then 1 else 0) +
    1 / (lam + 1) * (1 / (N : ℝ)) * ∑ v : Fin N, (if z' = depart z v then 1 else 0)

/-- The jump kernel of the system on `G_N` under JSQ(d) (sampling without replacement). -/
noncomputable def jsqdKernel (lam : ℝ) (d : ℕ) (M : ℕ → ℕ)
    (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) : (Fin N → ℕ) → (Fin N → ℕ) → ℝ :=
  lbKernel lam M N (jsqdRoute M G N d)

/-- `(Y, τ)` on `(Ω, P)` realises the load-balancing process on `N` servers with arrival rate
`λ`, routing law `route` and initial state `z₀`: `Y` is the uniformised chain with kernel
`lbKernel`, run at the epochs of an independent Poisson clock of rate `(λ + 1)N`;
`Φ(G_N, t) = jumpPath Y τ t`. -/
def IsLBProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam : ℝ) (M : ℕ → ℕ) (N : ℕ)
    (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ) (z₀ : Fin N → ℕ)
    (Y : ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → Ω → ℝ) : Prop :=
  IsUniformizedProcess P (lbKernel lam M N route) ((lam + 1) * (N : ℝ)) z₀ Y τ

/-- The process `Φ(G_N, t)` at time `t` on the sample point `ω`. -/
noncomputable def statePath {Ω : Type*} {N : ℕ} (Y : ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → Ω → ℝ)
    (ω : Ω) (t : ℝ) : Fin N → ℕ :=
  jumpPath (fun n => Y n ω) (fun k => τ k ω) t

/-- The scaled occupancy process `q(Φ(G_N, t))` on the sample point `ω`. -/
noncomputable def occPath {Ω : Type*} {N : ℕ} (Y : ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → Ω → ℝ)
    (ω : Ω) (t : ℝ) : ℕ → ℝ :=
  occ (statePath Y τ ω t)

/-- **Tightness in `ℓ^ω_1`** (§1.4, p. 7; App. I, (I.1)–(I.2), p. 50) of the laws of
`q(Φ(G_N, ∞))`, `N ≥ N₀`, where `π N` is the law of `Φ(G_N, ∞)` on `S_N`: for every `η > 0` there is
a compact set `K ⊆ ℓ₁` such that for every `N ≥ N₀`, the probability that the weighted
occupancy `(ω_i q_i)_{i ≥ 1}` is not (a summable sequence) in `K` is at most `η`. The map
`q ↦ (ω_i q_i)_{i ≥ 1}` is the isometry of `ℓ^ω_1` onto `ℓ₁`, so this is tightness of the laws
of `q` in `ℓ^ω_1`. -/
def IsTightWeighted (ω : ℕ → ℝ) (N₀ : ℕ) (π : (N : ℕ) → (Fin N → ℕ) → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : Set (lp (fun _ : ℕ => ℝ) 1), IsCompact K ∧
    ∀ N ≥ N₀, probOf (π N)
      {z | ¬ ∃ y ∈ K, ∀ i : ℕ, (y : ℕ → ℝ) i = ω (i + 1) * occ z (i + 1)} ≤ η

end StrictCompatLB.MeanField


