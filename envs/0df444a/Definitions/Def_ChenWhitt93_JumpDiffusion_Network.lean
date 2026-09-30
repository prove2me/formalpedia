-- Prove2me | Definitions.Def_ChenWhitt93_JumpDiffusion_Network
-- name    : ChenWhitt93_JumpDiffusion_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:47:03.879987+00:00
-- url     : https://prove2.me/theorems/cdd244cd-e23a-4622-afc3-c921a53bcde9
-- title:
--   Section 3 — the open queueing network with exogenous service interruptions, (3.1)–(3.3), (3.9)–(3.11)
-- statement:
--   This file sets up the network model of Section 3 of Chen and Whitt (1993). There are $J$ single-server stations.
--
--   1. **Up and down times.** For station $j$, $u^j_k$ and $d^j_k$ ($k\ge 1$) are the durations of the $k$th up period and the $k$th down period; all stations start at the beginning of an up period. The $(l+1)$st up period begins at
--   $$
--   T^j_l=\sum_{k=1}^{l}(u^j_k+d^j_k),\qquad T^j_0=0,
--   $$
--   station $j$ is up on $[T^j_l,T^j_l+u^j_{l+1})$ and down on $[T^j_l+u^j_{l+1},T^j_{l+1})$. The durations are nonnegative and $T^j_l\to\infty$ as $l\to\infty$ (finitely many cycles in finite time). The cumulative down time and up time are
--   $$
--   D_j(t)=\int_0^t 1[I_j(s)=0]\,ds,\qquad U_j(t)=t-D_j(t).
--   $$
--   2. **Primitive data.** $Z_j(0)\in\mathbb N$ is the initial queue length. $A_j(t)$ is the number of external arrivals to $j$ in $[0,t]$. $S_j(t)$ is the number of services completed at $j$ in its first $t$ units of busy time. The routing indicators $\chi_{kj}(l)$ equal $1$ when the $l$th departure from $k$ goes to $j$, with at most one destination per departure. The routing process is $R_{kj}(m)=\sum_{l=1}^m\chi_{kj}(l)$. $A_j$ and $S_j$ are nondecreasing and right-continuous.
--   3. **Queue length and busy time.** A pair $(Z,B)$ solves the network equations when, for all $t\ge 0$ and all $j$, $Z_j(t)\ge 0$ and
--   $$
--   Z_j(t)=Z_j(0)+A_j(t)+\sum_{k=1}^J R_{kj}\big(S_k(B_k(t))\big)-S_j(B_j(t)),\qquad (3.2)
--   $$
--   $$
--   B_j(t)=\int_0^t 1[Z_j(s)>0]\,1[I_j(s)=1]\,ds. \qquad (3.3)
--   $$
--   The cumulative idle time is $Y_j(t)=U_j(t)-B_j(t)$ (3.1).
--   4. **The centred processes.** For rates $\lambda,\mu\in\mathbb R^J$ and a routing matrix $P$,
--   $$
--   \xi_j(t)=A_j(t)-\lambda_jt+\sum_{k}\big[R_{kj}(S_k(B_k(t)))-P_{kj}S_k(B_k(t))\big]+\sum_k P_{kj}\big[S_k(B_k(t))-\mu_kB_k(t)\big]-\big[S_j(B_j(t))-\mu_jB_j(t)\big], \qquad (3.9)
--   $$
--   $$
--   \eta_j(t)=\Big(\lambda_j-\mu_j+\sum_k\mu_kP_{kj}\Big)t+\mu_jD_j(t)-\sum_k\mu_kP_{kj}D_k(t), \qquad (3.10)
--   $$
--   and the free process is $X_j(t)=Z_j(0)+\xi_j(t)+\eta_j(t)$ (3.11).
--
--   Every scaled process of Section 4 is built from these objects.
--
--   **Formalization Note** Stations are `Fin J`. The page indexes durations from $k=1$; here `up j k` is $u^j_{k+1}$. $Z$ is integer valued and (3.2) is computed in $\mathbb Z$, so no natural-number subtraction occurs. $Z\ge 0$ is part of the solution concept: the page's $Z_j(t)$ is a number of customers. The page asserts, citing Chen and Mandelbaum [5], that exactly one solution exists. The theorems of the mission quantify over all solutions and do not use a construction. The integrals in (3.3) and in $D_j$ are Lebesgue measures of subsets of $[0,t]$.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), pp. 343–346, Section 3 (the primitive data, T_lʲ and I_j on p. 343; U, D, (3.1)–(3.3) on p. 344; (3.9) on p. 345; (3.10)–(3.11) on p. 346)

import Mathlib

namespace ChenWhitt93.JumpDiffusion

open Filter Topology MeasureTheory

/-!
Chen and Whitt (1993), Section 3, pp. 343–346: the open network with `J` stations and exogenous
service interruptions. Stations are indexed by `Fin J`. Sequences indexed on the page from `1`
(up and down durations `u_kʲ, d_kʲ`, `k ≥ 1`) are indexed from `0` here: `up j k` is the page's
`u_{k+1}ʲ`.
-/

/-- The up/down cycles of one network: `up j k` and `down j k` are the durations of the
`(k+1)`st up period and `(k+1)`st down period of station `j`. -/
structure Interruptions (J : ℕ) where
  up : Fin J → ℕ → ℝ
  down : Fin J → ℕ → ℝ

/-- `T_lʲ = Σ_{k=1}^{l} (u_kʲ + d_kʲ)`, the epoch beginning the `(l+1)`st up period (p. 343). -/
def Interruptions.cycleStart {J : ℕ} (I : Interruptions J) (j : Fin J) (l : ℕ) : ℝ :=
  ∑ k ∈ Finset.range l, (I.up j k + I.down j k)

/-- `Iⱼ(t) = 1`: station `j` is up at time `t`, i.e. `T_lʲ ≤ t < T_lʲ + u_{l+1}ʲ` for some `l ≥ 0`. -/
def Interruptions.IsUp {J : ℕ} (I : Interruptions J) (j : Fin J) (t : ℝ) : Prop :=
  ∃ l : ℕ, I.cycleStart j l ≤ t ∧ t < I.cycleStart j l + I.up j l

/-- `Iⱼ(t) = 0`: station `j` is down at time `t`, i.e. `T_lʲ + u_{l+1}ʲ ≤ t < T_{l+1}ʲ` for some
`l ≥ 0`. -/
def Interruptions.IsDown {J : ℕ} (I : Interruptions J) (j : Fin J) (t : ℝ) : Prop :=
  ∃ l : ℕ, I.cycleStart j l + I.up j l ≤ t ∧ t < I.cycleStart j (l + 1)

/-- The page's assumptions on the durations (p. 343): they are nonnegative and `T_lʲ → ∞` as
`l → ∞` for each `j` (finitely many up–down cycles in finite time). -/
def Interruptions.IsValid {J : ℕ} (I : Interruptions J) : Prop :=
  (∀ j k, 0 ≤ I.up j k ∧ 0 ≤ I.down j k) ∧
  ∀ j, Tendsto (fun l => I.cycleStart j l) atTop atTop

/-- `Dⱼ(t) = ∫₀ᵗ 1[Iⱼ(s) = 0] ds`, the cumulative down time of station `j` in `[0, t]` (p. 344). -/
noncomputable def Interruptions.downTime {J : ℕ} (I : Interruptions J) (j : Fin J) (t : ℝ) : ℝ :=
  volume.real (Set.Icc 0 t ∩ {s | I.IsDown j s})

/-- `Uⱼ(t) = t − Dⱼ(t)`, the cumulative up time of station `j` in `[0, t]` (p. 344). -/
noncomputable def Interruptions.upTime {J : ℕ} (I : Interruptions J) (j : Fin J) (t : ℝ) : ℝ :=
  t - I.downTime j t

/-- The primitive data of one network other than the routing (p. 343): initial queue lengths
`Zⱼ(0)`, the arrival process `Aⱼ(t)` (external arrivals to `j` in `[0, t]`), the service process
`Sⱼ(t)` (services completed at `j` in the first `t` units of busy time of `j`), and the up/down
durations. -/
structure NetworkData (J : ℕ) extends Interruptions J where
  Z0 : Fin J → ℕ
  A : ℝ → Fin J → ℕ
  S : ℝ → Fin J → ℕ

/-- `R_{kj}(m) = Σ_{l=1}^{m} χ_{kj}(l)`: the number among the first `m` departures from station
`k` that go to station `j`, for routing indicators `χ k j l` (p. 343). -/
def routingCount {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (k j : Fin J) (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter (fun l => χ k j l = true)).card

/-- The standing assumptions of Section 3 on one network (p. 343–344): valid up/down durations;
`Aⱼ` and `Sⱼ` nondecreasing and right-continuous on `[0, ∞)` (elements of `D`); and each
departure is routed to at most one station. -/
def NetworkData.IsValid {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J) : Prop :=
  N.toInterruptions.IsValid ∧
  (∀ j, MonotoneOn (fun t => N.A t j) (Set.Ici 0) ∧ MonotoneOn (fun t => N.S t j) (Set.Ici 0)) ∧
  (∀ j, ∀ t, 0 ≤ t →
    ContinuousWithinAt (fun s => (N.A s j : ℝ)) (Set.Ici t) t ∧
    ContinuousWithinAt (fun s => (N.S s j : ℝ)) (Set.Ici t) t) ∧
  ∀ k j m l, χ k j l = true → χ k m l = true → j = m

/-- `(Z, B)` is a queue-length / busy-time pair of the network (p. 344): for all `t ≥ 0` and all
stations `j`, `Zⱼ(t) ≥ 0` (a number of customers) and
* (3.2) `Zⱼ(t) = Zⱼ(0) + Aⱼ(t) + Σₖ R_{kj}(Sₖ(Bₖ(t))) − Sⱼ(Bⱼ(t))`,
* (3.3) `Bⱼ(t) = ∫₀ᵗ 1[Zⱼ(s) > 0] 1[Iⱼ(s) = 1] ds`. -/
def IsQueueSolution {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J)
    (Z : ℝ → Fin J → ℤ) (B : ℝ → Fin J → ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ j,
    0 ≤ Z t j ∧
    Z t j = (N.Z0 j : ℤ) + (N.A t j : ℤ) + ∑ k, (routingCount χ k j (N.S (B t k) k) : ℤ)
      - (N.S (B t j) j : ℤ) ∧
    B t j = volume.real {s | s ∈ Set.Icc 0 t ∧ 0 < Z s j ∧ N.IsUp j s}

/-- (3.1) `Yⱼ(t) = Uⱼ(t) − Bⱼ(t)`, the cumulative idle time of station `j` (down time excluded). -/
noncomputable def idleTime {J : ℕ} (N : NetworkData J) (B : ℝ → Fin J → ℝ) (t : ℝ) : Fin J → ℝ :=
  fun j => N.upTime j t - B t j

/-- (3.9), with arrival rates `lam` and service rates `mu` and routing matrix `P`:
`ξⱼ(t) = Aⱼ(t) − λⱼt + Σₖ [R_{kj}(Sₖ(Bₖ(t))) − P_{kj}Sₖ(Bₖ(t))]
  + Σₖ P_{kj}[Sₖ(Bₖ(t)) − μₖBₖ(t)] − [Sⱼ(Bⱼ(t)) − μⱼBⱼ(t)]`. -/
noncomputable def xi {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J)
    (lam mu : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ) (B : ℝ → Fin J → ℝ) (t : ℝ) :
    Fin J → ℝ :=
  fun j => (N.A t j : ℝ) - lam j * t
    + ∑ k, ((routingCount χ k j (N.S (B t k) k) : ℝ) - P k j * (N.S (B t k) k : ℝ))
    + ∑ k, P k j * ((N.S (B t k) k : ℝ) - mu k * B t k)
    - ((N.S (B t j) j : ℝ) - mu j * B t j)

/-- (3.10) `ηⱼ(t) = (λⱼ − μⱼ + Σₖ μₖP_{kj}) t + μⱼDⱼ(t) − Σₖ μₖP_{kj}Dₖ(t)`. -/
noncomputable def eta {J : ℕ} (N : NetworkData J) (lam mu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (t : ℝ) : Fin J → ℝ :=
  fun j => (lam j - mu j + ∑ k, mu k * P k j) * t + mu j * N.downTime j t
    - ∑ k, mu k * P k j * N.downTime k t

/-- (3.11) `Xⱼ(t) = Zⱼ(0) + ξⱼ(t) + ηⱼ(t)`, the free (netput) process. -/
noncomputable def freeProcess {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J)
    (lam mu : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ) (B : ℝ → Fin J → ℝ) (t : ℝ) :
    Fin J → ℝ :=
  fun j => (N.Z0 j : ℝ) + xi χ N lam mu P B t j + eta N lam mu P t j

end ChenWhitt93.JumpDiffusion


