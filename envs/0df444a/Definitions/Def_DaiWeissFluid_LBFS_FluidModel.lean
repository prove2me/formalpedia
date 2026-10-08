-- Prove2me | Definitions.Def_DaiWeissFluid_LBFS_FluidModel
-- name    : DaiWeissFluid_LBFS_FluidModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:30:05.871778+00:00
-- url     : https://prove2.me/theorems/5ded8786-fa59-49e3-bb5c-b74e2cb5bbab
-- title:
--   Reentrant line, priority fluid model, LBFS ranking, and fluid stability
-- statement:
--   This module fixes the deterministic fluid model of a **reentrant line** (Dai and Weiss, §1 and §4).
--
--   **The line.** There are $I$ stations and $K$ classes. All fluid follows one route: it enters as class $1$, on completion of class $k$ becomes class $k+1$, and leaves after class $K$. Class $k$ is served at station $\sigma(k)$ with mean service time $m_k$, and $\mu_k = 1/m_k$. The **constituency** of station $i$ is $C_i = \{k : \sigma(k) = i\}$, and its **nominal workload** is $\rho_i = \sum_{k \in C_i} m_k$. The exogenous arrival rate is normalised to $1$.
--
--   **Fluid model (Definition 1.2).** A pair of paths $Q(t) = (Q_1(t),\dots,Q_K(t))$ (fluid levels) and $T(t) = (T_1(t),\dots,T_K(t))$ (cumulative time spent serving each class) is a fluid model solution when, for $t \ge 0$,
--   $$
--   Q_k(t) = Q_k(0) + \mu_{k-1}T_{k-1}(t) - \mu_k T_k(t),\qquad Q_k(t) \ge 0,
--   $$
--   with the convention $\mu_0 T_0(t) = t$ (1.8)–(1.9); $T_k(0) = 0$ and $T_k$ is nondecreasing (1.10); and the **idle time** $U_i(t) = t - B_i(t)$ of station $i$, where $B_i(t) = \sum_{k\in C_i} T_k(t)$, is nondecreasing (1.11)–(1.12). The **work-conserving** model adds (1.13): $U_i$ increases only at times when $\sum_{k\in C_i}Q_k(t) = 0$. The immediate volume is $W_i(t) = \sum_{k\in C_i} m_k Q_k(t)$ (2.1).
--
--   **Priority disciplines (§4).** A buffer priority discipline is a permutation $\pi$ of the classes; class $k$ has priority over class $l$ when $\pi(k) < \pi(l)$. Let $H_k = \{l \in C_{\sigma(k)} : \pi(l) \le \pi(k)\}$, $T_k^+(t) = \sum_{l\in H_k} T_l(t)$ (4.1), $U_k^+(t) = t - T_k^+(t)$ (4.2) and $W_k^+(t) = \sum_{l \in H_k} m_l Q_l(t)$ (4.3). The fluid model of the preemptive-resume priority discipline $\pi$ consists of (1.8)–(1.12) together with (4.4): $U_k^+$ increases only at times when $W_k^+(t) = 0$. The **Last-Buffer-First-Served** (LBFS) discipline is $\pi(k) = K+1-k$ (Definition 4.1).
--
--   **Rates (4.5).** At a regular time $t$, where every $T_k$ has a derivative $\dot T_k(t)$, the out-flow rate of buffer $k$ is $d_k(t) = \mu_k \dot T_k(t)$ and its in-flow rate is $a_k(t) = \mu_{k-1}\dot T_{k-1}(t)$, which is $1$ for the first class.
--
--   **LBFS capacity bound.** For the LBFS ranking, the class with the larger route index has higher priority. The proof of Theorem 4.4 uses $\hat\lambda = 1/\max_i \rho_i$, the reciprocal of the largest nominal station workload.
--
--   **Stability (Definition 1.3).** A fluid model is stable if there is a time $\delta > 0$ such that every solution with $|Q(0)| = \sum_k Q_k(0) = 1$ has $Q_k(t) = 0$ for all $t \ge \delta$ and all $k$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Classes and stations are `Fin K` and `Fin I`, 0-based: the paper's class $k$ is Lean index $k-1$. Paths are total functions `ℝ → Fin K → ℝ`, and every equation is imposed only on $t \ge 0$. The conditions "$U$ increases only when the content is zero" in (1.13) and (4.4) are encoded by `ConstantWhile`: $U$ is constant on every interval $[s,t] \subseteq [0,\infty)$ throughout which the content stays positive. For continuous paths this is equivalent to the paper's Stieltjes form $\int_0^\infty W_k^+(t)\,dU_k^+(t) = 0$. Lipschitz continuity is not imposed, since it follows from (1.10)–(1.12). The rates take the derivatives `dT k` as an argument. LBFS is `Fin.revPerm`, so $H_k$ contains classes at the same station with route index at least $k$. The value of `lamHat` is meaningful in the theorem when $K>0$ and all $m_k>0$. `FluidStable P` quantifies over the solution pairs $(Q,T)$ satisfying `P` with $\sum_k Q_k(0) = 1$.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), pp. 115–120, 122–125, Definitions 1.2, 1.3, 4.1, (1.7)–(1.13), (2.1), (4.1)–(4.5), proof of Theorem 4.4

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel

namespace DaiWeissFluid.LBFS

open Set

/-- A reentrant line has `K` route stages and `I` stations. -/
structure ReentrantLine (I K : ℕ) where
  σ : Fin K → Fin I
  m : Fin K → ℝ

namespace ReentrantLine

variable {I K : ℕ} (L : ReentrantLine I K)

/-- Service rate at a class. -/
noncomputable def μ (k : Fin K) : ℝ := (L.m k)⁻¹

/-- Constituency of station `i`. -/
def C (i : Fin I) : Finset (Fin K) := Finset.univ.filter (fun k => L.σ k = i)

/-- Nominal workload per unit time at station `i`. -/
noncomputable def ρ (i : Fin I) : ℝ := ∑ k ∈ L.C i, L.m k

/-- Inflow in (1.8), with external unit-rate input at the first class. -/
noncomputable def inflow (T : ℝ → Fin K → ℝ) (k : Fin K) (t : ℝ) : ℝ :=
  if h : (k : ℕ) = 0 then t
  else L.μ ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ *
    T t ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩

/-- Cumulative busy time at a station. -/
noncomputable def busy (T : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) : ℝ :=
  ∑ k ∈ L.C i, T t k

/-- Cumulative idle time at a station. -/
noncomputable def idle (T : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) : ℝ :=
  t - L.busy T i t

/-- Immediate volume at a station. -/
noncomputable def volume (Q : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) : ℝ :=
  ∑ k ∈ L.C i, L.m k * Q t k

/-- Fluid equations (1.8)–(1.12) on nonnegative time. -/
structure IsFluidSolution (Q T : ℝ → Fin K → ℝ) : Prop where
  flow : ∀ t, 0 ≤ t → ∀ k, Q t k = Q 0 k + L.inflow T k t - L.μ k * T t k
  nonneg : ∀ t, 0 ≤ t → ∀ k, 0 ≤ Q t k
  T_zero : ∀ k, T 0 k = 0
  T_mono : ∀ k, MonotoneOn (fun t => T t k) (Ici 0)
  idle_mono : ∀ i, MonotoneOn (L.idle T i) (Ici 0)

/-- `x` is constant on each nonnegative closed interval where `pos` holds throughout. -/
def ConstantWhile (x : ℝ → ℝ) (pos : ℝ → Prop) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, pos u) → x t = x s

/-- Work-conserving fluid equations (1.8)–(1.13). -/
def IsWorkConserving (Q T : ℝ → Fin K → ℝ) : Prop :=
  L.IsFluidSolution Q T ∧
    ∀ i, ConstantWhile (L.idle T i) (fun u => 0 < ∑ k ∈ L.C i, Q u k)

/-- Classes at the station of `k` with at least as high a priority as `k`. -/
def H (π : Equiv.Perm (Fin K)) (k : Fin K) : Finset (Fin K) :=
  Finset.univ.filter (fun l => L.σ l = L.σ k ∧ π l ≤ π k)

/-- Service allocated to the top priority set through class `k`. -/
noncomputable def Tplus (π : Equiv.Perm (Fin K)) (T : ℝ → Fin K → ℝ)
    (k : Fin K) (t : ℝ) : ℝ := ∑ l ∈ L.H π k, T t l

/-- Capacity not allocated to the top priority set through class `k`. -/
noncomputable def Uplus (π : Equiv.Perm (Fin K)) (T : ℝ → Fin K → ℝ)
    (k : Fin K) (t : ℝ) : ℝ := t - L.Tplus π T k t

/-- Immediate volume in the top priority set through class `k`. -/
noncomputable def Wplus (π : Equiv.Perm (Fin K)) (Q : ℝ → Fin K → ℝ)
    (k : Fin K) (t : ℝ) : ℝ := ∑ l ∈ L.H π k, L.m l * Q t l

/-- Preemptive-resume priority fluid model, (1.8)–(1.12) and (4.4). -/
def IsPrioritySolution (π : Equiv.Perm (Fin K)) (Q T : ℝ → Fin K → ℝ) : Prop :=
  L.IsFluidSolution Q T ∧
    ∀ k, ConstantWhile (L.Uplus π T k) (fun u => 0 < L.Wplus π Q k u)

/-- Outflow rate at a regular point, (4.5). -/
noncomputable def outRate (dT : Fin K → ℝ) (k : Fin K) : ℝ := L.μ k * dT k

/-- Inflow rate at a regular point, (4.5), including the unit external arrival rate. -/
noncomputable def inRate (dT : Fin K → ℝ) (k : Fin K) : ℝ :=
  if h : (k : ℕ) = 0 then 1
  else L.outRate dT ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩

/-- The reciprocal of the maximum nominal station workload, p. 125. -/
noncomputable def lamHat : ℝ := 1 / ⨆ i : Fin I, L.ρ i

end ReentrantLine

end DaiWeissFluid.LBFS


