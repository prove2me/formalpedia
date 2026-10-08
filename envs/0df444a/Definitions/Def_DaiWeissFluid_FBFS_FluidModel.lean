-- Prove2me | Definitions.Def_DaiWeissFluid_FBFS_FluidModel
-- name    : DaiWeissFluid_FBFS_FluidModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:28:44.573869+00:00
-- url     : https://prove2.me/theorems/39913a10-80f2-441e-ba6c-a77e85c60995
-- title:
--   Reentrant line, fluid model (1.8)–(1.13), priority condition (4.4), rates (4.5), FBFS, emptying time, stability (Definition 1.3)
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
--   **Priority disciplines (§4).** A buffer priority discipline is a permutation $\pi$ of the classes; class $k$ has priority over class $l$ when $\pi(k) < \pi(l)$. Let $H_k = \{l \in C_{\sigma(k)} : \pi(l) \le \pi(k)\}$, $T_k^+(t) = \sum_{l\in H_k} T_l(t)$ (4.1), $U_k^+(t) = t - T_k^+(t)$ (4.2) and $W_k^+(t) = \sum_{l \in H_k} m_l Q_l(t)$ (4.3). The fluid model of the preemptive-resume priority discipline $\pi$ consists of (1.8)–(1.12) together with (4.4): $U_k^+$ increases only at times when $W_k^+(t) = 0$. The **First-Buffer-First-Served** (FBFS) discipline is $\pi(k) = k$ (Definition 4.1).
--
--   **Rates (4.5).** At a regular time $t$, where every $T_k$ has a derivative $\dot T_k(t)$, the out-flow rate of buffer $k$ is $d_k(t) = \mu_k \dot T_k(t)$ and its in-flow rate is $a_k(t) = \mu_{k-1}\dot T_{k-1}(t)$, which is $1$ for the first class.
--
--   **Emptying time.** For FBFS, the module defines the constant of the proof of Theorem 4.3,
--   $$
--   \delta = \sum_{k=1}^{K} m_k\,\frac{\prod_{l=1}^{k-1}\bigl(1 - \sum_{j \in H_l\setminus\{l\}} m_j\bigr)}{\prod_{l=1}^{k}\bigl(1 - \sum_{j\in H_l} m_j\bigr)} .
--   $$
--
--   **Stability (Definition 1.3).** A fluid model is stable if there is a time $\delta > 0$ such that every solution with $|Q(0)| = \sum_k Q_k(0) = 1$ has $Q_k(t) = 0$ for all $t \ge \delta$ and all $k$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Classes and stations are `Fin K` and `Fin I`, 0-based: the paper's class $k$ is Lean index $k-1$. Paths are total functions `ℝ → Fin K → ℝ`, and every equation is imposed only on $t \ge 0$. The conditions "$U$ increases only when the content is zero" in (1.13) and (4.4) are encoded by `ConstantWhile`: $U$ is constant on every interval $[s,t] \subseteq [0,\infty)$ throughout which the content stays positive. For continuous paths this is equivalent to the paper's Stieltjes form $\int_0^\infty W_k^+(t)\,dU_k^+(t) = 0$. Lipschitz continuity is not imposed, since it follows from (1.10)–(1.12). The rates take the derivatives `dT k` as an argument. FBFS is `fbfs K = Equiv.refl`. In `fbfsEmptyingTime` the products run over $l < k$ and $l \le k$ in 0-based indices, and $H_l\setminus\{l\}$ is `(H l).erase l`. `FluidStable P` (Definition 1.3) is the series' shared definition `DaiWeissFluid.ThreeBuffer.FluidStable`, imported from the shared module rather than redeclared here; it quantifies over the solution pairs $(Q,T)$ satisfying `P` with $\sum_k Q_k(0) = 1$.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), pp. 115–119, 120, 122–124, Definitions 1.2, 1.3, 4.1, (1.7)–(1.13), (2.1), (4.1)–(4.5), proof of Theorem 4.3

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel

namespace DaiWeissFluid.FBFS

open Set

/-- A reentrant line (§1): `K` classes (stages of the single route) and `I` stations; class `k` is
served at station `σ k` with mean service time `m k`. Classes and stations are 0-based: the paper's
class `k` is `⟨k - 1, _⟩`, and the route is `0 → 1 → ⋯ → K - 1 → exit`. -/
structure ReentrantLine (I K : ℕ) where
  σ : Fin K → Fin I
  m : Fin K → ℝ

/-- The First-Buffer-First-Served ranking (Definition 4.1, p. 123): `π(k) = k`, so a class has
priority over every later class served at the same station. -/
def fbfs (K : ℕ) : Equiv.Perm (Fin K) := Equiv.refl (Fin K)

namespace ReentrantLine

variable {I K : ℕ} (L : ReentrantLine I K)

/-- `μ_k = 1/m_k` (p. 117). -/
noncomputable def μ (k : Fin K) : ℝ := (L.m k)⁻¹

/-- The constituency `C_i = {k : σ(k) = i}` (p. 116). -/
def C (i : Fin I) : Finset (Fin K) := Finset.univ.filter (fun k => L.σ k = i)

/-- The nominal workload `ρ_i = ∑_{k ∈ C_i} m_k` (p. 116). -/
noncomputable def ρ (i : Fin I) : ℝ := ∑ k ∈ L.C i, L.m k

/-- The in-flow term `μ_{k-1} T_{k-1}(t)` of (1.8), with the convention `μ₀ T₀(t) = t`. -/
noncomputable def inflow (T : ℝ → Fin K → ℝ) (k : Fin K) (t : ℝ) : ℝ :=
  if h : (k : ℕ) = 0 then t
  else L.μ ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ * T t ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩

/-- `B_i(t)` (1.11). -/
noncomputable def busy (T : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) : ℝ := ∑ k ∈ L.C i, T t k

/-- `U_i(t) = t - B_i(t)` (1.12). -/
noncomputable def idle (T : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) : ℝ := t - L.busy T i t

/-- The immediate volume `W_i(t) = ∑_{k ∈ C_i} m_k Q_k(t)` (2.1). -/
noncomputable def volume (Q : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) : ℝ := ∑ k ∈ L.C i, L.m k * Q t k

/-- (1.8)–(1.12): a fluid model solution on `[0, ∞)`. -/
structure IsFluidSolution (Q T : ℝ → Fin K → ℝ) : Prop where
  flow : ∀ t, 0 ≤ t → ∀ k, Q t k = Q 0 k + L.inflow T k t - L.μ k * T t k   -- (1.8)
  nonneg : ∀ t, 0 ≤ t → ∀ k, 0 ≤ Q t k                                      -- (1.9)
  T_zero : ∀ k, T 0 k = 0                                                   -- (1.10)
  T_mono : ∀ k, MonotoneOn (fun t => T t k) (Ici 0)                         -- (1.10)
  idle_mono : ∀ i, MonotoneOn (L.idle T i) (Ici 0)                          -- (1.11)–(1.12)

/-- "`x` increases only at times when `pos` fails": `x` is constant on every interval
`[s, t] ⊆ [0, ∞)` throughout which `pos` holds. -/
def ConstantWhile (x : ℝ → ℝ) (pos : ℝ → Prop) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, pos u) → x t = x s

/-- The work-conserving fluid model (1.8)–(1.13). -/
def IsWorkConserving (Q T : ℝ → Fin K → ℝ) : Prop :=
  L.IsFluidSolution Q T ∧
    ∀ i, ConstantWhile (L.idle T i) (fun u => 0 < ∑ k ∈ L.C i, Q u k)       -- (1.13)

/-- `H_k = {l ∈ C_{σ(k)} : π(l) ≤ π(k)}` (p. 122). -/
def H (π : Equiv.Perm (Fin K)) (k : Fin K) : Finset (Fin K) :=
  Finset.univ.filter (fun l => L.σ l = L.σ k ∧ π l ≤ π k)

/-- `T_k⁺(t)` (4.1). -/
noncomputable def Tplus (π : Equiv.Perm (Fin K)) (T : ℝ → Fin K → ℝ) (k : Fin K) (t : ℝ) : ℝ :=
  ∑ l ∈ L.H π k, T t l

/-- `U_k⁺(t) = t - T_k⁺(t)` (4.2). -/
noncomputable def Uplus (π : Equiv.Perm (Fin K)) (T : ℝ → Fin K → ℝ) (k : Fin K) (t : ℝ) : ℝ :=
  t - L.Tplus π T k t

/-- `W_k⁺(t) = ∑_{l ∈ H_k} m_l Q_l(t)` (4.3). -/
noncomputable def Wplus (π : Equiv.Perm (Fin K)) (Q : ℝ → Fin K → ℝ) (k : Fin K) (t : ℝ) : ℝ :=
  ∑ l ∈ L.H π k, L.m l * Q t l

/-- The fluid model of the preemptive-resume priority discipline `π`: (1.8)–(1.12) and (4.4). -/
def IsPrioritySolution (π : Equiv.Perm (Fin K)) (Q T : ℝ → Fin K → ℝ) : Prop :=
  L.IsFluidSolution Q T ∧
    ∀ k, ConstantWhile (L.Uplus π T k) (fun u => 0 < L.Wplus π Q k u)      -- (4.4)

/-- The out-flow rate `d_k = μ_k Ṫ_k` of (4.5), given the derivatives `dT k = Ṫ_k(t)` at a
regular point. -/
noncomputable def outRate (dT : Fin K → ℝ) (k : Fin K) : ℝ := L.μ k * dT k

/-- The in-flow rate `a_k = μ_{k-1} Ṫ_{k-1}` of (4.5), with the convention `μ₀ Ṫ₀ = 1`
(`T₀(t) = t`): the first class receives the exogenous inflow at rate one. -/
noncomputable def inRate (dT : Fin K → ℝ) (k : Fin K) : ℝ :=
  if h : (k : ℕ) = 0 then 1
  else L.outRate dT ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩

/-- The emptying time `δ` of the proof of Theorem 4.3 (p. 124), for the FBFS ranking
(`π = fbfs K`), in 0-based indices:
`δ = ∑_k m_k ∏_{l<k} (1 - ∑_{j ∈ H_l \ {l}} m_j) / ∏_{l≤k} (1 - ∑_{j ∈ H_l} m_j)`. -/
noncomputable def fbfsEmptyingTime : ℝ :=
  ∑ k : Fin K, L.m k *
    ((∏ l ∈ Finset.univ.filter (fun l : Fin K => l < k),
        (1 - ∑ j ∈ (L.H (fbfs K) l).erase l, L.m j)) /
      ∏ l ∈ Finset.univ.filter (fun l : Fin K => l ≤ k),
        (1 - ∑ j ∈ L.H (fbfs K) l, L.m j))

end ReentrantLine

end DaiWeissFluid.FBFS


