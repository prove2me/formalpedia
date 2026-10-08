-- Prove2me | Definitions.Def_DaiWeissFluid_KellyType_FluidModel
-- name    : DaiWeissFluid_KellyType_FluidModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:31:29.038662+00:00
-- url     : https://prove2.me/theorems/f5fc0510-ae92-4efb-8f70-99702e02d8ff
-- title:
--   Reentrant line, fluid model (1.8)–(1.13), priority condition (4.4), stability (Definition 1.3)
-- statement:
--   A **reentrant line** has $I$ stations and $K$ classes. Every customer follows the same route: it enters in class $1$, moves from class $k$ to class $k+1$ on completing service, and leaves after class $K$. Class $k$ is served at station $\sigma(k)$ with mean service time $m_k$, and $\mu_k = 1/m_k$. The **constituency** of station $i$ is $C_i = \{k : \sigma(k) = i\}$, and its **nominal workload** is $\rho_i = \sum_{k \in C_i} m_k$. The arrival rate is normalized to $1$.
--
--   A **fluid model solution** is a pair $(Q, T)$ of paths $Q(t) = (Q_1(t),\dots,Q_K(t))$ (fluid levels) and $T(t) = (T_1(t),\dots,T_K(t))$ (cumulative allocated service time) satisfying, for $t \ge 0$,
--
--   $$
--   \begin{aligned}
--   &Q_k(t) = Q_k(0) + \mu_{k-1}T_{k-1}(t) - \mu_k T_k(t), \qquad \mu_0 T_0(t) = t, &(1.8)\\
--   &Q_k(t) \ge 0, &(1.9)\\
--   &T_k(0) = 0,\ T_k \text{ nondecreasing}, &(1.10)\\
--   &B_i(t) = \textstyle\sum_{k\in C_i} T_k(t), \quad U_i(t) = t - B_i(t) \text{ nondecreasing}. &(1.11)\text{–}(1.12)
--   \end{aligned}
--   $$
--
--   It is **work-conserving** if in addition (1.13) the idle time $U_i$ increases only at times when the station content $\sum_{k \in C_i} Q_k(t)$ is $0$. The **immediate volume** at station $i$ is $W_i(t) = \sum_{k\in C_i} m_k Q_k(t)$ (2.1).
--
--   For a priority permutation $\pi$ of the classes (smaller $\pi$ = higher priority), $H_k = \{l \in C_{\sigma(k)} : \pi(l) \le \pi(k)\}$, $T_k^+ = \sum_{l\in H_k} T_l$ (4.1), $U_k^+(t) = t - T_k^+(t)$ (4.2), $W_k^+ = \sum_{l \in H_k} m_l Q_l$ (4.3), and the preemptive-resume priority fluid model requires (4.4): $U_k^+$ increases only when $W_k^+ = 0$.
--
--   A set of fluid solutions is **stable** (Definition 1.3) if there is $\delta > 0$ such that every solution in it with $|Q(0)| = \sum_k Q_k(0) = 1$ has $Q_k(t) = 0$ for all $t \ge \delta$ and all $k$.
--
--   These objects are the common language of all statements of the paper about fluid models.
--
--   **Formalization Note** Classes and stations are 0-based (`Fin K`, `Fin I`): the paper's class $k$ is Lean `k - 1`, station $i$ is Lean `i - 1`. Paths are total functions `ℝ → Fin K → ℝ`, and every equation is imposed only for $t \ge 0$. Conditions (1.13) and (4.4) are stated in interval form (`ConstantWhile`): the idle process is constant on every interval $[s,t] \subseteq [0,\infty)$ throughout which the relevant content is positive; for the continuous nondecreasing $U_i$ and the continuous nonnegative content this is equivalent to the paper's $\int_0^\infty (\sum_{k \in C_i} Q_k)\,dU_i = 0$. Lipschitz continuity is not assumed; it follows from (1.10)–(1.12). Positivity of the $m_k$ is not part of the structure; every theorem using it states it as a hypothesis. The paper's "(1.13) xU_i(·) increases only…" has a stray "x"; the condition is about $U_i$.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), pp. 115–119, 120, 122–123, Definitions 1.2, 1.3, (1.7), (1.8)–(1.13), (2.1), (4.1)–(4.4)

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel

namespace DaiWeissFluid.KellyType

open Set

/-- A reentrant line (§1): `K` classes (stages of the single route) and `I` stations; class `k` is
served at station `σ k` with mean service time `m k`. Classes and stations are 0-based: the paper's
class `k` is `⟨k - 1, _⟩`, and the route is `0 → 1 → ⋯ → K - 1 → exit`. -/
structure ReentrantLine (I K : ℕ) where
  σ : Fin K → Fin I
  m : Fin K → ℝ

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

end ReentrantLine

end DaiWeissFluid.KellyType


