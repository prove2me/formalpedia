-- Prove2me | Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
-- name    : DaiWeissFluid_LuKumar_FluidModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:30:39.965316+00:00
-- url     : https://prove2.me/theorems/f25d7e23-ee0e-4b5d-a977-a879be21006b
-- title:
--   Reentrant-line fluid equations, work conservation, and priority rule
-- statement:
--   A **reentrant line** has a fixed route through $K$ customer classes and $I$ single-server stations. Class $k$ uses station $\sigma(k)$ and has positive mean service time $m_k$, hence service rate $\mu_k=1/m_k$. The **constituency** $C_i$ is the set of classes served at station $i$, and its nominal workload is $\rho_i=\sum_{k\in C_i}m_k$. The external arrival rate is one.
--
--   A **fluid solution** consists of nonnegative class contents $Q_k(t)$ and cumulative service amounts $T_k(t)$ for $t\ge0$. It satisfies the flow equations
--   $$Q_k(t)=Q_k(0)+\mu_{k-1}T_{k-1}(t)-\mu_kT_k(t),$$
--   with $\mu_0T_0(t)=t$, $T_k(0)=0$, nondecreasing $T_k$, and nondecreasing station idle time $U_i(t)=t-\sum_{k\in C_i}T_k(t)$. The **work-conserving** condition says $U_i$ can increase only while the total content at station $i$ is zero.
--
--   For a priority permutation $\pi$, lower $\pi(k)$ means higher priority. Put $H_k=\{l\in C_{\sigma(k)}:\pi(l)\le\pi(k)\}$, $U_k^+(t)=t-\sum_{l\in H_k}T_l(t)$, and $W_k^+(t)=\sum_{l\in H_k}m_lQ_l(t)$. A **priority solution** also requires $U_k^+$ to increase only while $W_k^+=0$. Stability in the sense of Definition 1.3 (one $\delta>0$ empties every solution of initial total content one by time $\delta$, and it stays empty thereafter) is not declared here: the theorems use `FluidStable` from the shared module `DaiWeissFluid.ThreeBuffer.FluidModel`, which this module imports.
--
--   These definitions are shared infrastructure for the chapter’s instability and stability statements.
--
--   **Formalization Note** Classes and stations are numbered from zero in Lean: paper class $k$ is Lean index $k-1$. Paths are total real-time functions, with the fluid equations imposed for $t\ge0$. The paper’s “increases only when empty” conditions (1.13) and (4.4) are represented by constancy on intervals of positive content.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), pp. 115–120 and 122–123, Definitions 1.2, 1.3, equations (1.8)–(1.13), (2.1), (4.1)–(4.4)

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel

namespace DaiWeissFluid.LuKumar

open Set

/-- A reentrant line with `K` consecutive classes and `I` stations. Class `k` is served at `σ k` and has mean service time `m k`. -/
structure ReentrantLine (I K : ℕ) where
  σ : Fin K → Fin I
  m : Fin K → ℝ

namespace ReentrantLine

variable {I K : ℕ} (L : ReentrantLine I K)

/-- The service rate `μ_k = 1/m_k`. -/
noncomputable def μ (k : Fin K) : ℝ := (L.m k)⁻¹

/-- The constituency of station `i`. -/
def C (i : Fin I) : Finset (Fin K) := Finset.univ.filter (fun k => L.σ k = i)

/-- The nominal load `ρ_i`. -/
noncomputable def ρ (i : Fin I) : ℝ := ∑ k ∈ L.C i, L.m k

/-- Inflow to class `k`; outside arrivals into the first class have rate one. -/
noncomputable def inflow (T : ℝ → Fin K → ℝ) (k : Fin K) (t : ℝ) : ℝ :=
  if h : (k : ℕ) = 0 then t
  else L.μ ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ *
    T t ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩

/-- Cumulative busy time of station `i`, (1.11). -/
noncomputable def busy (T : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) : ℝ :=
  ∑ k ∈ L.C i, T t k

/-- Cumulative idle time of station `i`, (1.12). -/
noncomputable def idle (T : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) : ℝ :=
  t - L.busy T i t

/-- Immediate workload at station `i`, (2.1). -/
noncomputable def volume (Q : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) : ℝ :=
  ∑ k ∈ L.C i, L.m k * Q t k

/-- The fluid equations (1.8)–(1.12) on nonnegative time. -/
structure IsFluidSolution (Q T : ℝ → Fin K → ℝ) : Prop where
  flow : ∀ t, 0 ≤ t → ∀ k, Q t k = Q 0 k + L.inflow T k t - L.μ k * T t k
  nonneg : ∀ t, 0 ≤ t → ∀ k, 0 ≤ Q t k
  T_zero : ∀ k, T 0 k = 0
  T_mono : ∀ k, MonotoneOn (fun t => T t k) (Ici 0)
  idle_mono : ∀ i, MonotoneOn (L.idle T i) (Ici 0)

/-- `x` can increase only at times when `pos` fails, in interval form. -/
def ConstantWhile (x : ℝ → ℝ) (pos : ℝ → Prop) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, pos u) → x t = x s

/-- The work-conserving fluid model (1.8)–(1.13). -/
def IsWorkConserving (Q T : ℝ → Fin K → ℝ) : Prop :=
  L.IsFluidSolution Q T ∧
    ∀ i, ConstantWhile (L.idle T i) (fun u => 0 < ∑ k ∈ L.C i, Q u k)

/-- Classes at station `σ k` whose priority is at least that of `k`. -/
def H (π : Equiv.Perm (Fin K)) (k : Fin K) : Finset (Fin K) :=
  Finset.univ.filter (fun l => L.σ l = L.σ k ∧ π l ≤ π k)

/-- Cumulative service for the priority set `H_k`, (4.1). -/
noncomputable def Tplus (π : Equiv.Perm (Fin K)) (T : ℝ → Fin K → ℝ)
    (k : Fin K) (t : ℝ) : ℝ := ∑ l ∈ L.H π k, T t l

/-- Unused capacity for the priority set `H_k`, (4.2). -/
noncomputable def Uplus (π : Equiv.Perm (Fin K)) (T : ℝ → Fin K → ℝ)
    (k : Fin K) (t : ℝ) : ℝ := t - L.Tplus π T k t

/-- Immediate workload in the priority set `H_k`, (4.3). -/
noncomputable def Wplus (π : Equiv.Perm (Fin K)) (Q : ℝ → Fin K → ℝ)
    (k : Fin K) (t : ℝ) : ℝ := ∑ l ∈ L.H π k, L.m l * Q t l

/-- The preemptive-resume priority fluid model, (1.8)–(1.12) and (4.4). -/
def IsPrioritySolution (π : Equiv.Perm (Fin K)) (Q T : ℝ → Fin K → ℝ) : Prop :=
  L.IsFluidSolution Q T ∧
    ∀ k, ConstantWhile (L.Uplus π T k) (fun u => 0 < L.Wplus π Q k u)

end ReentrantLine

end DaiWeissFluid.LuKumar


