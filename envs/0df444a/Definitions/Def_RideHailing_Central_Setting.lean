-- Prove2me | Definitions.Def_RideHailing_Central_Setting
-- name    : RideHailing_Central_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:39:50.22181+00:00
-- url     : https://prove2.me/theorems/c2a2dd51-9816-4a94-8815-0b7f4b2ef4cd
-- title:
--   §2.1–§2.5 — the two-location ride-hailing fluid model under centralized control: Assumptions 1–3, C_C(n) (12a)–(12c), Π, π (12d), (13)–(14), the two-step selection and π_C(n)
-- statement:
--   This file sets up the steady-state fluid model of a ride-hailing platform with two locations of Afèche, Liu and Maglaras, in the centralized-control regime $C$.
--
--   **Primitives.** There are four routes $lk$ with $l,k\in\{1,2\}$. Route $lk$ has potential demand rate $\Lambda_{lk}$ and travel time $t_{lk}$. The platform charges a price $p$ per unit of travel time and keeps the share $\gamma$; drivers keep $\bar\gamma p$ per unit of busy time, where $\bar\gamma=1-\gamma$, and pay a driving cost rate $c$. There is a pool of $N$ potential drivers, whose opportunity cost rates are drawn from a distribution with cumulative distribution function $F$.
--
--   **Standing assumptions.** Every theorem of the mission assumes:
--   1. $0<\gamma<1$ and $\bar\gamma p-c>0$;
--   2. Assumption 1 (demand imbalance): $0<\Lambda_{12}<\Lambda_{21}$, and $\Lambda_{11},\Lambda_{22}\ge 0$;
--   3. Assumption 2 (positive profit from repositioning): $c\,t_{12}<t_{21}(\bar\gamma p-c)$ and $c\,t_{21}<t_{12}(\bar\gamma p-c)$;
--   4. Assumption 3: $F$ is the CDF of a probability measure on $\mathbb R$, $F$ is continuous, strictly increasing on $[0,\bar c_o]$ with $\bar c_o\ge p-c$, $F(0)=0$ and $F(\bar c_o)=1$;
--   5. $t_{lk}>0$ for all four routes, $p>0$, $N>0$ and $c>0$.
--
--   **Derived constants.** The offered loads are $S_{lk}=\Lambda_{lk}t_{lk}$ and $\bar S=\sum_{lk}S_{lk}$; the zone thresholds (17) are
--   $$n^C_1:=\bar S-(\Lambda_{21}-\Lambda_{12})t_{21},\qquad n^C_2:=\bar S+(\Lambda_{21}-\Lambda_{12})t_{12}.$$
--
--   **Allocations.** A capacity allocation $(s,r,q)$ consists of service capacities $s_{lk}$, repositioning capacities $r_{12},r_{21}$ and queueing capacities $q_1,q_2$, with totals $\bar s=\sum_{lk}s_{lk}$, $\bar r=r_{12}+r_{21}$, $\bar q=q_1+q_2$. For a driver capacity $n$, the set $\mathcal C_C(n)$ consists of the allocations satisfying
--   $$\frac{s_{12}+r_{12}}{t_{12}}=\frac{s_{21}+r_{21}}{t_{21}},\qquad \bar s+\bar r+\bar q=n,\qquad 0\le s\le S,\ r\ge0,\ q\ge0. \tag{12a–c}$$
--
--   **Objectives.** The platform's revenue rate is $\Pi(s)=\gamma p\bar s$ and the per-driver profit rate is
--   $$\pi(s,r,n)=\frac{(\bar\gamma p-c)\bar s-c\bar r}{n}. \tag{12d}$$
--
--   **Two-step objects.** $\Pi_C(n)$ is the supremum of $\Pi(s)$ over $\mathcal C_C(n)$ (problem (14)); $\mathcal C^*_C(n)$ is the set of maximizers of $\Pi$ over $\mathcal C_C(n)$; the *selected* allocations are the elements of $\mathcal C^*_C(n)$ that maximize $\pi(\cdot,\cdot,n)$ over $\mathcal C^*_C(n)$; and $\pi_C(n)$ is the supremum of $\pi(s,r,n)$ over $\mathcal C^*_C(n)$, i.e. the per-driver profit of a selected allocation.
--
--   **Problem (13).** A tuple $(s,r,q,n)$ is feasible for (13) when $n>0$, $(s,r,q)\in\mathcal C_C(n)$ and the participation equation $n=NF(\pi(s,r,n))$ (12e) holds.
--
--   These objects are the vocabulary of every statement of the mission: Proposition 1, the closed form (18), Lemma 1 and Corollary 1.
--
--   **Formalization Note** $F$ is `ProbabilityTheory.cdf μ` for a measure `μ` on $\mathbb R$ that the standing assumptions make a probability measure. Routes are named fields, not indices. $\Pi_C(n)$ and $\pi_C(n)$ are defined as `sSup`s; the theorems state attainment with `IsGreatest` or membership in the optimal sets, so the supremum convention is never relied on. $\pi_C$ is defined through the allocation problem, not by its closed form (18). The requirement $n>0$ in (13) is added because (12d) divides by $n$. The additions $t_{lk}>0$, $\Lambda_{11},\Lambda_{22}\ge0$, $p,N,c>0$ and continuity of $F$ are the paper's implicit conventions (travel times, rates, a driving cost, "a common continuous distribution").
-- source:
--   Afèche, Liu, Maglaras, Ride-Hailing Networks with Strategic Drivers: The Impact of Platform Control Capabilities on Performance, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2023.1221, pp. 5–8, Assumptions 1–3, (9), (12a)–(12e), (13)–(14), (17)

import Mathlib

namespace RideHailing.Central

open MeasureTheory ProbabilityTheory

/-- The primitives of the two-location ride-hailing fluid model (§2.1): potential demand rates
`Λlk` and travel times `tlk` of the four routes `lk`, the price `p` per unit of travel time, the
platform commission `γ`, the driving cost rate `c`, the driver pool size `N`, the upper end `cbar`
(the paper's `c̄_o`) of the support of the opportunity-cost distribution, and that distribution
`μ` itself, whose cumulative distribution function is the paper's `F`. -/
structure Model where
  Λ11 : ℝ
  Λ12 : ℝ
  Λ21 : ℝ
  Λ22 : ℝ
  t11 : ℝ
  t12 : ℝ
  t21 : ℝ
  t22 : ℝ
  p : ℝ
  γ : ℝ
  c : ℝ
  N : ℝ
  cbar : ℝ
  μ : Measure ℝ

namespace Model

variable (M : Model)

/-- The drivers' share `γ̄ = 1 − γ` of the fare (p. 5). -/
def gbar : ℝ := 1 - M.γ

/-- The opportunity-cost CDF `F` (Assumption 3). -/
noncomputable def F : ℝ → ℝ := fun x => cdf M.μ x

/-- Standing assumptions of §2.1 (p. 5): `γ ∈ (0,1)`, `γ̄p − c > 0`, Assumptions 1–3, and the
disclosed implicit conventions (positive travel times, nonnegative local demand rates, `p > 0`,
`N > 0`, `c > 0`, `F` the CDF of a probability measure). -/
structure Standing : Prop where
  γ_pos : 0 < M.γ
  γ_lt_one : M.γ < 1
  profit_pos : 0 < M.gbar * M.p - M.c
  /-- Assumption 1 (Demand Imbalance). -/
  Λ12_pos : 0 < M.Λ12
  Λ12_lt_Λ21 : M.Λ12 < M.Λ21
  Λ11_nonneg : 0 ≤ M.Λ11
  Λ22_nonneg : 0 ≤ M.Λ22
  /-- Assumption 2 (Positive Profit from Repositioning). -/
  assm2_12 : M.c * M.t12 < M.t21 * (M.gbar * M.p - M.c)
  assm2_21 : M.c * M.t21 < M.t12 * (M.gbar * M.p - M.c)
  /-- Assumption 3 (Opportunity Cost Distribution), for `F = cdf μ`, `μ` a probability
  measure with a continuous distribution function. -/
  prob : IsProbabilityMeasure M.μ
  F_continuous : Continuous M.F
  F_strictMonoOn : StrictMonoOn M.F (Set.Icc 0 M.cbar)
  cbar_ge : M.p - M.c ≤ M.cbar
  F_zero : M.F 0 = 0
  F_cbar : M.F M.cbar = 1
  /-- Disclosed implicit conventions. -/
  t11_pos : 0 < M.t11
  t12_pos : 0 < M.t12
  t21_pos : 0 < M.t21
  t22_pos : 0 < M.t22
  p_pos : 0 < M.p
  N_pos : 0 < M.N
  c_pos : 0 < M.c

/-- Offered loads `S_lk = Λ_lk t_lk` (9). -/
def S11 : ℝ := M.Λ11 * M.t11
def S12 : ℝ := M.Λ12 * M.t12
def S21 : ℝ := M.Λ21 * M.t21
def S22 : ℝ := M.Λ22 * M.t22

/-- Total offered load `S̄ = Σ_lk S_lk`. -/
def Sbar : ℝ := M.S11 + M.S12 + M.S21 + M.S22

/-- `n^C_1 := S̄ − (Λ21 − Λ12) t21` (17). -/
def nC1 : ℝ := M.Sbar - (M.Λ21 - M.Λ12) * M.t21

/-- `n^C_2 := S̄ + (Λ21 − Λ12) t12` (17). -/
def nC2 : ℝ := M.Sbar + (M.Λ21 - M.Λ12) * M.t12

end Model

/-- A capacity allocation `(s, r, q)` (§2.4): service capacities `s_lk` on the four routes,
repositioning capacities `r12`, `r21`, and queueing capacities `q1`, `q2`. -/
structure Alloc where
  s11 : ℝ
  s12 : ℝ
  s21 : ℝ
  s22 : ℝ
  r12 : ℝ
  r21 : ℝ
  q1 : ℝ
  q2 : ℝ

namespace Alloc

variable (x : Alloc)

/-- Total service capacity `s̄`. -/
def sbar : ℝ := x.s11 + x.s12 + x.s21 + x.s22
/-- Total repositioning capacity `r̄ = r12 + r21`. -/
def rbar : ℝ := x.r12 + x.r21
/-- Total queueing capacity `q̄ = q1 + q2`. -/
def qbar : ℝ := x.q1 + x.q2

end Alloc

namespace Model

variable (M : Model)

/-- `(s, r, q) ∈ C_C(n)`: constraints (12a)–(12c). -/
def InCC (n : ℝ) (x : Alloc) : Prop :=
  (x.s12 + x.r12) / M.t12 = (x.s21 + x.r21) / M.t21 ∧
  x.sbar + x.rbar + x.qbar = n ∧
  (0 ≤ x.s11 ∧ x.s11 ≤ M.S11) ∧ (0 ≤ x.s12 ∧ x.s12 ≤ M.S12) ∧
  (0 ≤ x.s21 ∧ x.s21 ≤ M.S21) ∧ (0 ≤ x.s22 ∧ x.s22 ≤ M.S22) ∧
  0 ≤ x.r12 ∧ 0 ≤ x.r21 ∧ 0 ≤ x.q1 ∧ 0 ≤ x.q2

/-- Platform revenue `Π(s) = γ p s̄` (p. 7). -/
def Rev (x : Alloc) : ℝ := M.γ * M.p * x.sbar

/-- Per-driver profit `π(s, r, n) = ((γ̄p − c) s̄ − c r̄)/n` (12d). -/
noncomputable def prof (x : Alloc) (n : ℝ) : ℝ :=
  ((M.gbar * M.p - M.c) * x.sbar - M.c * x.rbar) / n

/-- `Π_C(n) := max {Π(s) : (s, r, q) ∈ C_C(n)}` (14), as a supremum. -/
noncomputable def PiC (n : ℝ) : ℝ := sSup (M.Rev '' {x | M.InCC n x})

/-- `C*_C(n)`: the revenue-maximizing allocations of capacity `n` (§2.5). -/
def OptC (n : ℝ) : Set Alloc :=
  {x | M.InCC n x ∧ ∀ y, M.InCC n y → M.Rev y ≤ M.Rev x}

/-- The two-step selection of §2.5: elements of `C*_C(n)` maximizing the per-driver profit. -/
def SelC (n : ℝ) : Set Alloc :=
  {x | x ∈ M.OptC n ∧ ∀ y ∈ M.OptC n, M.prof y n ≤ M.prof x n}

/-- `π_C(n) := π(s_C(n), r_C(n), n)`: the largest per-driver profit over `C*_C(n)`. -/
noncomputable def piC (n : ℝ) : ℝ := sSup ((fun x => M.prof x n) '' M.OptC n)

/-- Feasibility for problem (13) in regime C: positive capacity `n`, `(s, r, q) ∈ C_C(n)` and
the participation equation (12e) `n = N F(π(s, r, n))`. -/
def Feas13 (x : Alloc) (n : ℝ) : Prop :=
  0 < n ∧ M.InCC n x ∧ n = M.N * M.F (M.prof x n)

end Model

end RideHailing.Central


