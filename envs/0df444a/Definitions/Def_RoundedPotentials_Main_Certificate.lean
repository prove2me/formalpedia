-- Prove2me | Definitions.Def_RoundedPotentials_Main_Certificate
-- name    : RoundedPotentials_Main_Certificate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T08:33:22.858621+00:00
-- url     : https://prove2.me/theorems/5be60bb1-d44e-4570-b838-1d37c37f481a
-- title:
--   Edge-list inputs, clipped flows, signed excess and certificate conditions
-- statement:
--   Let the vertices be $V=\{0,\ldots,n-1\}$. An input lists distinct directed pairs without self-loops, each with a nonnegative integer capacity at most the integer $W$. Antiparallel edges and listed zero capacities are allowed. Absent pairs have capacity zero. The input builds the published directed network, with the listed pairs as arcs. Write $c_{uv}$ for its capacity.
--
--   For a real potential vector $y$, define clipping, its induced assignment, and signed excess by
--   $$
--   \operatorname{clip}(z)=\min(1,\max(0,z)),\qquad f^y_{uv}=c_{uv}\operatorname{clip}(y_u-y_v),\qquad
--   \operatorname{ex}_f(v)=\sum_u f_{vu}-\sum_u f_{uv}.
--   $$
--   Capacity feasibility means $0\le f_{uv}\le c_{uv}$ on every pair. A prescribed excess vector $b$ is realized when $\operatorname{ex}_f(v)=b_v$ at every vertex. For terminals $s,t$ and value $p$, put $b_v=p(1[v=s]-1[v=t])$.
--
--   For an interval parameter $N$, certificate checks require $y_v\in[0,N-1]\cup[N,2N-1]$, $y_s\ge N$, $y_t\le N-1$, and $|\operatorname{ex}_{f^y}(v)-b_v|\le1/(8N)$. The grid denominator is $Q(N,W)=32N^2W$; indices $i_v$ represent $y_v=i_v/Q$. Downward rounding uses $i_v=\lfloor Qx_v\rfloor$. IndexRange is precisely $0\le i_v\le(2N-1)Q$.
--
--   These are operational definitions; capacity feasibility, existence, and correctness are subsequent theorem targets. Maximum-flow equality means an attained greatest flow value, using the published IsFlow predicate. Binary length is $1+\lfloor\log_2|i|\rfloor$, with length one for zero. No maximum-flow oracle enters the verifier.
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), pp. 4, 11–13, Box 1, Definitions 2.1–2.2, eqs. (1), (2), (6), (7); pp.15–17, eq. (10)

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network

namespace RoundedPotentials.Main
open scoped BigOperators

/-- The input promise is exactly §2: distinct loopless ordered pairs, capacities in [0,W]. -/
structure Instance (n W : ℕ) where
  edges : List (Fin n × Fin n × ℕ)
  noLoops : ∀ e ∈ edges, e.1 ≠ e.2.1
  uniquePairs : (edges.map (fun e => (e.1, e.2.1))).Nodup
  bounded : ∀ e ∈ edges, e.2.2 ≤ W

def capNat {n W : ℕ} (I : Instance n W) (u v : Fin n) : ℕ :=
  (I.edges.map (fun e => if e.1 = u ∧ e.2.1 = v then e.2.2 else 0)).sum

def network {n W : ℕ} (I : Instance n W) : FlowsNetworks.MaxFlow.Network (Fin n) where
  arcs := (I.edges.map (fun e => (e.1, e.2.1))).toFinset
  loopless := by
    intro a ha
    simp only [List.mem_toFinset, List.mem_map] at ha
    obtain ⟨e, he, rfl⟩ := ha
    exact I.noLoops e he
  cap u v := (capNat I u v : ℝ)
  cap_nonneg := by intros; exact Nat.cast_nonneg _

abbrev Assignment (n : ℕ) := Fin n → Fin n → ℝ

def clip (z : ℝ) : ℝ := min 1 (max 0 z)

noncomputable def induced {n W : ℕ} (I : Instance n W) (y : Fin n → ℝ) : Assignment n :=
  fun u v => (capNat I u v : ℝ) * clip (y u - y v)

noncomputable def excess {n : ℕ} (f : Assignment n) (v : Fin n) : ℝ :=
  (∑ u, f v u) - ∑ u, f u v

def target {n : ℕ} (s t : Fin n) (p : ℝ) (v : Fin n) : ℝ :=
  p * ((if v = s then 1 else 0) - (if v = t then 1 else 0))

def CapacityFeasible {n W : ℕ} (I : Instance n W) (f : Assignment n) : Prop :=
  ∀ u v, 0 ≤ f u v ∧ f u v ≤ (capNat I u v : ℝ)

def HasExcess {n : ℕ} (f : Assignment n) (b : Fin n → ℝ) : Prop :=
  ∀ v, excess f v = b v

def MaxValue {n W : ℕ} (I : Instance n W) (s t : Fin n) (p : ℝ) : Prop :=
  IsGreatest {w : ℝ | ∃ f : Assignment n, FlowsNetworks.MaxFlow.IsFlow (network I) s t f w} p

noncomputable def epsilon (N : ℕ) : ℝ := 1 / (8 * (N : ℝ))

def Intervals {n : ℕ} (N : ℕ) (s t : Fin n) (y : Fin n → ℝ) : Prop :=
  (∀ v, (0 ≤ y v ∧ y v ≤ (N : ℝ) - 1) ∨
    ((N : ℝ) ≤ y v ∧ y v ≤ 2 * (N : ℝ) - 1)) ∧
    (N : ℝ) ≤ y s ∧ y t ≤ (N : ℝ) - 1

def CertificateChecks {n W : ℕ} (I : Instance n W) (N : ℕ)
    (s t : Fin n) (p : ℤ) (y : Fin n → ℝ) : Prop :=
  Intervals N s t y ∧ ∀ v, |excess (induced I y) v - target s t (p : ℝ) v| ≤ epsilon N

def denominator (N W : ℕ) : ℕ := 32 * N * N * W

noncomputable def gridPotential {n : ℕ} (N W : ℕ) (i : Fin n → ℤ) : Fin n → ℝ :=
  fun v => (i v : ℝ) / (denominator N W : ℝ)

noncomputable def roundIndex {n : ℕ} (N W : ℕ) (x : Fin n → ℝ) : Fin n → ℤ :=
  fun v => ⌊(denominator N W : ℝ) * x v⌋

def IndexRange {n : ℕ} (N W : ℕ) (i : Fin n → ℤ) : Prop :=
  ∀ v, 0 ≤ i v ∧ i v ≤ (2 * (N : ℤ) - 1) * (denominator N W : ℤ)

/-- One digit for zero; signs are unnecessary for accepted nonnegative indices. -/
def binaryDigits (i : ℤ) : ℕ := Nat.log 2 i.natAbs + 1

end RoundedPotentials.Main


