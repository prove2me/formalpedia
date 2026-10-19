-- Prove2me | Definitions.Def_PBElicit_RandThresh_Setting
-- name    : PBElicit_RandThresh_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:15.131444+00:00
-- url     : https://prove2.me/theorems/47a0ee2f-07f9-41b3-9920-4091ec766e7e
-- title:
--   §2, pp. 5–7, and §3.1.3, pp. 12–13 — costs, F_c, normalized additive utilities, sw, threshold approval votes, randomized threshold rules, and the intervals and buckets of Theorem 3.5's proof
-- statement:
--   This file fixes the participatory budgeting model of Benadè, Nath, Procaccia and Shah, and the objects of the proof of their Theorem 3.5.
--
--   **Model (§2).** There are $n$ voters $N=[n]$ and a finite set $A$ of $m=|A|$ alternatives (projects). Alternative $a$ has cost $c_a$, and the budget is normalized to $1$. For $S\subseteq A$ write $c(S)=\sum_{a\in S}c_a$. The family of inclusion-maximal budget-feasible sets is
--   $$
--   \mathcal F_c=\{S\subseteq A:\ c(S)\le 1\ \text{and}\ c(T)>1\ \text{for all}\ S\subsetneq T\subseteq A\}.
--   $$
--   Each voter $i$ has nonnegative additive utilities $v_i:A\to\mathbb R_{\ge 0}$, normalized so that $v_i(A)=\sum_{a\in A}v_i(a)=1$; the vector $\vec v=(v_1,\dots,v_n)$ is a utility profile. The utilitarian social welfare of $S\subseteq A$ is
--   $$
--   \mathrm{sw}(S,\vec v)=\sum_{a\in S}\sum_{i\in N}v_i(a).
--   $$
--
--   **Threshold approval votes.** At threshold $t$, voter $i$ reports $\tau_i=\{a\in A: v_i(a)\ge t\}$; the profile $\vec\rho(\vec v,t)=(\tau_1,\dots,\tau_n)$ is the input induced by $\vec v$ at $t$.
--
--   **Randomized threshold rules (§3.1.3).** A rule is a finite mixture of arms $r$: arm $r$ is used with probability $w_r\ge 0$ ($\sum_r w_r=1$), elicits threshold approval votes at threshold $t_r$, and applies a deterministic aggregation map $g_r$ sending each threshold approval profile to a set in $\mathcal F_c$. The aggregation sees only the approval profile, never the utilities. Its expected welfare on $\vec v$ is
--   $$
--   \mathbb E[\mathrm{sw}]=\sum_r w_r\,\mathrm{sw}\big(g_r(\vec\rho(\vec v,t_r)),\vec v\big).
--   $$
--
--   **Objects of the proof of Theorem 3.5 (pp. 12–13).** With $m$ given, put $\ell_0=0$, $u_0=1/m^2$, $I_0=[0,1/m^2]$, and for $j\ge 1$
--   $$
--   \ell_j=\frac{2^{j-1}}{m^2},\qquad u_j=\frac{2^j}{m^2},\qquad I_j=(\ell_j,u_j].
--   $$
--   For an alternative $a$, $n^a_j=|\{i\in N: v_i(a)\in I_j\}|$; the cost bucket is $S_j=\{a\in A: c_a\in I_j\}$; for a set $S$, $n^*_{j,k}=\sum_{a\in S\cap S_k}n^a_j$. The predicate `IsWelfareOptimal c v S` says $S\in\mathcal F_c$ and $\mathrm{sw}(T,\vec v)\le\mathrm{sw}(S,\vec v)$ for every $T\in\mathcal F_c$; it identifies the page's $S^*$. A set $B_{j,k}$ of Mechanism A is a set of $\min(1/u_k,|S_k|)$ alternatives of $S_k$ with the largest numbers of approval votes at threshold $\ell_j$, ties broken arbitrarily.
--
--   These definitions are shared by every statement of the mission: the distortion bounds compare $\max_{T\in\mathcal F_c}\mathrm{sw}(T,\vec v)$ with the expected welfare of a rule.
--
--   **Formalization Note.** Voters are `Fin n`; alternatives a `Fintype` `A`. `ThresholdRule n A c` bundles the size, weights, thresholds and aggregation maps with the proofs that weights are nonnegative and sum to $1$ and that every output lies in $\mathcal F_c$ (`IsMaxFeasible`). `expWelfare` is the expectation over both the threshold and the aggregation. `lo m j`, `up m j`, `Ivl m j` are $\ell_j,u_j,I_j$ (with $\ell_0=0$, $u_0=1/m^2$); `cnt`, `bucket`, `cntStar` are $n^a_j$, $S_j$, $n^*_{j,k}$; `approvalCount v t a` is $|\{i: v_i(a)\ge t\}|$; `IsGreedyTop v c m j k B` says $B\subseteq S_k$, $|B|=\min(m^2/2^k,|S_k|)$ (natural-number division, exact when $m$ is a power of $2$ and $k\le 2\log_2 m$), and every alternative of $B$ has at least as many approvals at $\ell_j$ as every alternative of $S_k\setminus B$.
-- source:
--   Benadè, Nath, Procaccia & Shah, Preference Elicitation for Participatory Budgeting, author's manuscript (2018; Manag. Sci. 2021, doi:10.1287/mnsc.2020.3666), §2, pp. 5–7; §3.1.3, p. 12; proof of Theorem 3.5, pp. 12–13

import Mathlib

namespace PBElicit.RandThresh

open Classical

/-- `c(S) = ∑_{a ∈ S} c_a`, the cost of a set of alternatives (§2, p. 5). -/
noncomputable def cost {A : Type*} (c : A → ℝ) (S : Finset A) : ℝ := ∑ a ∈ S, c a

/-- `S ∈ F_c`: `S` is an inclusion-maximal budget-feasible set (budget `1`), §2, p. 5:
`c(S) ≤ 1` and `c(T) > 1` for every `S ⊊ T ⊆ A`. -/
def IsMaxFeasible {A : Type*} (c : A → ℝ) (S : Finset A) : Prop :=
  cost c S ≤ 1 ∧ ∀ T : Finset A, S ⊂ T → 1 < cost c T

/-- A utility profile (§2, p. 5): nonnegative additive utilities `v_i : A → ℝ≥0` normalized by
`v_i(A) = 1` for every voter `i ∈ [n]` (voters are `Fin n`). -/
def IsUtilityProfile {n : ℕ} {A : Type*} [Fintype A] (v : Fin n → A → ℝ) : Prop :=
  (∀ i a, 0 ≤ v i a) ∧ ∀ i, ∑ a, v i a = 1

/-- Utilitarian social welfare `sw(S, v⃗) = ∑_{a ∈ S} ∑_{i ∈ N} v_i(a)` (§2, p. 6). -/
noncomputable def sw {n : ℕ} {A : Type*} (v : Fin n → A → ℝ) (S : Finset A) : ℝ :=
  ∑ a ∈ S, ∑ i, v i a

/-- `S* = arg max_{S ∈ F_c} sw(S, v⃗)`, the welfare-maximizing feasible set in the
proof of Theorem 3.5 (p. 13). -/
def IsWelfareOptimal {n : ℕ} {A : Type*} (c : A → ℝ) (v : Fin n → A → ℝ)
    (S : Finset A) : Prop :=
  IsMaxFeasible c S ∧ ∀ T : Finset A, IsMaxFeasible c T → sw v T ≤ sw v S

/-- The threshold approval profile `ρ⃗(v⃗, t)` induced by `v⃗` at threshold `t` (§2, p. 6):
voter `i` approves `τ_i = {a ∈ A : v_i(a) ≥ t}`. -/
noncomputable def approvals {n : ℕ} {A : Type*} [Fintype A] (v : Fin n → A → ℝ) (t : ℝ) :
    Fin n → Finset A :=
  fun i => Finset.univ.filter (fun a => t ≤ v i a)

/-- A rule for randomized threshold approval votes (§3.1.3, p. 12), as a finite mixture of arms:
arm `r` has probability `weight r`, threshold `thr r`, and a deterministic aggregation map `agg r`
from threshold approval profiles to `F_c`. -/
structure ThresholdRule (n : ℕ) (A : Type*) [Fintype A] [DecidableEq A] (c : A → ℝ) where
  size : ℕ
  weight : Fin size → ℝ
  thr : Fin size → ℝ
  agg : Fin size → (Fin n → Finset A) → Finset A
  weight_nonneg : ∀ r, 0 ≤ weight r
  weight_sum : ∑ r, weight r = 1
  agg_mem : ∀ r ρ, IsMaxFeasible c (agg r ρ)

/-- The expected social welfare `E_{t∼D} E[sw(f(ρ⃗(v⃗, t)), v⃗)]` of a randomized threshold rule. -/
noncomputable def ThresholdRule.expWelfare {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    {c : A → ℝ} (R : ThresholdRule n A c) (v : Fin n → A → ℝ) : ℝ :=
  ∑ r, R.weight r * sw v (R.agg r (approvals v (R.thr r)))

/-- `ℓ_j = 2^{j-1}/m²` for `j ≥ 1`, and `ℓ_0 = 0` (proof of Theorem 3.5, pp. 12–13). -/
noncomputable def lo (m j : ℕ) : ℝ := if j = 0 then 0 else 2 ^ (j - 1) / (m : ℝ) ^ 2

/-- `u_j = 2^j/m²` (so `u_0 = 1/m²`), proof of Theorem 3.5, pp. 12–13. -/
noncomputable def up (m j : ℕ) : ℝ := 2 ^ j / (m : ℝ) ^ 2

/-- `I_0 = [0, 1/m²]` and `I_j = (2^{j-1}/m², 2^j/m²]` for `j ≥ 1` (proof of Theorem 3.5, p. 12). -/
def Ivl (m j : ℕ) : Set ℝ :=
  if j = 0 then Set.Icc 0 (1 / (m : ℝ) ^ 2) else Set.Ioc (lo m j) (up m j)

/-- `n^a_j = |{i ∈ N : v_i(a) ∈ I_j}|` (proof of Theorem 3.5, p. 12). -/
noncomputable def cnt {n : ℕ} {A : Type*} (v : Fin n → A → ℝ) (m : ℕ) (a : A) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => v i a ∈ Ivl m j)).card

/-- The cost bucket `S_j = {a ∈ A : c_a ∈ I_j}` (proof of Theorem 3.5, p. 13). -/
noncomputable def bucket {A : Type*} [Fintype A] (c : A → ℝ) (m j : ℕ) : Finset A :=
  Finset.univ.filter (fun a => c a ∈ Ivl m j)

/-- `n*_{j,k} = ∑_{a ∈ T ∩ S_k} n^a_j` for a set `T` (the page takes `T = S*`), p. 13. -/
noncomputable def cntStar {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (v : Fin n → A → ℝ)
    (c : A → ℝ) (m : ℕ) (T : Finset A) (j k : ℕ) : ℕ :=
  ∑ a ∈ T ∩ bucket c m k, cnt v m a j

/-- The number of voters approving `a` at threshold `t`: `|{i : v_i(a) ≥ t}|`. -/
noncomputable def approvalCount {n : ℕ} {A : Type*} (v : Fin n → A → ℝ) (t : ℝ) (a : A) : ℕ :=
  (Finset.univ.filter (fun i => t ≤ v i a)).card

/-- `B` is a set `B_{j,k}` of Mechanism A (p. 13): at threshold `ℓ_j`, the `1/u_k = m²/2^k`
alternatives of `S_k` with the most approval votes (all of `S_k` if `|S_k| ≤ 1/u_k`), ties broken
arbitrarily. -/
def IsGreedyTop {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (v : Fin n → A → ℝ)
    (c : A → ℝ) (m j k : ℕ) (B : Finset A) : Prop :=
  B ⊆ bucket c m k ∧ B.card = min (m ^ 2 / 2 ^ k) (bucket c m k).card ∧
    ∀ a ∈ B, ∀ b ∈ bucket c m k \ B, approvalCount v (lo m j) b ≤ approvalCount v (lo m j) a

end PBElicit.RandThresh


