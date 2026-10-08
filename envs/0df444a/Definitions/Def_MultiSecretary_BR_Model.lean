-- Prove2me | Definitions.Def_MultiSecretary_BR_Model
-- name    : MultiSecretary_BR_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:37:17.3968+00:00
-- url     : https://prove2.me/theorems/48cc97c9-9528-4d8c-beea-83d81b6dcf75
-- title:
--   Sec. 2–4 — the multi-secretary model: $V^*_{\mathrm{off}}$, online policies $\Pi(n,k)$, $V^*_{\mathrm{on}}$, counts $Z^r_j$, $\mathfrak S^r_j$, $S^{\pi,r}_j$, thresholds $T_j$, action index $j_0$
-- statement:
--   A decision maker sees $n$ candidates one at a time, with abilities $X_1,\dots,X_n$, and may select at most $k$ of them; every decision is final. The abilities are independent and identically distributed on a finite set $\mathcal A=\{a_m<a_{m-1}<\dots<a_1\}$ of distinct positive reals, with probability mass function $f_j=\mathbb P(X_1=a_j)>0$, $\sum_j f_j=1$. Write $\bar F(a_j)=f_1+\dots+f_{j-1}$ for the mass strictly above $a_j$, and
--   $$\epsilon=\tfrac12\min\{f_m,\dots,f_1\}.$$
--   Budget pairs range over the triangle $\mathcal T=\{(n,k)\in\mathbb Z_+^2: 0\le k\le n\}$.
--
--   This definition fixes the objects the mission is stated in.
--
--   1. **Offline value.** $V^*_{\mathrm{off}}(n,k)=\mathbb E\big[\max\{\sum_{t\in[n]}X_t\sigma_t:\sigma\in\{0,1\}^n,\ \sum_t\sigma_t\le k\}\big]$, the expected value of the best $k$ candidates chosen in hindsight.
--   2. **Online policies.** A selection rule $\sigma$ assigns to each realization and each time $t$ a decision $\sigma_t\in\{0,1\}$. It is *online* if $\sigma_t$ depends only on $X_1,\dots,X_t$, and *feasible* if $\sum_t\sigma_t\le k$ on every realization. $\Pi(n,k)$ is the set of feasible online rules, $V^\sigma_{\mathrm{on}}(n,k)=\mathbb E[\sum_t X_t\sigma_t]$, and $V^*_{\mathrm{on}}(n,k)=\max_{\sigma\in\Pi(n,k)}V^\sigma_{\mathrm{on}}(n,k)$.
--   3. **Counts.** $Z^r_j$ is the number of $a_j$-candidates among the first $r$; the offline counts are $\mathfrak S^r_j=\min\{Z^r_j,(k-\sum_{i<j}Z^r_i)_+\}$ (eq. (3)); the online counts $S^{\sigma,r}_j$ are the number of $a_j$-candidates selected by $\sigma$ among the first $r$.
--   4. **Thresholds** (p. 11). $T_1=0$, $T_j=\tfrac12(\bar F(a_j)+\bar F(a_{j+1}))=\bar F(a_j)+\tfrac12 f_j$ for $j\in\{2,\dots,m\}$, and $T_{m+1}=+\infty$.
--   5. **Action index** (5). $j_0(n,k)$ is the largest $j$ with $\bar F(a_j)+\tfrac12 f_j\le k/n$, and $1$ if there is none; this is the three-case definition (5) of p. 7.
--
--   These are the shared vocabulary of every statement of the mission: the regret of a policy is $V^*_{\mathrm{off}}-V^\sigma_{\mathrm{on}}$.
--
--   **Formalization Note** Lean index $i$ of `Fin m` is the paper's index $i+1$, so `a 0` is $a_1$, the largest ability. Expectations are finite sums over outcome sequences $x:\{0,\dots,n-1\}\to\{0,\dots,m-1\}$ weighted by $\prod_t f(x_t)$, the i.i.d. law. Policies are deterministic functions of the realization; the paper allows randomized policies, and for this finite problem the optimal value is the same (p. 39 cites Bertsekas–Shreve, Cor. 8.5.1). Restricting $V^*_{\mathrm{on}}$ to deterministic rules can only lower it, so an upper bound on $V^*_{\mathrm{off}}-V^*_{\mathrm{on}}$ is not weakened. The positive part in $\mathfrak S^r_j$ is natural-number subtraction. In $j_0$, $k/n$ is real division, equal to $0$ at $n=0$ (where $k=0$). The structure field $0<m$ is implied by $\sum_j f_j=1$.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Sec. 2, pp. 3–5; Sec. 3, p. 7, eqs. (3), (5); Sec. 3, p. 9 (online counts); Sec. 4, p. 11 (thresholds)

import Mathlib

namespace MultiSecretary.BR

open Finset

/-- An instance of the multi-secretary problem of Arlotto–Gurvich, *Uniformly Bounded Regret in the
Multi-Secretary Problem*, arXiv:1710.07719v2, Sec. 2, pp. 3–4: abilities are i.i.d. with a common
distribution supported on a finite set `A = {a_m < ⋯ < a_1}` of distinct positive reals, with
probability mass function `f`.

Indexing: Lean index `i : Fin m` is the paper's index `i + 1`, so `a 0 = a_1` is the **largest**
ability and `a` is strictly decreasing. All masses are positive (the paper's
`f_m = F(a_m) < F(a_{m-1}) < ⋯ < F(a_1) = 1`), and they sum to one. `m_pos` (`0 < m`) is implied by
`f_sum` and is recorded only so that the index `0` can be named. -/
structure Instance (m : ℕ) where
  a : Fin m → ℝ
  f : Fin m → ℝ
  a_pos : ∀ j, 0 < a j
  a_anti : StrictAnti a
  f_pos : ∀ j, 0 < f j
  f_sum : ∑ j, f j = 1
  m_pos : 0 < m

variable {m : ℕ}

namespace Instance

variable (I : Instance m)

/-- The index of the largest ability `a_1` (Lean index `0`). -/
def top : Fin m := ⟨0, I.m_pos⟩

/-- `ϵ = ½ min{f_m, …, f_1}` (Theorem 1, p. 5). -/
noncomputable def eps : ℝ := (univ.inf' ⟨I.top, mem_univ _⟩ I.f) / 2

/-- The survival function at the support points, `F̄(a_j) = f_1 + ⋯ + f_{j-1}`: the mass strictly
above `a_j` (in Lean indexing, `∑_{i < j} f i`). -/
noncomputable def survival (j : Fin m) : ℝ := ∑ i ∈ univ.filter (fun i => i < j), I.f i

/-- The probability of an outcome sequence `x : Fin n → Fin m`, i.e. of `(X_1, …, X_n) =
(a_{x 0}, …, a_{x (n-1)})` under independent draws from `f`: `∏_t f(x_t)`. -/
noncomputable def weight {n : ℕ} (x : Fin n → Fin m) : ℝ := ∏ t, I.f (x t)

/-- Expectation of `g` under the i.i.d. law of `(X_1, …, X_n)`, as a finite sum. -/
noncomputable def E {n : ℕ} (g : (Fin n → Fin m) → ℝ) : ℝ := ∑ x, I.weight x * g x

/-- The offline value `V*_off(n, k)` (Sec. 2, p. 5): the expectation of the largest total ability
`∑_t X_t σ_t` over all selection vectors `σ ∈ {0,1}^n` with `∑_t σ_t ≤ k`. -/
noncomputable def Voff (n k : ℕ) : ℝ :=
  I.E (fun x : Fin n → Fin m =>
    (univ.filter (fun s : Fin n → Bool => (univ.filter (fun t => s t = true)).card ≤ k)).sup'
      ⟨fun _ => false, by simp⟩
      (fun s => ∑ t, if s t = true then I.a (x t) else 0))

/-- The value `V^σ_on(n, k) = E[∑_t X_t σ_t]` of a deterministic selection rule
`σ : (Fin n → Fin m) → Fin n → Bool` (`σ x t = true`: candidate `t` is selected). -/
noncomputable def value {n : ℕ} (σ : (Fin n → Fin m) → Fin n → Bool) : ℝ :=
  I.E (fun x => ∑ t, if σ x t = true then I.a (x t) else 0)

/-- The thresholds of the Budget-Ratio policy (Sec. 4, p. 11): `T_1 = 0` and
`T_j = ½(F̄(a_j) + F̄(a_{j+1})) = F̄(a_j) + f_j/2` for `j ∈ {2, …, m}`; `T_{m+1} = +∞` is not an
element of `Fin m` and is encoded by the absence of an upper threshold. -/
noncomputable def T (j : Fin m) : ℝ := if j.val = 0 then 0 else I.survival j + I.f j / 2

/-- The action index `j₀(n, k)` of (5), p. 7: the largest `j` with `F̄(a_j) + f_j/2 ≤ k/n`, and
`j₀ = 1` (Lean index `0`) if there is none. This agrees with the three cases of (5). Here `k/n` is
real division (`k/0 = 0`). -/
noncomputable def actionIndex (n k : ℕ) : Fin m :=
  if h : (univ.filter (fun j : Fin m => I.survival j + I.f j / 2 ≤ (k : ℝ) / n)).Nonempty then
    (univ.filter (fun j : Fin m => I.survival j + I.f j / 2 ≤ (k : ℝ) / n)).max' h
  else I.top

end Instance

/-- Online (non-anticipating) selection rule: the decision on candidate `t` depends only on
`x 0, …, x t` (the paper's `σ_t ∈ F_t`). -/
def IsOnline {n : ℕ} (σ : (Fin n → Fin m) → Fin n → Bool) : Prop :=
  ∀ x y : Fin n → Fin m, ∀ t : Fin n, (∀ s, s ≤ t → x s = y s) → σ x t = σ y t

/-- Feasibility: on every realization at most `k` candidates are selected. -/
def IsFeasible {n : ℕ} (k : ℕ) (σ : (Fin n → Fin m) → Fin n → Bool) : Prop :=
  ∀ x : Fin n → Fin m, (univ.filter (fun t => σ x t = true)).card ≤ k

/-- `Π(n, k)`: the deterministic feasible online policies, as a finite set. -/
noncomputable def policies (n m k : ℕ) : Finset ((Fin n → Fin m) → Fin n → Bool) :=
  by classical exact univ.filter (fun σ => IsOnline σ ∧ IsFeasible k σ)

theorem never_mem_policies (n m k : ℕ) : (fun _ _ => false) ∈ policies n m k := by
  classical
  unfold policies
  convert (Finset.mem_filter (s := univ) (p := fun σ : (Fin n → Fin m) → Fin n → Bool =>
    IsOnline σ ∧ IsFeasible k σ) (a := fun _ _ => false)).mpr ⟨mem_univ _, fun _ _ _ _ => rfl, fun _ => by simp⟩

namespace Instance

variable (I : Instance m)

/-- `V*_on(n, k) = max_{π ∈ Π(n, k)} V^π_on(n, k)` (p. 5), over deterministic feasible online
policies. -/
noncomputable def Von (n k : ℕ) : ℝ :=
  (policies n m k).sup' ⟨_, never_mem_policies n m k⟩ I.value

end Instance

/-- `Z^r_j(x)`: the number of candidates of ability `a_j` among the first `r` (Sec. 3, p. 7). -/
def Z {n : ℕ} (r : ℕ) (j : Fin m) (x : Fin n → Fin m) : ℕ :=
  (univ.filter (fun t : Fin n => t.val < r ∧ x t = j)).card

/-- The offline counts of (3), p. 7, at horizon `r`:
`𝔖^r_j = min{Z^r_j, (k − ∑_{i<j} Z^r_i)_+}` (natural subtraction is the positive part). -/
def offCount {n : ℕ} (k r : ℕ) (j : Fin m) (x : Fin n → Fin m) : ℕ :=
  min (Z r j x) (k - ∑ i ∈ univ.filter (fun i => i < j), Z r i x)

/-- The online counts `S^{π,r}_j = ∑_{t=1}^r σ_t 1(X_t = a_j)` (p. 9). -/
def onCount {n : ℕ} (σ : (Fin n → Fin m) → Fin n → Bool) (r : ℕ) (j : Fin m)
    (x : Fin n → Fin m) : ℕ :=
  (univ.filter (fun t : Fin n => t.val < r ∧ σ x t = true ∧ x t = j)).card

end MultiSecretary.BR


