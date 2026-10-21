-- Prove2me | Definitions.Def_TechFinConstr_Selection_Model
-- name    : TechFinConstr_Selection_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:29.26644+00:00
-- url     : https://prove2.me/theorems/18432ff6-970f-4f5e-8245-b2d8b6fb6464
-- title:
--   §2–§3, pp. 7–11 — states, cash flows, baseline q, types 𝒫 (Assumptions 1–3), φ, Φ, Φ*, ῑ, tranches, contracting problem (1), optimal contracts, agency rent, c̄ₖ
-- statement:
--   This file sets up the moral-hazard financing model of Starmans (§2 and §3.1).
--
--   **Economy.** There are $n+1$ states $\Omega=\{0,1,\dots,n\}$. A project pays the cash flow $x_i$ in state $i$. If the entrepreneur shirks, the state is drawn from the baseline distribution $q$; the *expected value of effort* is a number $\pi$. The standing assumptions of §2 are
--   $$n>1,\qquad 0=x_0<x_1<\dots<x_n,\qquad q_i>0\ \ (i\in\Omega),\qquad \sum_{i\in\Omega}q_i=1,\qquad \pi>0 .$$
--   We write $\mathbb E_w[f]=\sum_{i}w_if_i$ for the expectation under a weight vector $w$, and $\sum_{i=j}^n w_i$ for a tail sum.
--
--   **Types.** An entrepreneur's type is the distribution $p$ of the state when the entrepreneur exerts effort. The *likelihood ratio* (Definition 1) is $\varphi_i(p)=(p_i-q_i)/q_i$. The type set $\mathscr P$ consists of probability vectors $p$ on $\Omega$ such that
--
--   1. (Assumption 1) $\mathbb E_p[x]-\mathbb E_q[x]=\pi$;
--   2. (Assumption 2) $\sum_{i=j}^n p_i\ge\sum_{i=j}^n q_i$ for every $j\in\Omega$, with strict inequality for some $j$;
--   3. (Assumption 3) $\varphi(p)$ is single-peaked: for some $j\in\Omega$ it is nondecreasing on $\{0,\dots,j\}$ and nonincreasing on $\{j,\dots,n\}$.
--
--   The *cumulative likelihood ratio* (Definition 3) is
--   $$\Phi_j(p)=\frac{\sum_{i=j}^n (p_i-q_i)}{\sum_{i=j}^n q_i},\qquad j\in\Omega,$$
--   and $\Phi^*(p)=\max_{j\in\Omega}\Phi_j(p)$. The state $\bar\iota(p)$ is the highest state $i$ with $p_i>q_i$ (equivalently $\varphi_i(p)>0$); it is the state $\bar\iota(p)$ of Lemma 2.
--
--   **Contracts.** For $k\in\{1,\dots,n\}$ the *tranche* $\bar s^k$ (Definition 2) pays $\bar s^k_i=\mathbb 1\{i\ge k\}(x_k-x_{k-1})$. Given a disutility of effort $c$, a contract $s\in\mathbb R^{\Omega}$ is *feasible* if
--   $$\mathbb E_p[s]-c\ge\mathbb E_q[s],\quad \mathbb E_p[s]-c\ge0,\quad s_i\ge0,\quad s_i\ge s_{i-1},\quad x_i-s_i\ge x_{i-1}-s_{i-1}\ (1\le i\le n),$$
--   which are constraints (1b)–(1f); it is *optimal* if it is feasible and maximizes the investor's expected payoff $\mathbb E_p[x-s]$ over all feasible contracts (1a). The *agency rent* of an optimal contract is $\mathbb E_q[s]$, and the agency rent function $c\mapsto\mathbb E_q[s^*(p)]$ is recorded as the infimum of $\mathbb E_q[s]$ over the optimal contracts at $c$.
--
--   Finally, for a permutation $\sigma$ of the tranches, $\bar c_k=\sum_{j=1}^k (x_{\sigma(j)}-x_{\sigma(j)-1})\,\Phi_{\sigma(j)}(p)\sum_{i=\sigma(j)}^n q_i$ are the thresholds of Proposition 1, with $\bar c_0=0$.
--
--   These objects are shared by every statement of the mission: the goal (Proposition 6) and its milestones are all about optimal contracts of problem (1).
--
--   **Formalization Note.** States are `Fin (n + 1)`. Tranches and positions of the ordering $\sigma$ are indexed by `j : Fin n`, standing for the paper's index $j+1\in\{1,\dots,n\}$: tranche `j` is the paper's $\bar s^{j+1}$, with $x_{j+1}$ = `x j.succ` and $x_j$ = `x j.castSucc`; `σ : Equiv.Perm (Fin n)` maps positions to tranches, so the paper's $\sigma(j+1)$ is `(σ j).succ`, and `cbar E p σ k` is $\bar c_k$ for every natural number $k$. `Phi` uses the p. 11 form $\sum(p_i-q_i)/\sum q_i$, which equals Definition 3's $\sum q_i\varphi_i(p)/\sum q_i$ because $q_i>0$. `iotaBar` is a state (`Fin (n + 1)`), equal to $0$ when no state has $p_i>q_i$ (this does not happen for $p\in\mathscr P$). `agencyRent` is the infimum of $\mathbb E_q[s]$ over optimal contracts; it is meaningful only where an optimal contract exists, which the theorems state. The investor's capital $I$ and the condition $\mathbb E_q[x]+\pi-c\ge I\ge\mathbb E_q[x]$ of p. 8 are omitted: they do not enter problem (1), which drops the investor's participation constraint (p. 9).
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), pp. 7–11, §2, §3.1, Definitions 1–3, Assumptions 1–6, problem (1a)–(1f), Lemma 2 (ῑ(p)), Proposition 1 (c̄ₖ)

import Mathlib

namespace TechFinConstr.Selection

open Finset

/-- §2, p. 7: an economy with states `Ω = {0, …, n}` (`Fin (n + 1)`), cash flows `x i` in state `i`,
the baseline (shirking) distribution `q`, and the common expected value of effort `piE` (the
paper's `π`, Assumption 1). -/
structure Economy (n : ℕ) where
  /-- cash flow `x_i` in state `i` -/
  x : Fin (n + 1) → ℝ
  /-- baseline distribution `q` (cash-flow distribution when the entrepreneur shirks) -/
  q : Fin (n + 1) → ℝ
  /-- expected value of effort `π` -/
  piE : ℝ

variable {n : ℕ}

/-- Standing assumptions of §2 (pp. 7–8): `n > 1`, `0 = x_0 < x_1 < ⋯ < x_n`, `q` a probability
vector with `q_i > 0` for every state, and `π > 0`. -/
def Economy.Standing (E : Economy n) : Prop :=
  1 < n ∧ E.x 0 = 0 ∧ StrictMono E.x ∧ (∀ i, 0 < E.q i) ∧ ∑ i, E.q i = 1 ∧ 0 < E.piE

/-- Expectation of `f` under the weights `w`: `E_w[f] = ∑_i w_i f_i`. -/
def expect (w f : Fin (n + 1) → ℝ) : ℝ := ∑ i, w i * f i

/-- Tail sum `∑_{i=j}^{n} w_i`. -/
def tail (w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  ∑ i ∈ univ.filter (fun i => j ≤ i), w i

/-- Definition 1 (p. 7): the likelihood ratio `φ_i(p) = (p_i − q_i)/q_i`. -/
noncomputable def phi (E : Economy n) (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (p i - E.q i) / E.q i

/-- Definition 3 (p. 10), in the equivalent form of p. 11:
`Φ_j(p) = ∑_{i=j}^n (p_i − q_i) / ∑_{i=j}^n q_i`. -/
noncomputable def Phi (E : Economy n) (p : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  tail (p - E.q) j / tail E.q j

/-- Definition 3 (p. 10): the maximum cumulative likelihood ratio `Φ*(p) = max_{j ∈ Ω} Φ_j(p)`,
the maximum over all of `Ω = {0, …, n}`. -/
noncomputable def PhiStar (E : Economy n) (p : Fin (n + 1) → ℝ) : ℝ :=
  univ.sup' univ_nonempty (Phi E p)

/-- The type set `𝒫` (p. 7): probability distributions `p` on `Ω` satisfying Assumption 1
(`E_p[x] − E_q[x] = π`), Assumption 2 (first-order stochastic dominance, with one strict tail) and
Assumption 3 (`φ(p)` single-peaked). -/
def InP (E : Economy n) (p : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
  expect p E.x - expect E.q E.x = E.piE ∧
  (∀ j, tail E.q j ≤ tail p j) ∧ (∃ j, tail E.q j < tail p j) ∧
  ∃ j : Fin (n + 1), (∀ i k : Fin (n + 1), i ≤ k → k ≤ j → phi E p i ≤ phi E p k) ∧
    (∀ i k : Fin (n + 1), j ≤ i → i ≤ k → phi E p k ≤ phi E p i)

/-- `ῑ(p)` of Lemma 2 (p. 12): the highest state `i` with `φ_i(p) > 0`, i.e. with `p_i > q_i`
(`0` if there is none; for `p ∈ 𝒫` there always is one). -/
noncomputable def iotaBar (E : Economy n) (p : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  (univ.filter (fun i : Fin (n + 1) => E.q i < p i)).sup id

/-- Definition 2 (p. 10): tranche `s̄^k_i = 1{i ≥ k}(x_k − x_{k−1})` for `k ∈ {1, …, n}`.
Tranches are indexed by `j : Fin n`, standing for the paper's `k = j + 1`; so `x_k` is
`x j.succ` and `x_{k−1}` is `x j.castSucc`. -/
def tranche (E : Economy n) (j : Fin n) (i : Fin (n + 1)) : ℝ :=
  if j.succ ≤ i then E.x j.succ - E.x j.castSucc else 0

/-- Constraints (1b)–(1f) of the contracting problem (1), pp. 9–10, for a contract
`s = (s_i)_{i ∈ Ω}` and disutility of effort `c`. -/
def Feasible (E : Economy n) (p : Fin (n + 1) → ℝ) (c : ℝ) (s : Fin (n + 1) → ℝ) : Prop :=
  expect p s - c ≥ expect E.q s ∧
  expect p s - c ≥ 0 ∧
  (∀ i, 0 ≤ s i) ∧
  (∀ i : Fin n, s i.castSucc ≤ s i.succ) ∧
  (∀ i : Fin n, E.x i.castSucc - s i.castSucc ≤ E.x i.succ - s i.succ)

/-- Problem (1), (1a): `s` maximizes the investor's expected payoff `E_p[x − s]` over all contracts
satisfying (1b)–(1f). -/
def IsOptimalContract (E : Economy n) (p : Fin (n + 1) → ℝ) (c : ℝ) (s : Fin (n + 1) → ℝ) : Prop :=
  Feasible E p c s ∧ ∀ s', Feasible E p c s' → expect p (E.x - s') ≤ expect p (E.x - s)

/-- The agency rent function `c ↦ E_q[s*(p)]` (p. 15): the infimum of `E_q[s]` over the optimal
contracts at `c` (all optimal contracts share this value, footnote 7, p. 11; it is only meaningful
where an optimal contract exists). -/
noncomputable def agencyRent (E : Economy n) (p : Fin (n + 1) → ℝ) (c : ℝ) : ℝ :=
  sInf (expect E.q '' {s | IsOptimalContract E p c s})

/-- `c̄_k` of Proposition 1 (p. 11) for an ordering `σ` of the tranches:
`c̄_k = ∑_{j=1}^{k} (x_{σ(j)} − x_{σ(j)−1}) Φ_{σ(j)}(p) ∑_{i=σ(j)}^n q_i`.
Position `j` of the ordering is `j : Fin n` (the paper's position `j + 1`), and the tranche at that
position is `σ j` (the paper's tranche `σ(j+1) = (σ j).succ`). -/
noncomputable def cbar (E : Economy n) (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin n => j.val < k),
    (E.x (σ j).succ - E.x (σ j).castSucc) * Phi E p (σ j).succ * tail E.q (σ j).succ

end TechFinConstr.Selection


