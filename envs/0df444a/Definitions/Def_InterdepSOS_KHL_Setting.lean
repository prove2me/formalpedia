-- Prove2me | Definitions.Def_InterdepSOS_KHL_Setting
-- name    : InterdepSOS_KHL_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:53.944848+00:00
-- url     : https://prove2.me/theorems/d16a45a3-b1cc-4224-80d0-7af7195360cf
-- title:
--   §2.2–§2.3, §6 — combinatorial interdependent valuations over k signal values, SOS (Definition 2.13), feasible allocations, ex-post IC/IR (Definitions 2.11–2.12), OTHER and SELF (display (7))
-- statement:
--   This file fixes the model of §6 of Eden, Feldman, Fiat, Goldner and Karlin: a combinatorial auction with interdependent values and single-dimensional signals drawn from a finite signal space.
--
--   There are $n$ agents $[n]$ and $m$ items $[m]$. Each agent $i$ holds a private signal $s_i\in\{0,1,\dots,k-1\}$; a profile is $\mathbf s=(s_1,\dots,s_n)$, and the **grid** is $\{0,\dots,k-1\}^n$. For a set $S$ of agents, $(\mathbf s_S,\mathbf 0_{[n]\setminus S})$ keeps the coordinates in $S$ and sets the others to $0$; $(\mathbf s_{-i},x_i)$ replaces agent $i$'s signal by $x$.
--
--   1. **Valuations** (Definition 2.9). Agent $i$'s value for the bundle $T\subseteq[m]$ at the profile $\mathbf s$ is $v_{iT}(\mathbf s)\in\mathbb R$. On the grid the standing assumptions are: $v_{iT}(\mathbf s)\ge0$; $v_{i\emptyset}\equiv0$; and for every nonempty $T$, $v_{iT}$ is weakly increasing in every signal and strictly increasing in $s_i$.
--   2. **SOS** (Definition 2.13, inequality (1) with $d=1$). A function $w$ of the profile is SOS if for every coordinate $j$, all $x,\delta\in\mathbb N$ with $x+\delta\le k-1$, and grid profiles $\mathbf s,\mathbf s'$ with $s'_l\le s_l$ for all $l\ne j$,
--   $$w(\mathbf s_{-j},x+\delta)-w(\mathbf s_{-j},x)\;\le\;w(\mathbf s'_{-j},x+\delta)-w(\mathbf s'_{-j},x).$$
--   The SOS setting (Definition 2.15) asks this of every $v_{iT}$.
--   3. **Allocations** (Definition 2.11). An assignment of bundles $T=(T_1,\dots,T_n)$ is a feasible allocation restricted to the agent set $N$ if distinct agents receive disjoint bundles and agents outside $N$ receive $\emptyset$. Its welfare at $\mathbf s$ is $\sum_i v_{iT_i}(\mathbf s)$.
--   4. **Incentives** (Definitions 2.3–2.5, 2.12). A deterministic mechanism is an allocation rule $x$ and a payment rule $p$, both functions of the reported profile. The utility of agent $i$ with true profile $\mathbf s$ who reports $y$ while the others report truthfully is
--   $$u_i(y,\mathbf s_{-i}\mid s_i)=v_{i\,x_i(\mathbf s_{-i},y)}(\mathbf s)-p_i(\mathbf s_{-i},y).$$
--   The mechanism is ex-post IC if for every grid profile $\mathbf s$, agent $i$ and report $y\in\{0,\dots,k-1\}$, $u_i(y,\mathbf s_{-i}\mid s_i)\le u_i(s_i,\mathbf s_{-i}\mid s_i)$, and ex-post IR if $u_i(s_i,\mathbf s_{-i}\mid s_i)\ge0$.
--   5. **Random partition.** The uniform average over the partition $(A,B)$ of $[n]$ is $\mathbb E_B[f(B)]=2^{-n}\sum_{B\subseteq[n]}f(B)$.
--   6. **OTHER and SELF** (display (7), p. 19). For an assignment $T$ and a profile $\mathbf s$,
--   $$\mathsf{OTHER}=\sum_i v_{iT_i}(\mathbf s_{-i},0_i),\qquad \mathsf{SELF}=\sum_{\ell=1}^{k-1}\sum_{i\,:\,s_i=\ell}v_{iT_i}(\mathbf 0_{-i},s_i).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Agents are `Fin n`, items `Fin m`, signals natural numbers with the grid condition `InGrid k s` (`∀ i, s i < k`). All valuation hypotheses are stated on grid profiles only. The empty bundle is worth $0$ and the monotonicity clauses apply to nonempty bundles only (the strictness clause cannot hold for $\emptyset$). The paper's $\mathbb R_+$ becomes the grid $\{0,\dots,k-1\}$ of §6.1.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), pp. 9–12 and 19, Definitions 2.3–2.5, 2.9, 2.11–2.13, 2.15, display (7), §6.1 signal space

import Mathlib

namespace InterdepSOS.KHL

/-- A profile of discrete signals: agent `i` reports `s i ∈ ℕ`; the signal space is
`{0, …, k-1}`, imposed through `InGrid k`. -/
abbrev Signal (n : ℕ) := Fin n → ℕ

/-- `v i T s` is agent `i`'s value for the bundle `T` of items at the signal profile `s`
(Definition 2.9). -/
abbrev Valuation (n m : ℕ) := Fin n → Finset (Fin m) → Signal n → ℝ

/-- A combinatorial allocation: agent `i` receives the bundle `T i`. -/
abbrev Allocation (n m : ℕ) := Fin n → Finset (Fin m)

/-- A deterministic allocation rule, a function of the reported profile. -/
abbrev AllocRule (n m : ℕ) := Signal n → Allocation n m

/-- A deterministic payment rule: `p s i` is agent `i`'s payment at the reported profile `s`. -/
abbrev Payment (n : ℕ) := Signal n → Fin n → ℝ

/-- The profile lies in the signal space `{0, …, k-1}^n`. -/
def InGrid {n : ℕ} (k : ℕ) (s : Signal n) : Prop := ∀ i, s i < k

/-- Keep the coordinates in `S` and set the others to `0`. -/
def keepOn {n : ℕ} (S : Finset (Fin n)) (s : Signal n) : Signal n :=
  fun j => if j ∈ S then s j else 0

/-- Standing hypotheses on combinatorial valuations over the grid `{0,…,k-1}^n` (Definition 2.9,
with the signal space of §6.1): values are nonnegative, the empty bundle is worth `0`, and for
every nonempty bundle the value is weakly increasing in every signal and strictly increasing in
the agent's own signal (strict increase is impossible for the empty bundle, whose value is `0`). -/
def IsCombValuation {n m : ℕ} (k : ℕ) (v : Valuation n m) : Prop :=
  (∀ i T s, InGrid k s → 0 ≤ v i T s) ∧
  (∀ i s, InGrid k s → v i ∅ s = 0) ∧
  (∀ i (T : Finset (Fin m)), T.Nonempty → ∀ s s', InGrid k s → InGrid k s' → s ≤ s' →
    v i T s ≤ v i T s') ∧
  (∀ i (T : Finset (Fin m)), T.Nonempty → ∀ (s : Signal n) (x y : ℕ), InGrid k s → x < y → y < k →
    v i T (Function.update s i x) < v i T (Function.update s i y))

/-- SOS on the grid (Definition 2.13, inequality (1) with `d = 1`): raising coordinate `j`
from `x` to `x + δ` helps at least as much when the other coordinates are lower. -/
def IsSOS {n : ℕ} (k : ℕ) (w : Signal n → ℝ) : Prop :=
  ∀ (j : Fin n) (x δ : ℕ) (s s' : Signal n), InGrid k s → InGrid k s' → x + δ < k →
    (∀ l, l ≠ j → s' l ≤ s l) →
    w (Function.update s j (x + δ)) - w (Function.update s j x) ≤
      w (Function.update s' j (x + δ)) - w (Function.update s' j x)

/-- A feasible allocation restricted to the agent set `N` (Definition 2.11): bundles of
distinct agents are disjoint, and agents outside `N` receive nothing. -/
def IsAllocOn {n m : ℕ} (N : Finset (Fin n)) (T : Allocation n m) : Prop :=
  (Pairwise fun i j => Disjoint (T i) (T j)) ∧ ∀ i, i ∉ N → T i = ∅

/-- Social welfare of the allocation `T` at the profile `s`. -/
def welfare {n m : ℕ} (v : Valuation n m) (T : Allocation n m) (s : Signal n) : ℝ :=
  ∑ i, v i (T i) s

/-- Utility of agent `i` with true profile `s` who reports `y` while the others report
truthfully (Definition 2.12): value at the true profile of the bundle received at the
reported profile, minus the payment at the reported profile. -/
def utility {n m : ℕ} (v : Valuation n m) (x : AllocRule n m) (p : Payment n)
    (i : Fin n) (s : Signal n) (y : ℕ) : ℝ :=
  v i (x (Function.update s i y) i) s - p (Function.update s i y) i

/-- Ex-post incentive compatibility on the grid (Definition 2.4). -/
def IsExPostIC {n m : ℕ} (k : ℕ) (v : Valuation n m) (x : AllocRule n m) (p : Payment n) :
    Prop :=
  ∀ i s y, InGrid k s → y < k → utility v x p i s y ≤ utility v x p i s (s i)

/-- Ex-post individual rationality on the grid (Definition 2.5). -/
def IsExPostIR {n m : ℕ} (k : ℕ) (v : Valuation n m) (x : AllocRule n m) (p : Payment n) :
    Prop :=
  ∀ i s, InGrid k s → 0 ≤ utility v x p i s (s i)

/-- The OTHER term of display (7): `∑_i v_{i T_i}(s_{-i}, 0_i)`. -/
def other {n m : ℕ} (v : Valuation n m) (T : Allocation n m) (s : Signal n) : ℝ :=
  ∑ i, v i (T i) (Function.update s i 0)

/-- The SELF term of display (7): `∑_{ℓ=1}^{k-1} ∑_{i : s_i = ℓ} v_{i T_i}(0_{-i}, s_i)`. -/
def self {n m : ℕ} (k : ℕ) (v : Valuation n m) (T : Allocation n m) (s : Signal n) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 (k - 1), ∑ i ∈ Finset.univ.filter (fun i => s i = ℓ),
    v i (T i) (Function.update (0 : Signal n) i (s i))

end InterdepSOS.KHL


