-- Prove2me | Definitions.Def_NetworkQuality_PotentialMax_Setting
-- name    : NetworkQuality_PotentialMax_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:25.042683+00:00
-- url     : https://prove2.me/theorems/9c870eea-af8e-4057-88fa-01c14e62a5fe
-- title:
--   §3.1, §3.2, §3.5 — the network market (7), strong network effects, stage-2 Nash equilibria, the potential (10), potential maximization and the firm's profit under it
-- statement:
--   A monopolist sells a network good to a finite set of consumers $N=\{1,\dots,n\}$, $n\ge 1$. In stage 1 it chooses a price $p\ge 0$ and a quality $q\ge 0$; in stage 2 the consumers simultaneously decide whether to buy.
--
--   **Primitives and standing assumptions** (pp. 4, 9). A market consists of
--   1. valuations $v_i>0$, labelled so that $v_1\ge v_2\ge\dots\ge v_n$ ("without loss of generality assume $v_i$ is decreasing in $i$");
--   2. a benefit $f(k,q)$ of the good when $k$ consumers buy and quality is $q$, with $f(k,q)\ge 0$, weakly increasing in the number of buyers $k\ge 1$, and, in quality, weakly increasing on $[0,\infty)$ and differentiable on $(0,\infty)$;
--   3. a cost of quality $c(q)\ge 0$, weakly increasing on $[0,\infty)$ and differentiable on $(0,\infty)$.
--
--   **Payoffs (7).** If $B\subseteq N$ is the set of buyers, consumer $i$ receives
--   $$u_i(B,p,q)=\begin{cases} v_i\,f(|B|,q)-p & i\in B,\\ 0 & i\notin B.\end{cases}$$
--
--   **Strong network effects at $q$** (Proposition 1, p. 10): $i\mapsto v_i f(i,q)$ is strictly increasing on $\{1,\dots,n\}$.
--
--   **Nash equilibrium of stage 2.** A buyer set $B$ is a (pure-strategy) Nash equilibrium at $(p,q)$ if no buyer $i\in B$ gains by not buying, $u_i(B\setminus\{i\},p,q)\le u_i(B,p,q)$, and no non-buyer $i\notin B$ gains by buying, $u_i(B\cup\{i\},p,q)\le u_i(B,p,q)$.
--
--   **Potential (10)** (p. 13):
--   $$\Phi(B,p,q)=\sum_{i=1}^{|B|} f(i,q)-p\sum_{i\in B}\frac{1}{v_i}.$$
--   A **potential maximizer** is a buyer set $B$ with $\Phi(B',p,q)\le\Phi(B,p,q)$ for every $B'\subseteq N$, i.e. $B\in\arg\max_{B'\subseteq N}\Phi(B',p,q)$ (p. 14).
--
--   **Profit under potential maximization.** The firm's profit with buyer set $B$ is $\pi(B,p,q)=|B|p-c(q)$ (p. 9). When the firm anticipates that stage 2 plays the potential maximizer, its profit is
--   $$\Pi(p,q)=\begin{cases} np-c(q) & \text{if } N \text{ is a potential maximizer of } \Phi(\cdot,p,q),\\ -c(q) & \text{otherwise.}\end{cases}$$
--   Under strong network effects the only potential maximizers are $N$ and $\emptyset$ (see the (12) milestone), so "otherwise" is the outcome in which nobody buys; at a tie $\Phi(N)=\Phi(\emptyset)$ the outcome "all buy" is selected, as in the paper's "if and only if $p\le\dots$" in (12).
--
--   These objects are the whole model of §3 of the paper, and every statement of the mission is phrased in terms of them.
--
--   **Formalization Note** Consumers are `Fin n`, so the paper's consumer $i$ is Lean index $i-1$; the first argument of `f` is a number of buyers in `ℕ`, so $f(i,q)$ for consumer $i$ is `f (i.val + 1) q`. `f` and `c` are total functions on `ℝ`; every assumption on them is imposed for quality $q\ge 0$ only (differentiability for $q>0$) and, for `f`, for numbers of buyers $k\ge 1$ only. "Increasing" and "decreasing" are read weakly. The "sufficiently convex" assumption on $c$ (p. 4) is not part of the standing assumptions: it is not pinned down and serves only the sufficiency of first-order conditions. Equilibria are pure: buyer sets.
-- source:
--   Chan, Quality Strategies in Network Markets, SSRN 4203818 (version of April 2023), pp. 4, 9–10, 13–14, (7), (10), Proposition 1

import Mathlib

namespace NetworkQuality.PotentialMax

open Classical

/-- The primitives of the multi-consumer network-good model (Chan, SSRN 4203818, §2 p. 4 and §3.1 p. 9).
Consumers `N = {1, …, n}` are `Fin n`: the paper's consumer `i` is index `i - 1`.
* `v i` is consumer `i`'s valuation `v_i`;
* `f k q` is the benefit `f(k, q)` of the network good when `k` consumers buy and quality is `q`;
* `c q` is the firm's cost of quality `c(q)`. -/
structure Market (n : ℕ) where
  v : Fin n → ℝ
  f : ℕ → ℝ → ℝ
  c : ℝ → ℝ

namespace Market

variable {n : ℕ} (M : Market n)

/-- The standing assumptions of pp. 4 and 9: `N` is nonempty; `v_i ∈ ℝ₊₊`, labelled so that `v_i`
is (weakly) decreasing in `i`; `f : ℤ₊ × ℝ₊ → ℝ₊` is increasing in the number of buyers and increasing
and differentiable in quality; `c(q) ≥ 0` is increasing and differentiable. Every condition on `f`
is imposed for numbers of buyers `k ≥ 1` only, and every condition on `f` and `c` for quality
`q ≥ 0` only (differentiability on `q > 0`). "Increasing" is read as weakly increasing. -/
def Standing : Prop :=
  0 < n ∧
  (∀ i, 0 < M.v i) ∧
  Antitone M.v ∧
  (∀ k q, 1 ≤ k → 0 ≤ q → 0 ≤ M.f k q) ∧
  (∀ q, 0 ≤ q → MonotoneOn (fun k => M.f k q) (Set.Ici 1)) ∧
  (∀ k, 1 ≤ k → MonotoneOn (M.f k) (Set.Ici 0)) ∧
  (∀ k, 1 ≤ k → DifferentiableOn ℝ (M.f k) (Set.Ioi 0)) ∧
  (∀ q, 0 ≤ q → 0 ≤ M.c q) ∧
  MonotoneOn M.c (Set.Ici 0) ∧
  DifferentiableOn ℝ M.c (Set.Ioi 0)

/-- Strong network effects at quality `q` (Proposition 1, p. 10): `v_i f(i, q)` is strictly
increasing in `i`. -/
def StrongNE (q : ℝ) : Prop :=
  StrictMono (fun i : Fin n => M.v i * M.f (i.val + 1) q)

/-- The payoff (7) of consumer `i` when the buyer set is `B`, the price `p` and the quality `q`. -/
noncomputable def u (i : Fin n) (B : Finset (Fin n)) (p q : ℝ) : ℝ :=
  if i ∈ B then M.v i * M.f B.card q - p else 0

/-- `B` is a (pure-strategy) Nash equilibrium of the stage-2 subgame at `(p, q)`: no buyer gains by
not buying, and no non-buyer gains by buying. -/
def IsNash (B : Finset (Fin n)) (p q : ℝ) : Prop :=
  (∀ i ∈ B, M.u i (B.erase i) p q ≤ M.u i B p q) ∧
  (∀ i ∉ B, M.u i (insert i B) p q ≤ M.u i B p q)

/-- The potential (10): `Φ(B, p, q) = ∑_{i=1}^{|B|} f(i, q) − p ∑_{i ∈ B} 1 / v_i`. -/
noncomputable def pot (B : Finset (Fin n)) (p q : ℝ) : ℝ :=
  ∑ k ∈ Finset.range B.card, M.f (k + 1) q - p * ∑ i ∈ B, 1 / M.v i

/-- `B` is a potential maximizer: `B ∈ arg max_{B' ⊆ N} Φ(B', p, q)` (p. 14). -/
def IsPotMax (B : Finset (Fin n)) (p q : ℝ) : Prop :=
  ∀ B' : Finset (Fin n), M.pot B' p q ≤ M.pot B p q

/-- The firm's profit `|B| p − c(q)` (p. 9) when stage 2 is played according to potential
maximization: all consumers buy (`B = N`) when `N` is a potential maximizer of `Φ(·, p, q)`
(ties resolved in the firm's favour, as in (12)), and otherwise the selected outcome is taken to be
`B = ∅`. -/
noncomputable def profitPM (p q : ℝ) : ℝ :=
  if M.IsPotMax Finset.univ p q then (n : ℝ) * p - M.c q else - M.c q

end Market

end NetworkQuality.PotentialMax


