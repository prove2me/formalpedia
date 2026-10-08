-- Prove2me | Definitions.Def_Dubey1986_Inefficiency_Setting
-- name    : Dubey1986_Inefficiency_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:38.485923+00:00
-- url     : https://prove2.me/theorems/9450f05d-62d5-461d-8114-0e251ca051aa
-- title:
--   p. 2 — simplices $S^i$, the $C^2$-normed game space $(U)^n$, open dense sets, $(s|e)$, $T$-efficient, Nash, efficient and strong Nash points
-- statement:
--   This file sets up the model of §2 of Dubey's paper.
--
--   There are $n$ players $N=\{1,\dots,n\}$. Player $i$ chooses a point of the **unit simplex**
--   $$S^i=\Big\{x\in\mathbb R^{k(i)}_+ : \sum_{j=1}^{k(i)} x_j\le 1\Big\}\subset\mathbb R^{k(i)},$$
--   a full-dimensional simplex whose vertices are the origin and the $k(i)$ unit vectors. A strategy profile is a point $s=(s^1,\dots,s^n)$ of $S=S^1\times\dots\times S^n$, viewed inside $\mathbb R^{r(n)}$ with $r(n)=\sum_i k(i)$ (player $i$'s block of coordinates holds $s^i$). A **vertex** of $S^i$ is an extreme point of $S^i$.
--
--   Fix open neighbourhoods $V^i\supseteq S^i$ and put $V=V^1\times\dots\times V^n$. A payoff function $f:V\to\mathbb R$ belongs to $U$ when it is $C^2$ on $V$ and its **$C^2$-norm**
--   $$\|f\|=\sup\{\|f(s)\|,\ \|Df(s)\|,\ \|D^2f(s)\| : s\in V\}$$
--   is finite. A **game** is $u=(u^1,\dots,u^n)\in(U)^n$, $u^i$ being player $i$'s payoff. A set $U_0\subseteq(U)^n$ is **open dense** when (1) it consists of games, (2) every $u\in U_0$ has an $\varepsilon>0$ such that every game $v$ with $\|v^i-u^i\|<\varepsilon$ for all $i$ lies in $U_0$, and (3) every game $u$ and every $\varepsilon>0$ admit $v\in U_0$ with $\|v^i-u^i\|<\varepsilon$ for all $i$.
--
--   For $s\in S$, $T\subseteq N$ and $e$, $(s|e)$ is the profile obtained from $s$ by replacing $s^i$ by $e^i$ for every $i\in T$. A point $s\in S$ is
--   1. **$T$-efficient** if there is no $e\in\times_{i\in T}S^i$ with $u^i(s|e)\ge u^i(s)$ for all $i\in T$ and $u^j(s|e)>u^j(s)$ for some $j\in T$;
--   2. a **Nash equilibrium** if it is $\{i\}$-efficient for every player $i$;
--   3. **efficient** if it is $N$-efficient;
--   4. a **strong Nash equilibrium** if it is $T$-efficient for every $T\subseteq N$.
--
--   $N(u)$, $E(u)$, $G(u)$ denote the sets of Nash, efficient and strong Nash points.
--
--   **Formalization Note** Players are `Fin n`, the profile space is `∀ i, Fin (k i) → ℝ`. The neighbourhoods $V^i$ are taken open (the paper says "neighborhoods"). Payoffs are total functions on $\mathbb R^{r(n)}$; only their values on $V$ matter. The $C^2$-norm takes values in $[0,\infty]$, so a game is required to have norm $<\infty$; Lean's norms on $\mathbb R^{r(n)}$ and on the derivative spaces are sup-type norms, equivalent to the Euclidean ones, so "open dense" means the same. Deviations $e$ are full profiles of which only the coordinates in $T$ are used.
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), p. 2 (§2, the model and definitions (1)–(4), footnote 1) and p. 3, first line

import Mathlib

namespace Dubey1986.Inefficiency

open scoped ENNReal

/-- The strategy space `ℝ^{r(n)}`, `r(n) = ∑ i, k i`: block `i` holds player `i`'s `k i`
coordinates. -/
abbrev Strat {n : ℕ} (k : Fin n → ℕ) : Type := ∀ i : Fin n, Fin (k i) → ℝ

/-- The unit simplex `S^i = {x ∈ ℝ_+^m : ∑ x_j ≤ 1}` (p. 2): the full-dimensional corner
simplex, with vertices `0` and the unit vectors. -/
def simplex (m : ℕ) : Set (Fin m → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∑ j, x j ≤ 1}

/-- The strategy-profile set `S = S^1 × ⋯ × S^n`. -/
def S {n : ℕ} (k : Fin n → ℕ) : Set (Strat k) :=
  Set.univ.pi fun i => simplex (k i)

/-- `x` is a vertex of the simplex `S^i ⊂ ℝ^m`: an extreme point. -/
def IsVertex (m : ℕ) (x : Fin m → ℝ) : Prop :=
  x ∈ Set.extremePoints ℝ (simplex m)

/-- The product `V = V^1 × ⋯ × V^n` of the neighbourhoods `V^i` of `S^i`. -/
def Vset {n : ℕ} {k : Fin n → ℕ} (V : ∀ i, Set (Fin (k i) → ℝ)) : Set (Strat k) :=
  Set.univ.pi V

/-- The `C²`-norm `sup {‖f s‖, ‖Df(s)‖, ‖D²f(s)‖ : s ∈ W}` (p. 2), valued in `ℝ≥0∞`. -/
noncomputable def c2Norm {n : ℕ} {k : Fin n → ℕ} (W : Set (Strat k)) (f : Strat k → ℝ) : ℝ≥0∞ :=
  ⨆ s ∈ W, (‖f s‖ₑ ⊔ ‖fderiv ℝ f s‖ₑ ⊔ ‖iteratedFDeriv ℝ 2 f s‖ₑ)

/-- `u = (u^1, …, u^n) ∈ (U)^n`: every payoff is `C²` on `V` with finite `C²`-norm. -/
def IsGame {n : ℕ} {k : Fin n → ℕ} (V : ∀ i, Set (Fin (k i) → ℝ))
    (u : Fin n → Strat k → ℝ) : Prop :=
  ∀ i, ContDiffOn ℝ 2 (u i) (Vset V) ∧ c2Norm (Vset V) (u i) < ⊤

/-- `U₀` is an open dense subset of `(U)^n` (product of the `C²`-norm topologies),
in ε-form. -/
def IsOpenDense {n : ℕ} {k : Fin n → ℕ} (V : ∀ i, Set (Fin (k i) → ℝ))
    (U₀ : Set (Fin n → Strat k → ℝ)) : Prop :=
  (∀ u ∈ U₀, IsGame V u) ∧
  (∀ u ∈ U₀, ∃ ε > 0, ∀ v, IsGame V v →
      (∀ i, c2Norm (Vset V) (v i - u i) < ENNReal.ofReal ε) → v ∈ U₀) ∧
  (∀ u, IsGame V u → ∀ ε > 0, ∃ v ∈ U₀,
      ∀ i, c2Norm (Vset V) (v i - u i) < ENNReal.ofReal ε)

/-- `(s|e)`: replace `s^i` by `e^i` for each `i ∈ T`. -/
def update {n : ℕ} {k : Fin n → ℕ} (s : Strat k) (T : Finset (Fin n)) (e : Strat k) :
    Strat k :=
  fun i => if i ∈ T then e i else s i

/-- `s` is `T`-efficient (p. 2, (1)): no `e ∈ ×_{i∈T} S^i` with `u^i(s|e) ≥ u^i(s)` for all
`i ∈ T` and `u^j(s|e) > u^j(s)` for some `j ∈ T`. -/
def IsTEfficient {n : ℕ} {k : Fin n → ℕ} (u : Fin n → Strat k → ℝ) (T : Finset (Fin n))
    (s : Strat k) : Prop :=
  ¬ ∃ e : Strat k, (∀ i ∈ T, e i ∈ simplex (k i)) ∧
      (∀ i ∈ T, u i s ≤ u i (update s T e)) ∧ ∃ j ∈ T, u j s < u j (update s T e)

/-- `N(u)`: the Nash equilibria (p. 2, (2)). -/
def NashSet {n : ℕ} {k : Fin n → ℕ} (u : Fin n → Strat k → ℝ) : Set (Strat k) :=
  {s | s ∈ S k ∧ ∀ i, IsTEfficient u {i} s}

/-- `E(u)`: the efficient points (p. 2, (3)). -/
def EffSet {n : ℕ} {k : Fin n → ℕ} (u : Fin n → Strat k → ℝ) : Set (Strat k) :=
  {s | s ∈ S k ∧ IsTEfficient u Finset.univ s}

/-- `G(u)`: the strong Nash equilibria (p. 2, (4)). -/
def StrongNashSet {n : ℕ} {k : Fin n → ℕ} (u : Fin n → Strat k → ℝ) : Set (Strat k) :=
  {s | s ∈ S k ∧ ∀ T, IsTEfficient u T s}

end Dubey1986.Inefficiency


