-- Prove2me | Definitions.Def_BlottoFPTAS_Main_Game
-- name    : BlottoFPTAS_Main_Game
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:39:57.529801+00:00
-- url     : https://prove2.me/theorems/e74c60d6-7683-4e46-bcb3-c0dc381538cf
-- title:
--   Continuous Colonel Blotto: allocations X(c), the tie-splitting share h, payoffs, mixed strategies, regrets, ε-Nash equilibria, U_w(μ; c), marginal CDFs and d
-- statement:
--   Two players $A$ and $B$ divide budgets $1$ and $b\in(0,1]$ among $n\ge1$ battlefields with common values $v_i>0$, $\sum_i v_i=1$. For a budget $c\ge0$ the **allocation set** is
--   $$X(c)=\Big\{x\in\mathbb R^n:\ x_i\ge0,\ \sum_{i=1}^n x_i\le c\Big\}.$$
--   The **share** of a player bidding $s$ against a bid $t$ is $h(s,t)=1$ if $s>t$, $\tfrac12$ if $s=t$ (including $0=0$), and $0$ if $s<t$. For a value vector $w$, `payoff w z x` $=\sum_i w_i h(z_i,x_i)$; the payoffs (1) are $u_A(x,y)=\sum_i v_ih(x_i,y_i)$ and $u_B(x,y)=\sum_i v_ih(y_i,x_i)$.
--
--   A **mixed strategy** with budget $c$ is a Borel probability measure $\mu$ on $\mathbb R^n$ with $\mu(X(c))=1$. For independent $X\sim\mu_A$, $Y\sim\mu_B$, $u_j(\mu_A,\mu_B)=\mathbb E[u_j(X,Y)]$ (integral against the product measure); $u_A(x,\mu_B)$ and $u_B(\mu_A,y)$ fix one pure allocation. The **regrets** (2) are
--   $$\mathrm{Reg}_A=\sup_{x\in X(1)}u_A(x,\mu_B)-u_A(\mu_A,\mu_B),\qquad \mathrm{Reg}_B=\sup_{y\in X(b)}u_B(\mu_A,y)-u_B(\mu_A,\mu_B),$$
--   and $(\mu_A,\mu_B)$ is an **$\varepsilon$-Nash equilibrium** when $\mu_A$, $\mu_B$ are strategies with budgets $1$, $b$ and both regrets are at most $\varepsilon$ ($\varepsilon=0$: Nash). The **opponent's supremum payoff** is $U_w(\mu;c)=\sup_{z\in X(c)}\mathbb E_{X\sim\mu}\big[\sum_iw_ih(z_i,X_i)\big]$, and `minSup m w c c'` $=\inf_P U_w(P;c')$ over strategies $P$ with budget $c$, so that §5.2's $C_1$, $C_\rho$ are `minSup m w 1 ρ` and `minSup m w ρ 1`. The **marginal CDF** is $F_{\mu,i}(t)=P_{X\sim\mu}(X_i\le t)$ and $d(\mu,\nu)=\max_i\sup_t|F_{\mu,i}(t)-F_{\nu,i}(t)|$. `uniformList L` is the uniform distribution on a finite list of allocations, counting repeats. An `Instance` packages rational data $(n,v,b)$ with $n\ge1$, $v_i>0$, $\sum_iv_i=1$, $0<b\le1$.
--
--   **Formalization Note.** Battlefields are `Fin n` (0-based). Suprema are real suprema over the subtype $X(c)$, which is nonempty for $c\ge0$ and on which payoffs are bounded; infima are over the nonempty set of strategies (the point mass at $0$).
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), pp. 4–6, §2, Eqs. (1)–(4); p. 31 (U_w, C₁, C_ρ)

import Mathlib

open scoped BigOperators
open MeasureTheory

namespace BlottoFPTAS.Main

/-!
# Continuous Colonel Blotto with common values (§2, pp. 4–6)

Bichler, Ghosh, *Efficient Equilibrium Computation in Colonel Blotto Games*, arXiv:2611.05221
(held version, sha256 cac3638e…), §2, pp. 4–6, Eqs. (1)–(4).

* Battlefields are `Fin n` (the paper's `[n] = {1, …, n}`, shifted to `0`-based indices).
* `w : Fin n → ℝ` is a value vector; the paper's game has `w = v` with `v_i > 0`, `∑ v_i = 1`.
  Payoff functions take the value vector as an argument because §5 uses several (`v`, `v′`,
  `v_red`, `v̂`).
* `X n c = {x ∈ ℝⁿ : x ≥ 0, ∑ x_i ≤ c}`; players `A` and `B` have budgets `1` and `b`.
* `share s t` is the paper's `h(s, t)`: `1` if `s > t`, `1/2` if `s = t`, `0` if `s < t`.
* A mixed strategy is a Borel probability measure on `Fin n → ℝ` giving full mass to `X n c`.
  Players' allocations are independent, so expected payoffs integrate against the product measure.
* Regrets are suprema over **all** feasible pure deviations in `X n c` (Eq. (2)); the supremum is
  taken over the subtype `X n c`, which is nonempty for `c ≥ 0` and on which payoffs are bounded.
-/

/-- The allocation set `X(c) = {x ∈ ℝⁿ_{≥0} : ∑_i x_i ≤ c}` (p. 4). -/
def X (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ c}

/-- The share `h(s, t)` of a player bidding `s` against a bid `t` (p. 5): `1` if `s > t`, `1/2` on
a tie (including `0 = 0`), `0` if `s < t`. -/
noncomputable def share (s t : ℝ) : ℝ :=
  if t < s then 1 else if s = t then 1 / 2 else 0

/-- The payoff `∑_i w_i h(z_i, x_i)` of a player bidding `z` against the opponent's bid `x`, for the
value vector `w`. With `w = v` this is `u_A(z, x)` when `z` is A's allocation and `u_B(x, z)` when
`z` is B's allocation (Eq. (1)). -/
noncomputable def payoff {n : ℕ} (w : Fin n → ℝ) (z x : Fin n → ℝ) : ℝ :=
  ∑ i, w i * share (z i) (x i)

/-- `u_A(x, y) = ∑_i v_i h(x_i, y_i)` (Eq. (1)). -/
noncomputable def uA {n : ℕ} (v : Fin n → ℝ) (x y : Fin n → ℝ) : ℝ :=
  payoff v x y

/-- `u_B(x, y) = ∑_i v_i h(y_i, x_i)` (Eq. (1)). -/
noncomputable def uB {n : ℕ} (v : Fin n → ℝ) (x y : Fin n → ℝ) : ℝ :=
  payoff v y x

/-- A mixed strategy with budget `c` (p. 5): a probability measure on `Fin n → ℝ` (Borel σ-algebra
of the product topology) giving full mass to `X(c)`. -/
def IsStrategy (n : ℕ) (c : ℝ) (μ : Measure (Fin n → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ μ (X n c)ᶜ = 0

/-- `u_A(μ_A, μ_B) = E[u_A(X, Y)]` for independent `X ∼ μ_A`, `Y ∼ μ_B` (p. 5). -/
noncomputable def expUA {n : ℕ} (v : Fin n → ℝ) (μA μB : Measure (Fin n → ℝ)) : ℝ :=
  ∫ p, uA v p.1 p.2 ∂(μA.prod μB)

/-- `u_B(μ_A, μ_B) = E[u_B(X, Y)]` for independent `X ∼ μ_A`, `Y ∼ μ_B` (p. 5). -/
noncomputable def expUB {n : ℕ} (v : Fin n → ℝ) (μA μB : Measure (Fin n → ℝ)) : ℝ :=
  ∫ p, uB v p.1 p.2 ∂(μA.prod μB)

/-- `u_A(x, μ_B)`: A plays the pure allocation `x` (p. 5). -/
noncomputable def pureUA {n : ℕ} (v : Fin n → ℝ) (x : Fin n → ℝ) (μB : Measure (Fin n → ℝ)) : ℝ :=
  ∫ y, uA v x y ∂μB

/-- `u_B(μ_A, y)`: B plays the pure allocation `y` (p. 5). -/
noncomputable def pureUB {n : ℕ} (v : Fin n → ℝ) (μA : Measure (Fin n → ℝ)) (y : Fin n → ℝ) : ℝ :=
  ∫ x, uB v x y ∂μA

/-- `Reg_A(μ_A, μ_B) = sup_{x ∈ X(1)} u_A(x, μ_B) − u_A(μ_A, μ_B)` (Eq. (2)). -/
noncomputable def regA {n : ℕ} (v : Fin n → ℝ) (μA μB : Measure (Fin n → ℝ)) : ℝ :=
  (⨆ x : X n 1, pureUA v x.1 μB) - expUA v μA μB

/-- `Reg_B(μ_A, μ_B) = sup_{y ∈ X(b)} u_B(μ_A, y) − u_B(μ_A, μ_B)` (Eq. (2)). -/
noncomputable def regB {n : ℕ} (v : Fin n → ℝ) (b : ℝ) (μA μB : Measure (Fin n → ℝ)) : ℝ :=
  (⨆ y : X n b, pureUB v μA y.1) - expUB v μA μB

/-- An `ε`-Nash equilibrium of the game `(n, v, b)` (p. 5): `μ_A` is a strategy with budget `1`,
`μ_B` a strategy with budget `b`, and both regrets are at most `ε`. `ε = 0` is a Nash
equilibrium. -/
def IsEpsNash {n : ℕ} (v : Fin n → ℝ) (b ε : ℝ) (μA μB : Measure (Fin n → ℝ)) : Prop :=
  IsStrategy n 1 μA ∧ IsStrategy n b μB ∧ regA v μA μB ≤ ε ∧ regB v b μA μB ≤ ε

/-- `U_w(μ; c) = sup_{z ∈ X(c)} E_{X∼μ}[∑_i w_i h(z_i, X_i)]`, the supremum expected payoff of an
opponent with budget `c ≥ 0` against `μ`, for the value vector `w` (p. 5; `U_w` p. 31). -/
noncomputable def U {n : ℕ} (w : Fin n → ℝ) (μ : Measure (Fin n → ℝ)) (c : ℝ) : ℝ :=
  ⨆ z : X n c, ∫ x, payoff w z.1 x ∂μ

/-- The marginal CDF `F_{μ,i}(t) = P_{X∼μ}(X_i ≤ t)` (p. 6). -/
noncomputable def marginalCDF {n : ℕ} (μ : Measure (Fin n → ℝ)) (i : Fin n) (t : ℝ) : ℝ :=
  (μ {x | x i ≤ t}).toReal

/-- `d(μ, ν) = max_i sup_t |F_{μ,i}(t) − F_{ν,i}(t)|` (p. 6). For probability measures each
supremum is over values in `[0, 1]`. -/
noncomputable def cdfDist {n : ℕ} (μ ν : Measure (Fin n → ℝ)) : ℝ :=
  ⨆ i : Fin n, ⨆ t : ℝ, |marginalCDF μ i t - marginalCDF ν i t|

/-- The optimization values of §5.2 (p. 31) for values `w` on `m` battlefields:
`minSup m w c c' = inf_P U_w(P; c')`, the infimum over strategies `P` with budget `c` of the
opponent's supremum payoff with budget `c'`. With budgets `1` and `ρ`, `C₁ = minSup m w 1 ρ`
and `C_ρ = minSup m w ρ 1`. The infimum is over the nonempty set of strategies (the point
mass at `0`), and every `U_w(P; c')` with `w ≥ 0` is bounded below by `0`. -/
noncomputable def minSup (m : ℕ) (w : Fin m → ℝ) (c c' : ℝ) : ℝ :=
  ⨅ P : {P : Measure (Fin m → ℝ) // IsStrategy m c P}, U w P.1 c'

/-- A game instance with rational data (§2.2, p. 6): `n ≥ 1` battlefields, positive rational values
summing to one, and a rational budget ratio `b ∈ (0, 1]`. -/
structure Instance where
  /-- The number of battlefields. -/
  n : ℕ
  /-- `n ≥ 1`. -/
  n_pos : 1 ≤ n
  /-- The common battlefield values. -/
  v : Fin n → ℚ
  /-- Every value is positive. -/
  v_pos : ∀ i, 0 < v i
  /-- The values sum to one. -/
  v_sum : ∑ i, v i = 1
  /-- B's budget. -/
  b : ℚ
  /-- `0 < b`. -/
  b_pos : 0 < b
  /-- `b ≤ 1`. -/
  b_le : b ≤ 1

/-- The real value vector of an instance. -/
noncomputable def Instance.vR (I : Instance) : Fin I.n → ℝ :=
  fun i => (I.v i : ℝ)

/-- The uniform distribution on a finite list of allocations, counting repeated entries
(`(1/|L|) ∑_{x ∈ L} δ_x`; the zero measure for the empty list). -/
noncomputable def uniformList {n : ℕ} (L : List (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  ((L.length : ENNReal)⁻¹) • (L.map fun x => Measure.dirac x).sum

end BlottoFPTAS.Main


