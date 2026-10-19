-- Prove2me | Definitions.Def_DERAggregation_Unregulated_Setting
-- name    : DERAggregation_Unregulated_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T11:24:21.880892+00:00
-- url     : https://prove2.me/theorems/dbee105d-124b-4966-9ff7-6e353e81dcf2
-- title:
--   §2–§3 — networked electricity market: prosumers, generators, the dispatch problems (9) and (21), (5a)-multipliers, two-part offers, Definition 1
-- statement:
--   The model of §2 (direct participation benchmark) and §3 (unregulated aggregation) of Gao, Alshehri and Birge.
--
--   **Market data.** A power network has a finite set $K$ of nodes and a finite set $L$ of transmission lines; the DC approximation of the network gives a matrix $B$ and line capacities $f$, and the network constraint reads $Bh\le f$ for the vector $h$ of nodal net injections. A finite set $I$ of prosumers is located at the nodes (prosumer $i$ at node $k(i)$); prosumer $i$ owns a DER capacity $C_i\ge 0$ and has a utility of consumption $u_i$ on $[0,Z]$. A finite set $J$ of generators is located at the nodes; generator $j$ produces $y_j\in[\underline y_j,\overline y_j]$ at cost $c_j(y_j)$.
--
--   **Assumption 1** (for each prosumer): $0\le C_i<Z$; $u_i$ is increasing, strictly concave and continuous on $[0,Z]$, differentiable on $(0,Z)$, with $u_i'(z)\to\infty$ as $z\to0^+$ and $u_i'(z)\to0$ as $z\to Z^-$. **Assumption 2** (for each generator): $\underline y_j<\overline y_j$; $c_j$ is increasing, strictly convex and continuous on $[\underline y_j,\overline y_j]$, differentiable on the open interval, with $c_j'\to0$ at $\underline y_j^+$ and $c_j'\to\infty$ at $\overline y_j^-$.
--
--   **Price-taking agents.** At the wholesale price $\lambda$, prosumer $i$ solves (1): maximize $\lambda z+u_i(C_i-z)$ over $C_i-Z\le z\le C_i$ ($z$ is the net sale); generator $j$ solves (3): maximize $\lambda y-c_j(y)$ over $[\underline y_j,\overline y_j]$.
--
--   **Benchmark dispatch (9).** With $X^k-D^k$ and $Y^k$ the nodal totals of the net sales $z=x-d$ and of the generation $y$, the ISO solves
--   $$\max\ \mathcal W_B=\sum_{i}u_i(C_i-z_i)-\sum_j c_j(y_j)$$
--   subject to (5a) $h=D-Y-X$, (5b) $\mathbf 1^\top h=0$, $Bh\le f$, and (6) $C-Z\le z\le C$, $\underline y\le y\le\overline y$.
--
--   **Aggregation dispatch (21).** In the unregulated aggregation model the ISO dispatches the sales $x$ and the purchases $d$ separately:
--   $$\max\ \mathcal W_A=\sum_i u_i(d_i+C_i-x_i)-\sum_j c_j(y_j)$$
--   subject to (5a), (5b) and (18) $0\le x\le C$, $0\le d\le Z-C+x$, $\underline y\le y\le\overline y$.
--
--   **Wholesale prices.** A vector $\lambda\in\mathbb R^K$ is a vector of optimal Lagrange multipliers of (5a) at a feasible point if, for some multiplier $\theta$ of $\mathbf 1^\top h=0$ and $\nu\ge0$ of $Bh\le f$ with complementary slackness $\nu^\top(f-Bh)=0$, the point maximizes the partial Lagrangian
--   $$\mathcal W+\sum_k\lambda^k\big(h^k+X^k-D^k+Y^k\big)-\theta\,\mathbf 1^\top h+\nu^\top(f-Bh)$$
--   over all $h$ and all participant decisions in the box (6) (resp. (18)). The wholesale prices of a model are the multipliers at an optimal solution of its dispatch problem.
--
--   **Two-part offers.** The aggregator offers prosumer $i$ a participation fee $P$ and a unit price $p$. At wholesale price $\lambda$ the prosumer's payoff (10) is $px-P+u(d+C-x)-\lambda d$ if she sells $x>0$, and $u(d+C)-\lambda d$ if $x=0$; she maximizes it over $x\in[0,C]$, $d\in[0,Z-C+x]$ (11). The aggregator's profit (13) from her is $P\,\mathbf 1\{x>0\}+(\lambda-p)x$ at her response $x$. A **Stackelberg equilibrium** of $\mathcal G(\lambda)$ (Definition 1) is a nonnegative offer vector $(P^*,p^*)$ with optimal responses $(x^*,d^*)$ such that, for every nonnegative offer $(P,p)$ and every vector of optimal responses to it, the aggregator's total profit (14) is at most that at $(P^*,p^*,x^*)$.
--
--   **Formalization Note** "Differentiable" in Assumptions 1–2 is read as differentiable on the open interval and continuous on the closed one, since the derivative limits make differentiability at the endpoints impossible; $0\le C_i$ is endnote 2 of the paper and $\underline y_j<\overline y_j$ is implicit. Multipliers are saddle points of the partial Lagrangian in which (5a) and (5b) are dualized and the participant box is kept as the domain (the paper's (98) also dualizes the box; for this concave program the multipliers of (5a) coincide). Optimal responses carry no tie-breaking rule. The typo $C^i_j$ in (20) is read as $C^k_i$.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), pp. 4–13, §2.1–§2.3 (Assumptions 1–3, (1), (3), (5)–(9)), §3.1–§3.5 ((10)–(15), Definition 1, (18), (20), (21)); Appendix p. 41, (98)

import Mathlib

namespace DERAggregation.Unregulated

open Filter Topology Set

/-- The data of the networked electricity market of §2–§3 (Gao, Alshehri, Birge, SSRN 3931052,
pp. 4–7, 13). `K` are the nodes, `I` the prosumers (prosumer `i` sits at node `loc i`), `J` the
conventional generators (generator `j` sits at node `gloc j`), `L` the transmission lines.
`B`, `f` are the DC network constraints `B h ≤ f`; `Z` is the consumption upper bound, `C i` the
DER capacity and `u i` the utility of consumption of prosumer `i`; `c j` is the cost function of
generator `j` on `[ylo j, yhi j]`. -/
structure Market (K I J L : Type) where
  loc : I → K
  gloc : J → K
  B : Matrix L K ℝ
  f : L → ℝ
  Z : ℝ
  C : I → ℝ
  u : I → ℝ → ℝ
  c : J → ℝ → ℝ
  ylo : J → ℝ
  yhi : J → ℝ

/-- Assumption 1 (p. 5) for one prosumer, with endnote 2 (`0 ≤ C`): `u` is increasing, strictly
concave and continuous on `[0, Z]`, differentiable on `(0, Z)`, `Z > C`, `u' → ∞` as `z → 0⁺` and
`u' → 0` as `z → Z⁻`. -/
def UtilAssm (u : ℝ → ℝ) (C Z : ℝ) : Prop :=
  0 ≤ C ∧ C < Z ∧ StrictMonoOn u (Icc 0 Z) ∧ StrictConcaveOn ℝ (Icc 0 Z) u ∧
    ContinuousOn u (Icc 0 Z) ∧ DifferentiableOn ℝ u (Ioo 0 Z) ∧
    Tendsto (deriv u) (𝓝[>] 0) atTop ∧ Tendsto (deriv u) (𝓝[<] Z) (𝓝 0)

/-- Assumption 2 (p. 6) for one generator: `c` is increasing, strictly convex and continuous on
`[lo, hi]` (`lo < hi`), differentiable on `(lo, hi)`, `c' → 0` as `y → lo⁺` and `c' → ∞` as
`y → hi⁻`. -/
def CostAssm (c : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  lo < hi ∧ StrictMonoOn c (Icc lo hi) ∧ StrictConvexOn ℝ (Icc lo hi) c ∧
    ContinuousOn c (Icc lo hi) ∧ DifferentiableOn ℝ c (Ioo lo hi) ∧
    Tendsto (deriv c) (𝓝[>] lo) (𝓝 0) ∧ Tendsto (deriv c) (𝓝[<] hi) atTop

/-- Assumption 1 for every prosumer of the market. -/
def Assumption1 {K I J L : Type} (M : Market K I J L) : Prop :=
  ∀ i, UtilAssm (M.u i) (M.C i) M.Z

/-- Assumption 2 for every generator of the market. -/
def Assumption2 {K I J L : Type} (M : Market K I J L) : Prop :=
  ∀ j, CostAssm (M.c j) (M.ylo j) (M.yhi j)

/-- Nodal total over the prosumers at node `k`: `∑_{i ∈ [n_k]} v^k_i`. -/
def nodeSum {K I J L : Type} [Fintype I] [DecidableEq K] (M : Market K I J L) (v : I → ℝ)
    (k : K) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => M.loc i = k), v i

/-- Nodal total over the generators at node `k`: `Y^k = ∑_{j ∈ [N_k]} y^k_j`. -/
def genSum {K I J L : Type} [Fintype J] [DecidableEq K] (M : Market K I J L) (y : J → ℝ)
    (k : K) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => M.gloc j = k), y j

/-! ### The price-taking agents, (1) and (3) -/

/-- The prosumer's payoff (1): `π(z) = λ z + u(C − z)`. -/
def prosPay (lam : ℝ) (u : ℝ → ℝ) (C z : ℝ) : ℝ := lam * z + u (C - z)

/-- `z` is an optimal solution of the prosumer's problem (1):
`max λ z + u(C − z)` subject to `C − Z ≤ z ≤ C`. -/
def IsOptPros (u : ℝ → ℝ) (C Z lam z : ℝ) : Prop :=
  z ∈ Icc (C - Z) C ∧ ∀ z' ∈ Icc (C - Z) C, prosPay lam u C z' ≤ prosPay lam u C z

/-- The generator's payoff (3): `π̂(y) = λ y − c(y)`. -/
def genPay (lam : ℝ) (c : ℝ → ℝ) (y : ℝ) : ℝ := lam * y - c y

/-- `y` is an optimal solution of the generator's problem (3) on `[lo, hi]`. -/
def IsOptGen (c : ℝ → ℝ) (lo hi lam y : ℝ) : Prop :=
  y ∈ Icc lo hi ∧ ∀ y' ∈ Icc lo hi, genPay lam c y' ≤ genPay lam c y

/-! ### The benchmark economic dispatch (9) -/

section Dispatch

variable {K I J L : Type} [Fintype K] [DecidableEq K] [Fintype I] [Fintype J] [Fintype L]

/-- The participant box (6) of the benchmark, in the net sale `z = x − d`:
`C − Z ≤ z ≤ C` and `y̲ ≤ y ≤ ȳ`. -/
def BoxB (M : Market K I J L) (z : I → ℝ) (y : J → ℝ) : Prop :=
  (∀ i, M.C i - M.Z ≤ z i ∧ z i ≤ M.C i) ∧ (∀ j, M.ylo j ≤ y j ∧ y j ≤ M.yhi j)

/-- The constraints (5)–(6) of the benchmark dispatch (9): nodal balance (5a)
`h = D − Y − X` (with `X − D` the nodal total of `z = x − d`), network constraints (5b)
`1ᵀh = 0`, `Bh ≤ f`, and the box (6). -/
def FeasB (M : Market K I J L) (h : K → ℝ) (z : I → ℝ) (y : J → ℝ) : Prop :=
  (∀ k, h k = -(nodeSum M z k) - genSum M y k) ∧
    ∑ k, h k = 0 ∧ (∀ l, Matrix.mulVec M.B h l ≤ M.f l) ∧ BoxB M z y

/-- The social welfare (8): `W_B = ∑_i u_i(C_i − z_i) − ∑_j c_j(y_j)` with `z = x − d`. -/
def WB (M : Market K I J L) (z : I → ℝ) (y : J → ℝ) : ℝ :=
  ∑ i, M.u i (M.C i - z i) - ∑ j, M.c j (y j)

/-- `(h, z, y)` is an optimal solution of the benchmark dispatch (9). -/
def IsOptB (M : Market K I J L) (h : K → ℝ) (z : I → ℝ) (y : J → ℝ) : Prop :=
  FeasB M h z y ∧ ∀ h' z' y', FeasB M h' z' y' → WB M z' y' ≤ WB M z y

/-- The partial Lagrangian of (9) (cf. (98), p. 41): (5a) is dualized with multipliers `λ`,
`1ᵀh = 0` with `θ` and `Bh ≤ f` with `ν ≥ 0`; the box (6) is kept as the domain. -/
def LagB (M : Market K I J L) (lam : K → ℝ) (θ : ℝ) (ν : L → ℝ) (h : K → ℝ) (z : I → ℝ)
    (y : J → ℝ) : ℝ :=
  WB M z y + ∑ k, lam k * (h k + nodeSum M z k + genSum M y k) - θ * ∑ k, h k +
    ∑ l, ν l * (M.f l - Matrix.mulVec M.B h l)

/-- `λ` is a vector of optimal Lagrange multipliers of (5a) at the point `(h, z, y)` of (9):
there are `θ` and `ν ≥ 0` with complementary slackness such that `(h, z, y)` maximizes the
partial Lagrangian over all `h` and the box (6). -/
def IsMultB (M : Market K I J L) (lam : K → ℝ) (h : K → ℝ) (z : I → ℝ) (y : J → ℝ) : Prop :=
  ∃ (θ : ℝ) (ν : L → ℝ), (∀ l, 0 ≤ ν l) ∧ ∑ l, ν l * (M.f l - Matrix.mulVec M.B h l) = 0 ∧
    ∀ h' z' y', BoxB M z' y' → LagB M lam θ ν h' z' y' ≤ LagB M lam θ ν h z y

/-- `λ` is a vector of wholesale prices of the benchmark model: the optimal Lagrange
multipliers of (5a) at an optimal solution of (9). -/
def IsPriceB (M : Market K I J L) (lam : K → ℝ) : Prop :=
  ∃ h z y, IsOptB M h z y ∧ IsMultB M lam h z y

/-! ### The aggregation economic dispatch (21) -/

/-- The participant constraints (18): `0 ≤ x ≤ C`, `0 ≤ d ≤ Z − C + x`, `y̲ ≤ y ≤ ȳ`. -/
def BoxA (M : Market K I J L) (x d : I → ℝ) (y : J → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ M.C i) ∧ (∀ i, 0 ≤ d i ∧ d i ≤ M.Z - M.C i + x i) ∧
    (∀ j, M.ylo j ≤ y j ∧ y j ≤ M.yhi j)

/-- The constraints (5), (18) of the aggregation dispatch (21): nodal balance (5a)
`h = D − Y − X`, network constraints (5b) and the box (18). -/
def FeasA (M : Market K I J L) (h : K → ℝ) (x d : I → ℝ) (y : J → ℝ) : Prop :=
  (∀ k, h k = nodeSum M d k - genSum M y k - nodeSum M x k) ∧
    ∑ k, h k = 0 ∧ (∀ l, Matrix.mulVec M.B h l ≤ M.f l) ∧ BoxA M x d y

/-- The social welfare (20): `W_A = ∑_i u_i(d_i + C_i − x_i) − ∑_j c_j(y_j)`. -/
def WA (M : Market K I J L) (x d : I → ℝ) (y : J → ℝ) : ℝ :=
  ∑ i, M.u i (d i + M.C i - x i) - ∑ j, M.c j (y j)

/-- `(h, x, d, y)` is an optimal solution of the aggregation dispatch (21). -/
def IsOptA (M : Market K I J L) (h : K → ℝ) (x d : I → ℝ) (y : J → ℝ) : Prop :=
  FeasA M h x d y ∧ ∀ h' x' d' y', FeasA M h' x' d' y' → WA M x' d' y' ≤ WA M x d y

/-- The partial Lagrangian of (21): (5a) dualized with `λ`, (5b) with `θ` and `ν ≥ 0`; the box
(18) is kept as the domain. -/
def LagA (M : Market K I J L) (lam : K → ℝ) (θ : ℝ) (ν : L → ℝ) (h : K → ℝ) (x d : I → ℝ)
    (y : J → ℝ) : ℝ :=
  WA M x d y + ∑ k, lam k * (h k + nodeSum M x k - nodeSum M d k + genSum M y k) -
    θ * ∑ k, h k + ∑ l, ν l * (M.f l - Matrix.mulVec M.B h l)

/-- `λ` is a vector of optimal Lagrange multipliers of (5a) at the point `(h, x, d, y)` of (21). -/
def IsMultA (M : Market K I J L) (lam : K → ℝ) (h : K → ℝ) (x d : I → ℝ) (y : J → ℝ) : Prop :=
  ∃ (θ : ℝ) (ν : L → ℝ), (∀ l, 0 ≤ ν l) ∧ ∑ l, ν l * (M.f l - Matrix.mulVec M.B h l) = 0 ∧
    ∀ h' x' d' y', BoxA M x' d' y' → LagA M lam θ ν h' x' d' y' ≤ LagA M lam θ ν h x d y

/-- `λ` is a vector of wholesale prices of the unregulated aggregation model: the optimal
Lagrange multipliers of (5a) at an optimal solution of (21). -/
def IsPriceA (M : Market K I J L) (lam : K → ℝ) : Prop :=
  ∃ h x d y, IsOptA M h x d y ∧ IsMultA M lam h x d y

end Dispatch

/-! ### Two-part offers: the prosumer's problem (10)–(11) and the aggregator's profit (13) -/

/-- The prosumer's payoff (10) under the two-part offer `(P, p)` at wholesale price `λ`. -/
noncomputable def pay2 (u : ℝ → ℝ) (C lam P p x d : ℝ) : ℝ :=
  if 0 < x then p * x - P + u (d + C - x) - lam * d else u (d + C) - lam * d

/-- The feasible set of (11): `x ∈ [0, C]`, `d ∈ [0, Z − C + x]`. -/
def Feas2 (C Z x d : ℝ) : Prop := 0 ≤ x ∧ x ≤ C ∧ 0 ≤ d ∧ d ≤ Z - C + x

/-- `(x, d)` is an optimal solution of the prosumer's problem (11) (an optimal response to the
offer `(P, p)`); no tie-breaking rule is imposed. -/
def IsResp (u : ℝ → ℝ) (C Z lam P p x d : ℝ) : Prop :=
  Feas2 C Z x d ∧ ∀ x' d', Feas2 C Z x' d' → pay2 u C lam P p x' d' ≤ pay2 u C lam P p x d

/-- The aggregator's profit (13) from one prosumer: `P·1{x > 0} + (λ − p) x`. -/
noncomputable def aggProfit (lam P p x : ℝ) : ℝ :=
  P * (if 0 < x then 1 else 0) + (lam - p) * x

/-- Definition 1 (p. 12): `(P, p, x)` (with the purchases `d`) is a Stackelberg equilibrium of
the game `G(λ)`: the offers are nonnegative, each `(x i, d i)` is an optimal response of
prosumer `i` to `(P i, p i)`, and no nonnegative offer `(P', p')` yields the aggregator a larger
total profit (14) against any optimal responses `(x', d')` to it. -/
def IsStackelberg {K I J L : Type} [Fintype I] (M : Market K I J L) (lam : K → ℝ)
    (P p x d : I → ℝ) : Prop :=
  (∀ i, 0 ≤ P i ∧ 0 ≤ p i) ∧
    (∀ i, IsResp (M.u i) (M.C i) M.Z (lam (M.loc i)) (P i) (p i) (x i) (d i)) ∧
    ∀ P' p' x' d' : I → ℝ, (∀ i, 0 ≤ P' i ∧ 0 ≤ p' i) →
      (∀ i, IsResp (M.u i) (M.C i) M.Z (lam (M.loc i)) (P' i) (p' i) (x' i) (d' i)) →
      ∑ i, aggProfit (lam (M.loc i)) (P' i) (p' i) (x' i) ≤
        ∑ i, aggProfit (lam (M.loc i)) (P i) (p i) (x i)

end DERAggregation.Unregulated


