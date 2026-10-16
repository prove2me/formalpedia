-- Prove2me | Definitions.Def_OnDemandDelivery_RouteElim_Setting
-- name    : OnDemandDelivery_RouteElim_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:28.410994+00:00
-- url     : https://prove2.me/theorems/09a2bc46-5ca9-4dc2-8844-a32774bb4985
-- title:
--   §5.1 and Appendix G — the routing subproblem SF1 (24)–(25), its LP relaxation RF1 (26)–(27) and dual, the reduced cost (33), and the restricted problems SF1_r, RF1_r (75)–(79)
-- statement:
--   Fix one period $n$ of the dispatching and routing problem of Liu and Luo, and a feasible solution $(\bar{\mathbf x},\bar{\mathbf z})$ of the Benders master problem. The **routing subproblem** is described by the following data:
--
--   1. a finite set $\mathcal R^n$ of feasible routes, a finite set $\mathcal I^n$ of current customer locations, and the finite set $\{n+1,\dots,N\}$ of future periods;
--   2. a cost $c_r$ for each route $r\in\mathcal R^n$;
--   3. coefficients $\alpha_{i,r}$, indicating whether location $i\in\mathcal I^n$ is served in route $r$, and $\beta_{n',r}$, indicating whether route $r$ is still running in period $n'$;
--   4. the fleet size $\bar K\in\mathbb N$, the number $\zeta^n_n\in\mathbb N$ of drivers still en route in period $n$, and the master values $\bar z^{n'}_k$, $k=0,\dots,\bar K$.
--
--   The **standing assumptions** are $\alpha_{i,r},\beta_{n',r}\in\{0,1\}$, $\bar z^{n'}_k\in\{0,1\}$ and $\sum_{k=0}^{\bar K}\bar z^{n'}_k=1$. Write $b_{n'}=\sum_{k=0}^{\bar K}k\,\bar z^{n'}_k$ and $\operatorname{cost}(\theta)=\sum_{r}\theta_r c_r$.
--
--   **SF1** asks for $\theta\in\{0,1\}^{\mathcal R^n}$ minimizing $\operatorname{cost}(\theta)$ subject to
--   $$\sum_{r}\beta_{n',r}\theta_r\le b_{n'}\ (\forall n'),\qquad \sum_r\theta_r\le \bar K-\zeta^n_n,\qquad \sum_r\alpha_{i,r}\theta_r=1\ (\forall i\in\mathcal I^n).$$
--   An optimal solution is a feasible $\theta$ whose cost is at most that of every feasible point. **RF1** is the linear relaxation with $\theta\ge 0$ real and the covering rows $\sum_r\alpha_{i,r}\theta_r\ge 1$ in place of the equalities.
--
--   The **dual of RF1** has variables $\mu_{n'}$ for the rows (25), $\mu_n$ for (19) and $\nu_i$ for (26). It is feasible when $\mu_{n'}\le 0$, $\mu_n\le 0$, $\nu_i\ge 0$ and $\sum_i\alpha_{i,r}\nu_i+\sum_{n'}\beta_{n',r}\mu_{n'}+\mu_n\le c_r$ for every route $r$. Its objective is $\sum_{n'}\mu_{n'}b_{n'}+\mu_n(\bar K-\zeta^n_n)+\sum_i\nu_i$, and a dual optimal solution is a dual feasible point maximizing this objective over the dual feasible set. The **reduced cost** of route $r$ is
--   $$c_r-\sum_{i\in\mathcal I^n}\alpha_{i,r}\nu_i-\sum_{n'=n+1}^N\beta_{n',r}\mu_{n'}-\mu_n .$$
--
--   For a route $r$, let $\mathcal I^n_r=\{i\mid\alpha_{i,r}=0\}$ and let $\mathcal R^n_r$ be the routes covering locations only in $\mathcal I^n_r$. **SF1$_r$** asks for binary $\theta'$ supported on $\mathcal R^n_r$ with
--   $$\sum_{r'}\beta_{n',r'}\theta'_{r'}\le b_{n'}-\beta_{n',r},\qquad \sum_{r'}\theta'_{r'}\le\bar K-\zeta^n_n-1,\qquad \sum_{r'}\alpha_{i,r'}\theta'_{r'}=1\ (i\in\mathcal I^n_r).$$
--   Its optimal cost $\phi(\mathrm{SF1}_r)$ is an extended real, $+\infty$ when SF1$_r$ is infeasible. **RF1$_r$** (75)–(79) has the same constraints with $\theta'\ge 0$ real. Its dual has $\mu_{n'}\le0$, $\mu_n\le 0$, $\nu_i$ free for $i\in\mathcal I^n_r$, the column constraints of the routes in $\mathcal R^n_r$, and objective $\sum_{n'}\sum_{k}\mu_{n'}k\bar z^{n'}_k-\sum_{n'}\beta_{n',r}\mu_{n'}+\mu_n(\bar K-\zeta^n_n-1)+\sum_{i\in\mathcal I^n_r}\nu_i$.
--
--   These objects are the setting of Lemma 2 (route elimination) and of its proof in Appendix G.
--
--   **Formalization Note** Routes, locations and future periods are arbitrary finite types; vectors over routes are real functions, and support on $\mathcal R^n_r$ is the condition $\theta'_{r'}=0$ for $r'\notin\mathcal R^n_r$. "Route $r'$ covers location $i$" is read as $\alpha_{i,r'}\neq 0$. The paper does not print the dual signs; the standard ones for a minimization (nonpositive on $\le$ rows, nonnegative on $\ge$ rows, free on equality rows) are used. SF1$_r$'s right-hand sides are reduced by $r$'s own use, as in RF1$_r$ (76)–(77); (76) prints $z^{n'}_k$ without the bar, read as the master value $\bar z^{n'}_k$. The double sum $\sum_{n'}\sum_k\bar\mu_{n'}k\bar z^{n'}_k$ is written as $\sum_{n'}\bar\mu_{n'}b_{n'}$. $\bar K-\zeta^n_n$ is computed in the reals.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, pp. 15–17, (17), (19)–(22), (24)–(27), (29), and p. 19, (33), and Appendix G, p. 42, (75)–(79)

import Mathlib

namespace OnDemandDelivery.RouteElim

open Finset

/-- The data of the single-period routing subproblem **SF1** of Liu–Luo (arXiv:2107.13058v3, §5.1,
pp. 15–16) for one period `n` and a fixed master solution `(x̄, z̄)`.

* `R` is the finite set `ℛⁿ` of feasible routes, `I` the set `ℐⁿ` of current customers (locations),
  `P` the set `{n+1, …, N}` of future periods;
* `c r` is the cost `c_r` of route `r`, `α i r` is `α_{i,r}` (route `r` serves location `i`),
  `β p r` is `β_{n′,r}` (route `r` is still running in period `n′ = p`);
* `Kbar` is the fleet size `K̄`, `ζn` the number `ζⁿₙ` of drivers still en route in period `n`;
* `zbar p k` is the master solution's `z̄^{n′}_k` (`n′ = p`, used for `k = 0, …, K̄`). -/
structure Data (R I P : Type) where
  /-- `c_r`, the cost of route `r`. -/
  c : R → ℝ
  /-- `α_{i,r}`: whether location `i` is served in route `r`. -/
  α : I → R → ℝ
  /-- `β_{n′,r}`: whether route `r` is running in future period `n′`. -/
  β : P → R → ℝ
  /-- The fleet size `K̄`. -/
  Kbar : ℕ
  /-- `ζⁿₙ`, the drivers dispatched earlier and still en route in period `n`. -/
  ζn : ℕ
  /-- The master solution `z̄^{n′}_k`. -/
  zbar : P → ℕ → ℝ

variable {R I P : Type} [Fintype R] [Fintype I] [Fintype P]

namespace Data

variable (D : Data R I P)

/-- The standing assumptions of §5.1 (pp. 15–16): `α_{i,r}, β_{n′,r} ∈ {0,1}`, and the master solution
satisfies `z̄^{n′}_k ∈ {0,1}` for `k = 0, …, K̄` (21) and `∑_{k=0}^{K̄} z̄^{n′}_k = 1` (17). -/
def Standing : Prop :=
  (∀ i r, D.α i r = 0 ∨ D.α i r = 1) ∧
  (∀ p r, D.β p r = 0 ∨ D.β p r = 1) ∧
  (∀ p k, k ≤ D.Kbar → D.zbar p k = 0 ∨ D.zbar p k = 1) ∧
  (∀ p, ∑ k ∈ range (D.Kbar + 1), D.zbar p k = 1)

/-- The right-hand side of (25): `b_{n′} = ∑_{k=0}^{K̄} k z̄^{n′}_k`. -/
def b (p : P) : ℝ := ∑ k ∈ range (D.Kbar + 1), (k : ℝ) * D.zbar p k

/-- The objective (24): `∑_{r ∈ ℛⁿ} θ_r c_r`. -/
def cost (θ : R → ℝ) : ℝ := ∑ r, θ r * D.c r

/-- Feasibility for **SF1** (24)–(25), (19), (20), (22): binary `θ` with
`∑_r β_{n′,r} θ_r ≤ b_{n′}` for every `n′`, `∑_r θ_r ≤ K̄ − ζⁿₙ`, and `∑_r α_{i,r} θ_r = 1` for every `i`. -/
def SF1Feasible (θ : R → ℝ) : Prop :=
  (∀ p, ∑ r, D.β p r * θ r ≤ D.b p) ∧
  (∑ r, θ r ≤ (D.Kbar : ℝ) - D.ζn) ∧
  (∀ i, ∑ r, D.α i r * θ r = 1) ∧
  (∀ r, θ r = 0 ∨ θ r = 1)

/-- An optimal solution of **SF1**: feasible, with cost at most that of every feasible `θ'`. -/
def SF1Optimal (θ : R → ℝ) : Prop :=
  D.SF1Feasible θ ∧ ∀ θ', D.SF1Feasible θ' → D.cost θ ≤ D.cost θ'

/-- Feasibility for the LP relaxation **RF1** (24), (19), (25), (26), (27): real `θ ≥ 0` with
`∑_r β_{n′,r} θ_r ≤ b_{n′}`, `∑_r θ_r ≤ K̄ − ζⁿₙ`, and the covering rows `∑_r α_{i,r} θ_r ≥ 1`. -/
def RF1Feasible (θ : R → ℝ) : Prop :=
  (∀ p, ∑ r, D.β p r * θ r ≤ D.b p) ∧
  (∑ r, θ r ≤ (D.Kbar : ℝ) - D.ζn) ∧
  (∀ i, 1 ≤ ∑ r, D.α i r * θ r) ∧
  (∀ r, 0 ≤ θ r)

/-- Dual feasibility for **RF1**, with dual variables `μ_{n′}` of (25), `μₙ` of (19) and `νᵢ` of (26):
`μ ≤ 0`, `μₙ ≤ 0` (rows `≤` of a minimization), `ν ≥ 0` (rows `≥`), and for every route `r`
`∑_i α_{i,r} νᵢ + ∑_{n′} β_{n′,r} μ_{n′} + μₙ ≤ c_r` (column of `θ_r ≥ 0`). -/
def DualFeasible (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) : Prop :=
  (∀ p, μ p ≤ 0) ∧ μn ≤ 0 ∧ (∀ i, 0 ≤ ν i) ∧
  ∀ r, ∑ i, D.α i r * ν i + ∑ p, D.β p r * μ p + μn ≤ D.c r

/-- The dual objective of **RF1** (the left side of (29)):
`∑_{n′} μ_{n′} b_{n′} + μₙ (K̄ − ζⁿₙ) + ∑_i νᵢ`. -/
def dualObjective (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) : ℝ :=
  ∑ p, μ p * D.b p + μn * ((D.Kbar : ℝ) - D.ζn) + ∑ i, ν i

/-- A dual optimal solution of **RF1**: dual feasible, and no dual feasible point has a larger dual
objective. -/
def DualOptimal (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) : Prop :=
  D.DualFeasible μ μn ν ∧
    ∀ μ' μn' ν', D.DualFeasible μ' μn' ν' → D.dualObjective μ' μn' ν' ≤ D.dualObjective μ μn ν

/-- The reduced cost of route `r`, the left side of (33):
`c_r − ∑_{i} α_{i,r} νᵢ − ∑_{n′} β_{n′,r} μ_{n′} − μₙ`. -/
def reducedCost (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (r : R) : ℝ :=
  D.c r - ∑ i, D.α i r * ν i - ∑ p, D.β p r * μ p - μn

/-- `r′ ∈ ℛⁿ_r` (Appendix G, p. 42): route `r′` covers locations only in
`ℐⁿ_r = {i | α_{i,r} = 0}`, i.e. `α_{i,r′} ≠ 0` implies `α_{i,r} = 0`. -/
def InRr (r r' : R) : Prop := ∀ i, D.α i r' ≠ 0 → D.α i r = 0

/-- Feasibility for the restricted problem **SF1_r** (Appendix G, p. 42): binary `θ′` supported on
`ℛⁿ_r`, with the right-hand sides reduced by `r`'s own use as in (76)–(77),
`∑_{r′} β_{n′,r′} θ′_{r′} ≤ b_{n′} − β_{n′,r}`, `∑_{r′} θ′_{r′} ≤ K̄ − ζⁿₙ − 1`, and
`∑_{r′} α_{i,r′} θ′_{r′} = 1` for `i ∈ ℐⁿ_r`. -/
def SF1rFeasible (r : R) (θ' : R → ℝ) : Prop :=
  (∀ r', ¬ D.InRr r r' → θ' r' = 0) ∧
  (∀ p, ∑ r', D.β p r' * θ' r' ≤ D.b p - D.β p r) ∧
  (∑ r', θ' r' ≤ (D.Kbar : ℝ) - D.ζn - 1) ∧
  (∀ i, D.α i r = 0 → ∑ r', D.α i r' * θ' r' = 1) ∧
  (∀ r', θ' r' = 0 ∨ θ' r' = 1)

/-- Feasibility for the LP **RF1_r** (75)–(79): the constraints of **SF1_r** with `θ′ ≥ 0` real
instead of binary. -/
def RF1rFeasible (r : R) (θ' : R → ℝ) : Prop :=
  (∀ r', ¬ D.InRr r r' → θ' r' = 0) ∧
  (∀ p, ∑ r', D.β p r' * θ' r' ≤ D.b p - D.β p r) ∧
  (∑ r', θ' r' ≤ (D.Kbar : ℝ) - D.ζn - 1) ∧
  (∀ i, D.α i r = 0 → ∑ r', D.α i r' * θ' r' = 1) ∧
  (∀ r', 0 ≤ θ' r')

/-- `φ(SF1_r)`, the optimal cost of **SF1_r**, in `EReal`: the infimum of the cost over the feasible
set, `⊤` when **SF1_r** is infeasible. -/
noncomputable def phiSF1r (r : R) : EReal :=
  sInf ((fun θ' => ((D.cost θ' : ℝ) : EReal)) '' {θ' | D.SF1rFeasible r θ'})

/-- Dual feasibility for **RF1_r** with dual variables `μ_{n′}` of (76), `μₙ` of (77) and `νᵢ`
(`i ∈ ℐⁿ_r`) of (78): `μ ≤ 0`, `μₙ ≤ 0`, `ν` free (equality rows), and for every `r′ ∈ ℛⁿ_r`
`∑_{i ∈ ℐⁿ_r} α_{i,r′} νᵢ + ∑_{n′} β_{n′,r′} μ_{n′} + μₙ ≤ c_{r′}`. The values `νᵢ` for `i ∉ ℐⁿ_r`
play no role. -/
def RF1rDualFeasible (r : R) (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) : Prop :=
  (∀ p, μ p ≤ 0) ∧ μn ≤ 0 ∧
  ∀ r', D.InRr r r' →
    ∑ i ∈ univ.filter (fun i => D.α i r = 0), D.α i r' * ν i + ∑ p, D.β p r' * μ p + μn ≤ D.c r'

/-- The dual objective of **RF1_r** at `(μ, μₙ, (νᵢ)_{i ∈ ℐⁿ_r})`, written as on p. 42:
`∑_{n′} ∑_{k=0}^{K̄} μ_{n′} k z̄^{n′}_k − ∑_{n′} β_{n′,r} μ_{n′} + μₙ (K̄ − ζⁿₙ − 1) + ∑_{i ∈ ℐⁿ_r} νᵢ`. -/
noncomputable def rf1rBound (r : R) (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) : ℝ :=
  ∑ p, μ p * D.b p - ∑ p, D.β p r * μ p + μn * ((D.Kbar : ℝ) - D.ζn - 1) +
    ∑ i ∈ univ.filter (fun i => D.α i r = 0), ν i

end Data

end OnDemandDelivery.RouteElim


