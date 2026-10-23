-- Prove2me | Definitions.Def_DoubleAuctionEff_Repeated_Model
-- name    : DoubleAuctionEff_Repeated_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:23.05398+00:00
-- url     : https://prove2.me/theorems/ba99b449-4017-4a04-b80e-5d7954d5417e
-- title:
--   §3–§6, pp. 7–18 — exchange economy with EReal utilities: Assumptions 1–5; indifference price (1); value CS of (P); supergradient prices (2)–(4); the repeated auction; Pareto efficiency
-- statement:
--   The model of a multi-asset double auction market with price-taking agents.
--
--   Let $I$ be a finite set of agents and $J$ a finite set of assets. Agent $i$ holds a portfolio $x_i\in\mathbb R^J$; an allocation is $x=(x_i)_{i\in I}\in\mathbb R^{I\times J}$. Agent $i$'s preferences are given by an extended-real utility $u_i:\mathbb R^J\to[-\infty,+\infty]$ with effective domain $\operatorname{dom}u_i=\{x_i\mid u_i(x_i)>-\infty\}$, and all prices are quoted in a numeraire portfolio $g\in\mathbb R^J$.
--
--   1. **Concavity** of an extended-real function $f$ means that its hypograph $\{(x,a)\in\mathbb R^J\times\mathbb R\mid a\le f(x)\}$ is convex.
--   2. **Assumption 1** (for agent $i$): $u_i$ is upper semicontinuous, concave, and $u_i(x_i+rg)>u_i(x_i)$ for all $x_i\in\operatorname{dom}u_i$ and $r>0$.
--   3. **Indifference price** (1): for an endowment $x^0_i$,
--   $$D_i(x_i)=\sup\{r\in\mathbb R\mid u_i(x^0_i+x_i-rg)\ge u_i(x^0_i)\},$$
--   a supremum in $[-\infty,+\infty]$.
--   4. **Market value** $CS(x)$: the optimum value of the market clearing problem (P), $\sup\{\sum_{i}D_i(x_i)\mid \sum_i x_i=0\}$, where the $D_i$ are built from the current allocation $x$. The perturbed value $V(z)=\sup\{\sum_iD_i(x_i)\mid\sum_ix_i=z\}$ is the optimum value of $(P_z)$, and **Assumption 2** asks that $V(z)$ be finite for all $\|z\|\le\varepsilon$, for some $\varepsilon>0$.
--   5. **Solutions**: $\bar x$ solves (P) if $\sum_i\bar x_i=0$ and $\sum_iD_i(x_i)\le\sum_iD_i(\bar x_i)$ for every feasible $x$; $(r,w)$ solves (P′) if $\sum_iw_i+rg=\sum_ix^0_i$, $u_i(w_i)\ge u_i(x^0_i)$ for all $i$, and $r$ is maximal among such pairs.
--   6. **Supergradient** (2)/(4): $p\in\partial D(\bar x)$ if $D(\bar x)$ is finite and $D(x)\le D(\bar x)+p\cdot(x-\bar x)$ for all $x$.
--   7. **Repeated auction** (p. 17): $x^0$ is the initial allocation and, for $t\ge1$, the purchases $\bar x^t$ and the price $p^t$ of the $t$-th auction satisfy (2)–(3) for the indifference prices built from $x^{t-1}$, and $x^t_i=x^{t-1}_i+\bar x^t_i-(p^t\cdot\bar x^t_i)g$.
--   8. **Recession directions and Assumption 3** (p. 14): $d$ satisfies $u_i^\infty(d)\ge0$; Assumption 3 says that $u_i^\infty(x_i)\ge0$ for all $i$ and $\sum_ix_i=0$ imply $x=0$.
--   9. **Assumption 4** (p. 15): if $u_i(x_i)>u_i(x'_i)$ for some $x'_i\in\operatorname{dom}u_i$, then $x_i-\varepsilon g\in\operatorname{dom}u_i$ for all small $\varepsilon>0$.
--   10. **Assumption 5** (p. 17): for every $r>0$ there is $\delta_i>0$ with $u_i(x_i+rg)\ge u_i(x_i)+\delta_ir$ for all $x_i\in\mathbb B(r)$.
--   11. **Double auction equilibrium**: $CS(x)=0$. **Individual rationality**: $u_i(\bar x_i)\ge u_i(x^0_i)$ for all $i$. **Pareto efficiency**: $x$ is feasible ($\sum_ix_i=\sum_ix^0_i$) and no feasible $x'$ has $u_i(x'_i)\ge u_i(x_i)$ for all $i$ with strict inequality for some $i$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** Utilities take values in `EReal`; since `EReal` is not a module, concavity is convexity of the real hypograph (Rockafellar's definition) rather than Mathlib's `ConcaveOn`. The supergradient requires $D(\bar x)$ finite (Rockafellar's convention; otherwise $D(\bar x)=+\infty$ would satisfy (4) vacuously). $u_i^\infty(d)\ge0$ is encoded through the characterization the paper quotes from Rockafellar's Theorem 8.6: $u_i(x)\le u_i(x+\alpha d)$ for all $x\in\operatorname{dom}u_i$, $\alpha>0$; for upper semicontinuous concave $u_i$ with nonempty domain and no value $+\infty$ this is $u_i^\infty(d)\ge0$, and for empty domain every $d$ qualifies, which only strengthens Assumption 3. $\mathbb B(r)$ and $|z|$ use the sup norm of $\mathbb R^J$ (the paper fixes no norm; Assumption 2 and the family of conditions in Assumption 5 do not depend on it). In the repeated auction, `x t` is $x^t$ and `y t`, `p t` for $t\ge1$ are $\bar x^t$, $p^t$; `y 0`, `p 0` are unused.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, pp. 7–18, problem (P), (1), (P_z), Assumption 2, (2)–(5), (P′), Assumptions 1, 3, 4, 5, the recursion on p. 17, individual rationality p. 18, Pareto efficiency p. 15

import Mathlib

namespace DoubleAuctionEff.Repeated

open Matrix

/-- The effective domain `dom f = {x | f x > −∞}` of an extended-real function (p. 9). -/
def dom {J : Type*} (f : (J → ℝ) → EReal) : Set (J → ℝ) := {x | ⊥ < f x}

/-- Concavity of an extended-real function (Rockafellar's definition): its hypograph
`{(x, a) | a ∈ ℝ, a ≤ f x}` is a convex subset of `ℝ^J × ℝ`. -/
def IsConcaveE {J : Type*} (f : (J → ℝ) → EReal) : Prop :=
  Convex ℝ {q : (J → ℝ) × ℝ | ((q.2 : ℝ) : EReal) ≤ f q.1}

/-- Assumption 1 (p. 8), for one agent: `u` is upper semicontinuous, concave, and strictly
increasing in the direction of the numeraire `g`: `u (x + r g) > u x` for `x ∈ dom u`, `r > 0`. -/
def Assumption1 {J : Type*} (u : (J → ℝ) → EReal) (g : J → ℝ) : Prop :=
  UpperSemicontinuous u ∧ IsConcaveE u ∧ ∀ x ∈ dom u, ∀ r : ℝ, 0 < r → u x < u (x + r • g)

/-- The indifference price (1), p. 8, of an agent with utility `u` and current endowment `x0`:
`D(y) = sup {r ∈ ℝ | u (x0 + y − r g) ≥ u x0}`, a supremum in `EReal`
(`−∞` if no `r` qualifies, `+∞` if the qualifying `r` are unbounded). -/
noncomputable def indiffPrice {J : Type*} (u : (J → ℝ) → EReal) (g x0 : J → ℝ) (y : J → ℝ) :
    EReal :=
  ⨆ (r : ℝ) (_ : u x0 ≤ u (x0 + y - r • g)), (r : EReal)

/-- `CS(x)`: the optimum value of the market clearing problem (P) (p. 7, notation p. 15), with
the indifference prices built from the current allocation `x`:
`sup {Σ_i D_i(y_i) | Σ_i y_i = 0}`. -/
noncomputable def CS {I J : Type*} [Fintype I] (u : I → (J → ℝ) → EReal) (g : J → ℝ)
    (x : I → J → ℝ) : EReal :=
  ⨆ (y : I → J → ℝ) (_ : ∑ i, y i = 0), ∑ i, indiffPrice (u i) g (x i) (y i)

/-- The optimum value of the perturbed market clearing problem (P_z) (p. 10):
`sup {Σ_i D_i(y_i) | Σ_i y_i = z}`. -/
noncomputable def perturbedValue {I J : Type*} [Fintype I] (u : I → (J → ℝ) → EReal)
    (g : J → ℝ) (x0 : I → J → ℝ) (z : J → ℝ) : EReal :=
  ⨆ (y : I → J → ℝ) (_ : ∑ i, y i = z), ∑ i, indiffPrice (u i) g (x0 i) (y i)

/-- Assumption 2 (p. 11): there is `ε > 0` such that the optimum value of (P_z) is finite for
all `z` with `‖z‖ ≤ ε` (sup norm on `ℝ^J`). -/
def Assumption2 {I J : Type*} [Fintype I] [Fintype J] (u : I → (J → ℝ) → EReal) (g : J → ℝ)
    (x0 : I → J → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ z : J → ℝ, ‖z‖ ≤ ε → ∃ c : ℝ, perturbedValue u g x0 z = (c : EReal)

/-- `xbar` solves (P) (p. 7): it is feasible (`Σ_i xbar_i = 0`) and its objective value
`Σ_i D_i(xbar_i)` is at least that of every feasible `y`. -/
def SolvesP {I J : Type*} [Fintype I] (u : I → (J → ℝ) → EReal) (g : J → ℝ)
    (x0 xbar : I → J → ℝ) : Prop :=
  ∑ i, xbar i = 0 ∧ ∀ y : I → J → ℝ, ∑ i, y i = 0 →
    ∑ i, indiffPrice (u i) g (x0 i) (y i) ≤ ∑ i, indiffPrice (u i) g (x0 i) (xbar i)

/-- Feasibility in problem (P′) of Lemma 9 (p. 13):
`Σ_i w_i + r g = Σ_i x0_i` and `u_i(w_i) ≥ u_i(x0_i)` for all `i`. -/
def FeasibleP' {I J : Type*} [Fintype I] (u : I → (J → ℝ) → EReal) (g : J → ℝ)
    (x0 : I → J → ℝ) (r : ℝ) (w : I → J → ℝ) : Prop :=
  ∑ i, w i + r • g = ∑ i, x0 i ∧ ∀ i, u i (x0 i) ≤ u i (w i)

/-- `(r, w)` solves (P′) (p. 13): it is feasible and `r` is maximal among feasible pairs. -/
def SolvesP' {I J : Type*} [Fintype I] (u : I → (J → ℝ) → EReal) (g : J → ℝ)
    (x0 : I → J → ℝ) (r : ℝ) (w : I → J → ℝ) : Prop :=
  FeasibleP' u g x0 r w ∧ ∀ (r' : ℝ) (w' : I → J → ℝ), FeasibleP' u g x0 r' w' → r' ≤ r

/-- Conditions (2)/(4) (p. 11): `p` is a supergradient of `D` at `xbar`, i.e. `D(xbar)` is finite
(Rockafellar's convention: the superdifferential is empty where `D` is not finite) and
`D z ≤ D xbar + p · (z − xbar)` for all `z`. -/
def IsSupergrad {J : Type*} [Fintype J] (D : (J → ℝ) → EReal) (xbar p : J → ℝ) : Prop :=
  (∃ c : ℝ, D xbar = (c : EReal)) ∧
    ∀ z : J → ℝ, D z ≤ D xbar + (((p ⬝ᵥ (z - xbar) : ℝ)) : EReal)

/-- The repeated double auction (p. 17). `x 0 = x0`; for `t ≥ 0` the `(t+1)`-th auction is run
at the allocation `x t`: its purchases `y (t+1)` and price `p (t+1)` satisfy the market clearing
conditions (2)–(3) for the indifference prices built from `x t`, and
`x (t+1) i = x t i + y (t+1) i − (p (t+1) · y (t+1) i) g`.
So `y t = x̄^t`, `p t = p^t` for `t ≥ 1`; `y 0`, `p 0` are unused. -/
def IsAuctionSeq {I J : Type*} [Fintype I] [Fintype J] (u : I → (J → ℝ) → EReal) (g : J → ℝ)
    (x0 : I → J → ℝ) (x y : ℕ → I → J → ℝ) (p : ℕ → J → ℝ) : Prop :=
  x 0 = x0 ∧ ∀ t : ℕ,
    ∑ i, y (t + 1) i = 0 ∧
    (∀ i, IsSupergrad (indiffPrice (u i) g (x t i)) (y (t + 1) i) (p (t + 1))) ∧
    (∀ i, x (t + 1) i = x t i + y (t + 1) i - (p (t + 1) ⬝ᵥ y (t + 1) i) • g)

/-- `u^∞(d) ≥ 0` (p. 14), encoded through the characterization the paper quotes from
[Rockafellar, Thm 8.6]: `λ ↦ u (x + λ d)` is nondecreasing for every `x ∈ dom u`, i.e.
`u x ≤ u (x + α d)` for all `x ∈ dom u` and `α > 0`. -/
def IsRecessionDir {J : Type*} (u : (J → ℝ) → EReal) (d : J → ℝ) : Prop :=
  ∀ x ∈ dom u, ∀ α : ℝ, 0 < α → u x ≤ u (x + α • d)

/-- Assumption 3 (p. 14): if `u_i^∞(x_i) ≥ 0` for all `i` and `Σ_i x_i = 0`, then `x = 0`. -/
def Assumption3 {I J : Type*} [Fintype I] (u : I → (J → ℝ) → EReal) : Prop :=
  ∀ x : I → J → ℝ, (∀ i, IsRecessionDir (u i) (x i)) → ∑ i, x i = 0 → x = 0

/-- Assumption 4 (p. 15), for one agent: if `u x > u x'` for some `x' ∈ dom u`, then
`x − ε g ∈ dom u` for all small enough `ε > 0`. -/
def Assumption4 {J : Type*} (u : (J → ℝ) → EReal) (g : J → ℝ) : Prop :=
  ∀ x x' : J → ℝ, x' ∈ dom u → u x' < u x →
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), x - ε • g ∈ dom u

/-- The inequality of Assumption 5 at one radius `r` with constant `δ`:
`u (x + r g) ≥ u x + δ r` for all `x ∈ 𝔹(r)` (closed sup-norm ball of radius `r` about `0`). -/
def Assumption5At {J : Type*} [Fintype J] (u : (J → ℝ) → EReal) (g : J → ℝ) (r δ : ℝ) : Prop :=
  ∀ x ∈ Metric.closedBall (0 : J → ℝ) r, u x + ((δ * r : ℝ) : EReal) ≤ u (x + r • g)

/-- Assumption 5 (p. 17), for one agent: for every `r > 0` there is `δ > 0` with
`u (x + r g) ≥ u x + δ r` for all `x ∈ 𝔹(r)`. -/
def Assumption5 {J : Type*} [Fintype J] (u : (J → ℝ) → EReal) (g : J → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ δ : ℝ, 0 < δ ∧ Assumption5At u g r δ

/-- A double auction equilibrium (p. 15): `CS(x) = 0`. -/
def IsDAEquilibrium {I J : Type*} [Fintype I] (u : I → (J → ℝ) → EReal) (g : J → ℝ)
    (x : I → J → ℝ) : Prop :=
  CS u g x = 0

/-- Individual rationality (p. 18): `u_i(xbar_i) ≥ u_i(x0_i)` for all `i`. -/
def IsIndivRational {I J : Type*} (u : I → (J → ℝ) → EReal) (x0 xbar : I → J → ℝ) : Prop :=
  ∀ i, u i (x0 i) ≤ u i (xbar i)

/-- Feasibility of an allocation relative to the endowment `x0` ((5), p. 11):
`Σ_i x_i = Σ_i x0_i`. -/
def IsFeasible {I J : Type*} [Fintype I] (x0 x : I → J → ℝ) : Prop :=
  ∑ i, x i = ∑ i, x0 i

/-- Pareto efficiency (p. 15): `x` is feasible and no feasible `x'` has `u_i(x'_i) ≥ u_i(x_i)`
for all `i` with strict inequality for some `i`. -/
def IsParetoEfficient {I J : Type*} [Fintype I] (u : I → (J → ℝ) → EReal)
    (x0 x : I → J → ℝ) : Prop :=
  IsFeasible x0 x ∧ ¬ ∃ x' : I → J → ℝ, IsFeasible x0 x' ∧
    (∀ i, u i (x i) ≤ u i (x' i)) ∧ ∃ i, u i (x i) < u i (x' i)

end DoubleAuctionEff.Repeated


