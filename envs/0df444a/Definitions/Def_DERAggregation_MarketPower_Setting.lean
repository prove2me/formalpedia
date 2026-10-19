-- Prove2me | Definitions.Def_DERAggregation_MarketPower_Setting
-- name    : DERAggregation_MarketPower_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T11:24:21.64149+00:00
-- url     : https://prove2.me/theorems/2fdbe2a4-82de-435c-aeb7-e311632ed970
-- title:
--   §5 — one-node market with quadratic prosumer utilities and N linear-cost generators: Assumption 5, the dispatch problems (49), (69), market clearing and the strategic outcomes
-- statement:
--   The single-node market of §5 of Gao, Alshehri and Birge.
--
--   **Data.** There are finitely many prosumers $i$ and $N\ge1$ identical generators $j=1,\dots,N$. Prosumer $i$ owns a DER capacity $C_i\ge0$ and has the quadratic utility of consumption
--   $$u_i(z)=a_iz^2+b_iz .$$
--   Every generator has the true linear cost $c_j(y_j)=\alpha y_j$. Write $C=\sum_iC_i$.
--
--   **Assumption 5** (p. 26) is the conjunction of: $a_i<0$ for all $i$; $\alpha>0$; $C_i\ge0$; $N\ge1$; at least one prosumer has $2a_iC_i+b_i>\alpha$; and the two informal clauses read as
--   1. (H1) for every $i$, $\dfrac{C+\sum_l b_l/(2a_l)}{\sum_l 1/(2a_l)}<b_i$ (the participation clearing price at zero generator supply lies below every $b_i$);
--   2. (H2) $-C+\sum_i(\alpha-b_i)/(2a_i)>0$ (the optimal total supply is positive).
--
--   **Truthful dispatch.** With prosumer participation, the system operator solves (49):
--   $$\mathcal W^T=\max_{z_i>-C_i,\ y_j\ge0}\ \sum_iu_i(C_i+z_i)-\sum_j\alpha y_j\quad\text{s.t.}\quad\sum_jy_j=\sum_iz_i ,$$
--   where $z_i$ is the net purchase of prosumer $i$. Without participation it solves (69), the same problem with purchases $d_i\ge0$ in place of $z_i>-C_i$; its value is $\mathcal W^{TN}$. Both values are defined as suprema of the welfare over the feasible set.
--
--   **Price-taking prosumers and market clearing.** At a market price $\lambda$, a participating prosumer's optimal response maximizes $u_i(C_i+z)-\lambda z$ over $z>-C_i$ ((47)); a non-participating prosumer's maximizes $u_i(C_i+d)-\lambda d$ over $d\ge0$ ((66)). A pair $(\lambda,z)$ clears the market at total generator supply $y$ if every $z_i$ is an optimal response at $\lambda$ and $\sum_iz_i=y$ ((52), (57); likewise (67), (76) without participation).
--
--   **Strategic outcome.** A strategic outcome is a symmetric pure equilibrium of the generators' quantity game (56) (resp. (75)): each generator supplies $q\ge0$, $(\lambda,z)$ clears the market at total $Nq$, and for every $q'\ge0$ and every price $\lambda'$ clearing the market at total $q'+(N-1)q$, a single deviating generator's profit $\lambda'q'-\alpha q'$ does not exceed $\lambda q-\alpha q$. The welfares $\mathcal W^S$ and $\mathcal W^{SN}$ are the **true** welfare $\sum_iu_i(C_i+z_i)-N\alpha q$ at such an outcome.
--
--   Finally $\mathcal W_0=\sum_iu_i(C_i)$ (87) and $z^T_i=-C_i+(\alpha-b_i)/(2a_i)$ is the expression of (50).
--
--   **Formalization Note** H1 and H2 are the precise readings of Assumption 5's informal clauses "$b_i\gg|a_i|$. So, the market price always falls into the range $(0,b_i)$" and "the optimal total supply always satisfies $y>0$"; the lower end $0$ of the range is not used. The paper's §5.4 example ($a_i=-0.1$, $b_i=10$, $C=(10,30)$, $\alpha=5$) satisfies all of Assumption 5 as encoded. $C_i\ge0$ is the paper's standing convention for capacities. The paper models strategic generators as bidding a tilted cost function $\tilde c_j$ that implements the quantity of (56)/(75) (Lemmas 5 and 8); that bid layer is not modelled, and the strategic outcome is defined directly as the quantity equilibrium against market clearing, which is the outcome at which the paper evaluates $\mathcal W^S$ and $\mathcal W^{SN}$. Generators are indexed by `Fin N`; the welfare suprema use `sSup`, and Propositions 5 and 7 state that they are attained.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), pp. 26–34, §5 (Assumption 5), §5.1 ((47), (49), (52), (56), (57)), §5.2 ((66), (67), (69), (75), (76)), §5.3 ((87))

import Mathlib

namespace DERAggregation.MarketPower

open Finset

/-! # §5 of Gao, Alshehri, Birge (SSRN 3931052, pp. 26–32): one node, `n` prosumers, `N` generators

Prosumers are indexed by a finite type `ι`; prosumer `i` has DER capacity `C i` and quadratic
utility of consumption `u_i(z) = a_i z² + b_i z`. The `N` generators (indexed by `Fin N`) all have
the true linear cost `c_j(y_j) = α y_j`. -/

/-- The quadratic utility of consumption of Assumption 5 (p. 26): `u_i(z) = a_i z² + b_i z`. -/
def u {ι : Type*} (a b : ι → ℝ) (i : ι) (z : ℝ) : ℝ := a i * z ^ 2 + b i * z

/-- Assumption 5 (p. 26), with its informal clauses made precise:
* `a_i < 0` for every prosumer, `α > 0`, capacities `C_i ≥ 0`, and at least one generator (`N ≥ 1`);
* (H1) "`b_i ≫ |a_i|`, so the market price always falls into `(0, b_i)`": the participation
  market-clearing price at zero generator supply, `(C + Σ_l b_l/(2a_l)) / Σ_l 1/(2a_l)`, is below
  every `b_i` (hence so is the clearing price at every total supply `y ≥ 0`);
* (H2) "the optimal total supply always satisfies `y > 0`": `−C + Σ_i (α − b_i)/(2a_i) > 0`;
* "there exists at least one prosumer `i` such that `2a_iC_i + b_i > α`", as printed. -/
def Assumption5 {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) : Prop :=
  (∀ i, a i < 0) ∧ 0 < α ∧ (∀ i, 0 ≤ C i) ∧ 1 ≤ N ∧
  (∀ i, ((∑ l, C l) + (∑ l, b l / (2 * a l))) / (∑ l, 1 / (2 * a l)) < b i) ∧
  0 < -(∑ i, C i) + (∑ i, (α - b i) / (2 * a i)) ∧
  (∃ i, α < 2 * a i * C i + b i)

/-- Feasible set of the participation dispatch problem (49): net purchases `z_i > −C_i`,
generator outputs `y_j ≥ 0`, and balance `Σ_j y_j = Σ_i z_i`. -/
def FeasT {ι : Type*} [Fintype ι] (C : ι → ℝ) (N : ℕ) (z : ι → ℝ) (y : Fin N → ℝ) : Prop :=
  (∀ i, -C i < z i) ∧ (∀ j, 0 ≤ y j) ∧ ∑ j, y j = ∑ i, z i

/-- Social welfare `Σ_i u_i(C_i + z_i) − Σ_j α y_j` (objective of (49) and of (69)). -/
def welT {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) (z : ι → ℝ) (y : Fin N → ℝ) :
    ℝ :=
  (∑ i, u a b i (C i + z i)) - (∑ j, α * y j)

/-- `W^T`, the optimal social welfare of (49) (prosumer participation, truthful generators),
as the supremum of the welfare over the feasible set. -/
noncomputable def WT {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup {w | ∃ (z : ι → ℝ) (y : Fin N → ℝ), FeasT C N z y ∧ w = welT a b C α N z y}

/-- Feasible set of the no-participation dispatch problem (69): purchases `d_i ≥ 0`,
generator outputs `y_j ≥ 0`, and balance `Σ_j y_j = Σ_i d_i`. -/
def FeasTN {ι : Type*} [Fintype ι] (N : ℕ) (d : ι → ℝ) (y : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ d i) ∧ (∀ j, 0 ≤ y j) ∧ ∑ j, y j = ∑ i, d i

/-- `W^{TN}`, the optimal social welfare of (69) (no prosumer participation, truthful
generators), as the supremum of the welfare over the feasible set. -/
noncomputable def WTN {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup {w | ∃ (d : ι → ℝ) (y : Fin N → ℝ), FeasTN N d y ∧ w = welT a b C α N d y}

/-- Prosumer `i`'s optimal response with participation at market price `λ` ((47), (52)):
`z` maximizes `u_i(C_i + z') − λ z'` over `z' > −C_i`. -/
def IsRespP {ι : Type*} (a b C : ι → ℝ) (lam : ℝ) (i : ι) (z : ℝ) : Prop :=
  -C i < z ∧ ∀ z', -C i < z' → u a b i (C i + z') - lam * z' ≤ u a b i (C i + z) - lam * z

/-- Prosumer `i`'s optimal response without participation at market price `λ` ((66), (67)):
`d` maximizes `u_i(C_i + d') − λ d'` over `d' ≥ 0`. -/
def IsRespN {ι : Type*} (a b C : ι → ℝ) (lam : ℝ) (i : ι) (d : ℝ) : Prop :=
  0 ≤ d ∧ ∀ d', 0 ≤ d' → u a b i (C i + d') - lam * d' ≤ u a b i (C i + d) - lam * d

/-- Market clearing with participation at total generator supply `y` ((52), (57)): every
prosumer's net purchase `z_i` is an optimal response at the price `λ`, and `Σ_i z_i = y`. -/
def ClearsP {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (y lam : ℝ) (z : ι → ℝ) : Prop :=
  (∀ i, IsRespP a b C lam i (z i)) ∧ ∑ i, z i = y

/-- Market clearing without participation at total generator supply `y` ((67), (76)): every
prosumer's purchase `d_i` is an optimal response at the price `λ`, and `Σ_i d_i = y`. -/
def ClearsN {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (y lam : ℝ) (d : ι → ℝ) : Prop :=
  (∀ i, IsRespN a b C lam i (d i)) ∧ ∑ i, d i = y

/-- Strategic outcome with participation (§5.1.2, (56)–(57)): a symmetric pure equilibrium of
the generators' quantity game. Every generator supplies `q ≥ 0`; `(λ, z)` clears the market at the
total `N q`; and no single generator gains by deviating to any `q' ≥ 0` while the other `N − 1`
keep `q`, where its profit is `λ' q' − α q'` at a price `λ'` clearing the market at the total
`q' + (N − 1) q`. -/
def IsStratP {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) (q lam : ℝ)
    (z : ι → ℝ) : Prop :=
  0 ≤ q ∧ ClearsP a b C ((N : ℝ) * q) lam z ∧
  ∀ (q' lam' : ℝ) (z' : ι → ℝ), 0 ≤ q' → ClearsP a b C (q' + ((N : ℝ) - 1) * q) lam' z' →
    lam' * q' - α * q' ≤ lam * q - α * q

/-- Strategic outcome without participation (§5.2.2, (75)–(76)): the same symmetric pure
equilibrium of the generators' quantity game, against market clearing by purchases `d_i ≥ 0`. -/
def IsStratN {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) (q lam : ℝ)
    (d : ι → ℝ) : Prop :=
  0 ≤ q ∧ ClearsN a b C ((N : ℝ) * q) lam d ∧
  ∀ (q' lam' : ℝ) (d' : ι → ℝ), 0 ≤ q' → ClearsN a b C (q' + ((N : ℝ) - 1) * q) lam' d' →
    lam' * q' - α * q' ≤ lam * q - α * q

/-- `W^S`: the true social welfare `Σ_i u_i(C_i + z_i) − Σ_j α y_j` at a strategic outcome with
participation, where each of the `N` generators supplies `q`. -/
def welS {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) (z : ι → ℝ) (q : ℝ) : ℝ :=
  (∑ i, u a b i (C i + z i)) - (N : ℝ) * (α * q)

/-- `W^{SN}`: the true social welfare `Σ_i u_i(C_i + d_i) − Σ_j α y_j` at a strategic outcome
without participation, where each of the `N` generators supplies `q`. -/
def welSN {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ) (d : ι → ℝ) (q : ℝ) : ℝ :=
  (∑ i, u a b i (C i + d i)) - (N : ℝ) * (α * q)

/-- `W_0 := Σ_i u_i(C_i)` (87), p. 34: the welfare with no generator and no market. -/
def W0 {ι : Type*} [Fintype ι] (a b C : ι → ℝ) : ℝ :=
  ∑ i, u a b i (C i)

/-- The expression `z^T_i = −C_i + (α − b_i)/(2a_i)` of (50) (Proposition 5 shows it is the
optimal net purchase of prosumer `i` in (49)). -/
noncomputable def zT {ι : Type*} (a b C : ι → ℝ) (α : ℝ) (i : ι) : ℝ :=
  -C i + (α - b i) / (2 * a i)

end DERAggregation.MarketPower


