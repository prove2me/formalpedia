-- Prove2me | Definitions.Def_WagerFairDiv_Model
-- name    : WagerFairDiv_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:30.966677+00:00
-- url     : https://prove2.me/theorems/5926d878-62d3-44e2-a1b6-c8fd1d169e93
-- title:
--   Fair division and wagering: report profiles, positive weights / wagers, mechanisms, feasible allocations
-- statement:
--   This file fixes the common model of §2 of Freeman, Pennock and Vaughan.
--
--   **Agents, goods, outcomes** (§2.1, p.2; §2.2, p.3). There are $n$ agents and $m$ divisible goods; on the wagering side the agents are bettors and the goods are the $m$ possible values of a random variable $X$.
--
--   **Profiles.** Each agent $i$ has values $\mathbf v_i=(v_{i,1},\dots,v_{i,m})$ with $v_{i,j}\ge0$ and $\sum_{j=1}^m v_{i,j}=1$ (fair division), or beliefs $\mathbf p_i$ with $p_{i,j}$ the probability of $X=j$ (wagering). Both are points of the probability simplex
--   $$\Delta_m=\Big\{x\in\mathbb R^m:\ x_j\ge0\ \forall j,\ \textstyle\sum_{j=1}^m x_j=1\Big\}.$$
--   A **profile** is a vector $(\hat{\mathbf v}_1,\dots,\hat{\mathbf v}_n)\in\Delta_m^n$ of reports.
--
--   **Weights and wagers.** Each agent has a weight $e_i>0$ (entitlement) or a wager $w_i>0$; write $E=\sum_i e_i$ and $W=\sum_i w_i$.
--
--   **Values of bundles.** Agent $i$'s value for a bundle $\mathbf z\in\mathbb R^m$ is $v_i(\mathbf z)=\sum_{j=1}^m v_{i,j}z_j$; the same formula $\sum_j p_{i,j}b_{i,j}$ is a bettor's expected number of paying securities.
--
--   **Mechanisms.** A mechanism maps a profile and a positive weight / wager vector to a number $M_{i,j}$ for every agent $i$ and good $j$. An **allocation** $\mathbf a$ is **feasible** if $a_{i,j}\ge0$ for all $i,j$ and $\sum_{i=1}^n a_{i,j}\le1$ for every $j$ (waste is allowed). An **allocation mechanism** $\mathcal A$ outputs a feasible allocation on every input; $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)$ is the fraction of good $j$ given to agent $i$. A **wagering mechanism** $\mathcal B$, in the security interpretation of p.3, gives agent $i$ the number $\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=b_{i,j}=w_i+\Pi_i(\hat{\mathbf p},\mathbf w,j)\ge0$ of type-$j$ securities (each pays \$1 if $X=j$); validity is $b_{i,j}\ge0$, i.e. no bettor loses more than her wager.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Agents are `Fin n` and goods / outcomes `Fin m`, 0-based. Profiles are `Fin n → stdSimplex ℝ (Fin m)` (Mathlib's standard simplex). Weights and wagers are the subtype `PosVec n` of strictly positive vectors and `PosVec.total` is $E$ or $W$. Allocation and wagering mechanisms share the type `Mech n m`; the predicates `IsAllocMech` and `IsWagerMech` single out the valid ones.
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), §2.1 Fair Division, p.2 (agents, divisible goods, normalized values vᵢ,ⱼ ≥ 0, Σⱼ vᵢ,ⱼ = 1, vᵢ(z), weights eᵢ > 0, E, feasible allocation, allocation mechanism); §2.2 Wagering, p.3 (outcomes of X, beliefs pᵢ, wagers wᵢ > 0, W, validity Πᵢ ≥ −wᵢ, security form bᵢ,ⱼ = wᵢ + Πᵢ(p̂, w, j) ≥ 0, Bᵢ,ⱼ(p̂, w)). PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib

namespace WagerFairDiv

/-- A **profile** of reported (or true) values / beliefs: one point of the probability simplex
over the `m` goods (= outcomes) for each of the `n` agents (= bettors).

Freeman, Pennock & Vaughan, *An Equivalence Between Wagering and Fair-Division Mechanisms*
(preprint, 2018), §2.1, p.2 ("values vᵢ,ⱼ ≥ 0 … normalized so that Σⱼ vᵢ,ⱼ = 1") and §2.2, p.3
(beliefs pᵢ, pᵢ,ⱼ the probability i assigns to X = j).

**Formalization Note.** Agents are `Fin n` and goods/outcomes are `Fin m`, 0-based (the paper's
agent 1 is `0`). Reports range over the same set as true values and beliefs: Mathlib's
`stdSimplex ℝ (Fin m)` (nonnegative entries summing to 1). -/
abbrev Profile (n m : ℕ) : Type := Fin n → stdSimplex ℝ (Fin m)

/-- A vector of **weights** `e` (fair division, §2.1, p.2: "a fixed weight eᵢ > 0") or
**wagers** `w` (wagering, §2.2, p.3: "a budget or wager wᵢ > 0"): a strictly positive vector
indexed by the agents. -/
abbrev PosVec (n : ℕ) : Type := {w : Fin n → ℝ // ∀ i, 0 < w i}

/-- The total weight `E = Σᵢ eᵢ` (§2.1, p.2) or total wager `W = Σᵢ wᵢ` (§2.2, p.3). -/
def PosVec.total {n : ℕ} (w : PosVec n) : ℝ := ∑ i, w.1 i

/-- A **mechanism**: on every profile of reports and every positive weight / wager vector it
outputs a real number for every agent `i` and good / outcome `j`.

An allocation mechanism `A` (§2.1, p.2) outputs `Aᵢ,ⱼ(v̂, e)`, the fraction of good `j` given to
agent `i`; a wagering mechanism `B` in security form (§2.2, p.3) outputs `Bᵢ,ⱼ(p̂, w)`, the number
of type-`j` securities given to agent `i`. Both share this type; `IsAllocMech` and
`IsWagerMech` say which outputs are admissible.

**Formalization Note.** Mechanisms are total functions on (profile, positive vector). -/
abbrev Mech (n m : ℕ) : Type := Profile n m → PosVec n → Fin n → Fin m → ℝ

/-- The additive value `vᵢ(z) = Σⱼ vᵢ,ⱼ zⱼ` of a bundle `z` for an agent with values `x`
(§2.1, p.2); the same expression `Σⱼ pᵢ,ⱼ bᵢ,ⱼ` is the expected number of paying securities of a
bettor with beliefs `x` (§2.2, p.3; Definitions 5, 7, 8). -/
def val {m : ℕ} (x z : Fin m → ℝ) : ℝ := ∑ j, x j * z j

/-- A **feasible allocation** (§2.1, p.2): `aᵢ,ⱼ ≥ 0` for all `i, j`, and `Σᵢ aᵢ,ⱼ ≤ 1` for all
`j`. Goods may be allocated incompletely (waste is allowed). -/
def IsFeasibleAlloc {n m : ℕ} (a : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ a i j) ∧ ∀ j, ∑ i, a i j ≤ 1

/-- A (valid) **allocation mechanism** (§2.1, p.2): on every input `(v̂, e)` it "outputs a
feasible allocation". -/
def IsAllocMech {n m : ℕ} (A : Mech n m) : Prop :=
  ∀ (v : Profile n m) (e : PosVec n), IsFeasibleAlloc (A v e)

/-- A (valid) **wagering mechanism** in security form (§2.2, p.3): every agent receives a
nonnegative number of securities of each type, `bᵢ,ⱼ = wᵢ + Πᵢ(p̂, w, j) ≥ 0`, which is the
validity requirement that no agent loses more than her wager. -/
def IsWagerMech {n m : ℕ} (B : Mech n m) : Prop :=
  ∀ (p : Profile n m) (w : PosVec n) (i : Fin n) (j : Fin m), 0 ≤ B p w i j

end WagerFairDiv


