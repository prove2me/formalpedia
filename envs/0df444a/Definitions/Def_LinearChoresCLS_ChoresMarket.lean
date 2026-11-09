-- Prove2me | Definitions.Def_LinearChoresCLS_ChoresMarket
-- name    : LinearChoresCLS_ChoresMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:26.081806+00:00
-- url     : https://prove2.me/theorems/aa0a1f87-a8a4-4fbd-928b-b8bc2b048ab5
-- title:
--   Linear Fisher market with chores and its competitive equilibria (Definitions 2.1, 2.2, Eq. (2.2))
-- statement:
--   A **linear Fisher market with chores** $F=(N,M,\{d_{aj}\},\{B_a\},\{S_j\})$ consists of a finite set $N$ of agents, a finite set $M$ of divisible chores, a disutility $d_{aj}$ incurred by agent $a$ per unit of chore $j$, an earning requirement $B_a$ for each agent and a supply $S_j$ for each chore. The market is **valid** when all $d_{aj}$, $B_a$ and $S_j$ are strictly positive.
--
--   Given payments (prices) $p\in\mathbb R^M_{\ge 0}$, agent $a$'s **demand set** is
--   $$
--   X_a(p)=\operatorname*{arg\,min}_{z_a\in\mathbb R^M_{\ge0}}\Big\{\sum_j d_{aj}z_{aj} : \sum_j p_j z_{aj}\ge B_a\Big\}.
--   $$
--   A pair $(p,z)\in\mathbb R^M_{\ge0}\times\mathbb R^{N\times M}_{\ge0}$ is a **competitive equilibrium** if every agent receives a bundle $z_a\in X_a(p)$ (individual optimality) and every chore is fully allocated, $\sum_a z_{aj}=S_j$ (market clearing). The **normalized price domain** is
--   $$
--   \mathcal P=\Big\{p\in\mathbb R^M_{>0} : \sum_j S_jp_j=\sum_a B_a\Big\}.
--   $$
--
--   These are the objects of the paper's main theorem: an instance of the search problem is a valid market, an answer is a competitive equilibrium.
--
--   **Formalization Note** The data are real numbers; positivity is the separate predicate `Valid`. The demand set is written out as an argmin set (feasibility plus optimality against every feasible bundle), exactly as Definition 2.1, rather than through the derived ratio condition, which divides by prices that may vanish.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Definition 2.1, Definition 2.2 and Eq. (2.2), pp.5–6

import Mathlib

open Finset

namespace LinearChoresCLS

/-- **Fisher market with chores** `F = (N, M, {d_{aj}}, {B_a}, {S_j})` (Liu–Ma–Tao–Yang–Zheng,
*Competitive Equilibrium for Linear Chores is CLS-complete*, arXiv:2611.06589, held version
sha256 85d34a9e…, Definition 2.1, p.6): a finite set `N` of agents and a finite set `M` of divisible
chores, a linear disutility coefficient `d_{aj}` for agent `a` performing one unit of chore `j`, an
earning requirement `B_a` for each agent and a supply `S_j` for each chore.

**Formalization Note.** The data are real numbers. The positivity the paper requires
(`d_{aj} > 0`, `B_a > 0`, `S_j > 0`, p.5) is the separate predicate `ChoresMarket.Valid`. -/
structure ChoresMarket (N M : Type*) where
  /-- disutility `d_{aj}` of agent `a` per unit of chore `j` -/
  disutil : N → M → ℝ
  /-- earning requirement `B_a` -/
  earn : N → ℝ
  /-- supply `S_j` -/
  supply : M → ℝ

namespace ChoresMarket

variable {N M : Type*} [Fintype N] [Fintype M]

/-- Validity of a chores market (arXiv:2611.06589, §2, p.5, and Definition 2.1, p.6): every
disutility coefficient, earning requirement and supply is strictly positive. -/
def Valid (F : ChoresMarket N M) : Prop :=
  (∀ a j, 0 < F.disutil a j) ∧ (∀ a, 0 < F.earn a) ∧ ∀ j, 0 < F.supply j

/-- **Demand correspondence** `X_a(p) := argmin_{z_a ∈ ℝ^m_{≥0}} {d_a(z_a) : ⟨p, z_a⟩ ≥ B_a}`
(arXiv:2611.06589, Definition 2.1, p.6): the nonnegative bundles that meet agent `a`'s earning
requirement at prices `p` and minimize her linear disutility `∑_j d_{aj} z_{aj}` among all such
bundles.

**Formalization Note.** The argmin is written out as a set: feasibility plus optimality against
every feasible bundle. It is empty when no feasible bundle attains the infimum. -/
def demandSet (F : ChoresMarket N M) (p : M → ℝ) (a : N) : Set (M → ℝ) :=
  {y | (∀ j, 0 ≤ y j) ∧ F.earn a ≤ ∑ j, p j * y j ∧
    ∀ y' : M → ℝ, (∀ j, 0 ≤ y' j) → F.earn a ≤ ∑ j, p j * y' j →
      ∑ j, F.disutil a j * y j ≤ ∑ j, F.disutil a j * y' j}

/-- **Competitive equilibrium** (arXiv:2611.06589, Definition 2.2, p.6): a price–allocation pair
`(p, z) ∈ ℝ^m_{≥0} × ℝ^{n×m}_{≥0}` such that (1) every agent's bundle lies in her demand set
`X_a(p)` (individual optimality) and (2) every chore is fully allocated, `∑_a z_{aj} = S_j`
(market clearing).

**Formalization Note.** Definition 2.2 is used literally (the argmin demand set), not the derived
ratio form `d_{aj}/p_j = min_k d_{ak}/p_k`, which divides by prices that may be `0`. -/
def IsCE (F : ChoresMarket N M) (p : M → ℝ) (z : N → M → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ (∀ a j, 0 ≤ z a j) ∧ (∀ a, z a ∈ F.demandSet p a) ∧
    ∀ j, ∑ a, z a j = F.supply j

/-- **Normalized price domain** `P := {p ∈ ℝ^m_{>0} : ∑_j S_j p_j = ∑_a B_a}`
(arXiv:2611.06589, Eq. (2.2), p.6): strictly positive prices satisfying payment balance (2.1). -/
def priceDomain (F : ChoresMarket N M) : Set (M → ℝ) :=
  {p | (∀ j, 0 < p j) ∧ ∑ j, F.supply j * p j = ∑ a, F.earn a}

end ChoresMarket

end LinearChoresCLS


