-- Prove2me | Definitions.Def_StructBandit_IsStructureSet
-- name    : StructBandit_IsStructureSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:56.723467+00:00
-- url     : https://prove2.me/theorems/9c5f01c7-5c98-4eff-9467-c0d01a8114ca
-- title:
--   The structured bandit model: $P_\Omega$, means, optimal arms, gaps, $\mathrm{int}(\mathcal P)$
-- statement:
--   A **structured bandit** has a finite nonempty set of arms $X$ and a finite set $\mathfrak R\subset[0,\infty)$ of possible rewards. A reward distribution is a table $Q=(Q(r,x))_{r\in\mathfrak R,x\in X}$, and
--
--   $$
--   \mathcal P_\Omega:=\Big\{Q\in\mathbb R_+^{|\mathfrak R|\times|X|}:\ \sum_{r\in\mathfrak R}Q(r,x)=1\ \ \forall x\in X\Big\}.
--   $$
--
--   The expected reward of arm $x$ is $\sum_r rQ(r,x)$, the optimal arms are $x^\star(Q)=\arg\max_x\sum_r rQ(r,x)$ (a set), $\mathrm{Rew}^\star(Q)=\max_x\sum_r rQ(r,x)$, the suboptimal arms are $\tilde X(Q)=X\setminus x^\star(Q)$ and the gaps are $\Delta(x,Q)=\mathrm{Rew}^\star(Q)-\sum_r rQ(r,x)$.
--
--   The structural information is a set $\mathcal P\subseteq\mathcal P_\Omega$ that is **closed, convex and has non-empty interior**. The interior $\mathrm{int}(\mathcal P)$ is taken in the topology of the affine hull $\{Q:\sum_rQ(r,x)=1\ \forall x\}$ of $\mathcal P_\Omega$: $Q\in\mathrm{int}(\mathcal P)$ iff some sup-norm ball around $Q$, intersected with the affine hull, lies in $\mathcal P$.
--
--   These are the objects on which every statement of the mission is built.
--
--   **Formalization Note** The reward set is a `Finset ℝ` used as a type, so a distribution is a function `R → X → ℝ`. The paper's $\mathcal P$ is written `S` in Lean. `IsStructureSet S` bundles nonnegative rewards, $S\subseteq\mathcal P_\Omega$, closedness, convexity and a nonempty interior (`relInt`).
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, §3, p.7, Eq. (1); p.8 (x⋆, Rew⋆, X̃, ∆); App. B, p.40 (topology)

import Mathlib

open scoped BigOperators

namespace StructBandit

open Classical in
/-- **The reward distributions `P_Ω`, the mean reward, the optimal and suboptimal arms, the gaps,
the interior of a structure set, and the structured-bandit model.**
Van Parys & Golrezaei, *Optimal Learning for Structured Bandits*, arXiv:2007.07302v3, §3, p.7 (model,
Eq. (1)), p.8 (`x⋆(P)`, `Rew⋆(P)`, `X̃(P)`, `∆(x,P)`), App. B, p.40 (topology relative to the affine hull).

The arms form a finite nonempty type `X`; the rewards form a finite set `R` of nonnegative reals
(footnote 4, p.7). A reward distribution is a table `Q : R → X → ℝ` (`Q ∈ ℝ^{|R|×|X|}`), and
`P_Ω := {Q ≥ 0 : ∑_{r∈R} Q(r,x) = 1 ∀x ∈ X}` (1).

**Formalization Note.** The reward set is a `Finset ℝ`, used as a type through its coercion, so a
distribution is a function on `R × X` and `P_Ω` lives in the finite-dimensional space `R → X → ℝ`
with its product (sup-norm) topology. -/
def POmega (R : Finset ℝ) (X : Type*) [Fintype X] : Set (R → X → ℝ) :=
  {Q | (∀ r x, 0 ≤ Q r x) ∧ ∀ x, ∑ r, Q r x = 1}

/-- The expected reward `∑_{r∈R} r Q(r,x)` of arm `x` under `Q` (arXiv:2007.07302v3, p.7). -/
def mean {R : Finset ℝ} {X : Type*} (Q : R → X → ℝ) (x : X) : ℝ :=
  ∑ r : R, (r : ℝ) * Q r x

/-- The optimal per-round expected reward `Rew⋆(Q) := max_{x∈X} ∑_{r∈R} r Q(r,x)` (p.8). -/
noncomputable def rewStar {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (Q : R → X → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (mean Q)

open Classical in
/-- The **set** of optimal arms `x⋆(Q) = argmax_{x∈X} ∑_{r∈R} r Q(r,x)` (p.8). It is a set: ties are
kept, never broken. -/
noncomputable def optArms {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (Q : R → X → ℝ) :
    Finset X :=
  Finset.univ.filter (fun x => mean Q x = rewStar Q)

open Classical in
/-- The suboptimal arms `X̃(Q) := X ∖ x⋆(Q)` (p.8). -/
noncomputable def subArms {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (Q : R → X → ℝ) :
    Finset X :=
  Finset.univ.filter (fun x => mean Q x < rewStar Q)

/-- The suboptimality gap `∆(x,Q) := Rew⋆(Q) − ∑_{r∈R} r Q(r,x)` (p.8). -/
noncomputable def gap {R : Finset ℝ} {X : Type*} [Fintype X] [Nonempty X] (Q : R → X → ℝ) (x : X) :
    ℝ :=
  rewStar Q - mean Q x

/-- The **interior** `int(S)` (the paper's `int(𝒫)`) of a set of reward distributions, in the topology of App. B (p.40):
the topology relative to the affine hull `{Q : ∑_r Q(r,x) = 1 ∀x}` of `P_Ω`, with the sup-norm balls as
a base. `Q ∈ int(S)` iff `Q ∈ S` and, for some `κ > 0`, every `Q′` with unit column sums and
`max_{r,x} |Q′(r,x) − Q(r,x)| < κ` lies in `S`.

**Formalization Note.** This is not the interior of `S` as a subspace of `P_Ω` (that would admit
boundary points of `P_Ω`): the ball is taken in the affine hull, so an interior point of `S ⊆ P_Ω` is
strictly positive as soon as `|R| ≥ 2`. -/
def relInt {R : Finset ℝ} {X : Type*} [Fintype X] (S : Set (R → X → ℝ)) : Set (R → X → ℝ) :=
  {Q | Q ∈ S ∧ ∃ κ > (0 : ℝ), ∀ Q' : R → X → ℝ, (∀ x, ∑ r, Q' r x = 1) →
    (∀ r x, |Q' r x - Q r x| < κ) → Q' ∈ S}

/-- **The structured bandit model** (arXiv:2007.07302v3, §3, p.7): the rewards in `R` are nonnegative
("a nonnegative random reward `R_t(x) = r ∈ R`"), and the structure set `S` (the paper's `𝒫`) is a closed convex subset
of `P_Ω` with non-empty interior (interior in the sense of App. B, p.40, see `relInt`). -/
structure IsStructureSet {R : Finset ℝ} {X : Type*} [Fintype X] (S : Set (R → X → ℝ)) : Prop where
  /-- Rewards are nonnegative reals (p.7). -/
  rewards_nonneg : ∀ r : R, 0 ≤ (r : ℝ)
  /-- `S ⊆ P_Ω`. -/
  subset : S ⊆ POmega R X
  /-- `S` is closed. -/
  closed : IsClosed S
  /-- `S` is convex. -/
  convex : Convex ℝ S
  /-- `S` has non-empty interior (relative to the affine hull of `P_Ω`). -/
  interior_nonempty : (relInt S).Nonempty

end StructBandit


