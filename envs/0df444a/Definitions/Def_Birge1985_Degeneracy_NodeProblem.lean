-- Prove2me | Definitions.Def_Birge1985_Degeneracy_NodeProblem
-- name    : Birge1985_Degeneracy_NodeProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:31:12.863996+00:00
-- url     : https://prove2.me/theorems/e83ca231-f07e-4614-bb30-ce43e7912d66
-- title:
--   Scenario problem (7) of nested decomposition, its dual, Farkas certificates, and the feasibility and optimality cuts it generates
-- statement:
--   This file sets up the scenario problems of the **Nested Decomposition for Stochastic Programming Algorithm** (NDSPA) of Birge (1985), and the cuts that a descendant problem sends to its ancestor.
--
--   **The scenario problem (7).** Fix a node (period $t$, scenario $j$) of a finite scenario tree, and let $x^{a} \in \mathbb{R}^{n_{\mathrm{in}}}$ be the current decision of its ancestor. After $r$ feasibility cuts and $s$ optimality cuts have been added, the node solves
--
--   $$
--   \begin{aligned}
--   \text{minimize}\quad & c^\top x + \theta && (7.1)\\
--   \text{subject to}\quad & A x = \xi + B x^{a}, && (7.2)\\
--   & D_l^\top x \ge d_l,\quad l = 1,\dots,r, && (7.3)\\
--   & E_l^\top x + \theta \ge e_l,\quad l = 1,\dots,s, && (7.4)\\
--   & x \ge 0, && (7.5)
--   \end{aligned}
--   $$
--
--   over $x \in \mathbb{R}^{n}$ and a **free** scalar $\theta$. Here $A$ is $m \times n$, $B$ is $m \times n_{\mathrm{in}}$, $\xi \in \mathbb{R}^m$ is the scenario's random vector, and $D_l, E_l \in \mathbb{R}^n$, $d_l, e_l \in \mathbb{R}$ are the cut coefficients. Optionally the problem carries the extra restriction $\theta = 0$: NDSPA imposes it during its forward pass (Step 0) and removes it in Step 2, and a last-period node, which has no future cost, is represented with this restriction permanently.
--
--   The constraints are recorded as a finite family of tagged linear constraints on the variable vector $z = (x, \theta) \in \mathbb{R}^{n+1}$: the rows of (7.2) and the restriction $\theta = 0$ are equalities; the rows of (7.3), (7.4) and the sign constraints $x_i \ge 0$ are inequalities. With this family, *basic*, *basic feasible* and *degenerate* solutions of (7) are the general-form notions (a basic solution is degenerate when more than $n + 1$ constraints are active at it).
--
--   **Duals and certificates.** For multipliers $\lambda$ on this family (nonnegative on the inequality rows, free on the equality rows), $\lambda$ is **dual feasible** when $\sum_i \lambda_i a_i$ equals the cost vector $(c, 1)$, where $a_i$ is the constraint vector of row $i$; its **dual objective** is $\sum_i \lambda_i b_i$, with $b_i$ the right-hand side; it is **dual optimal** when it maximizes the dual objective among dual feasible vectors. It is a **Farkas certificate** of infeasibility when $\sum_i \lambda_i a_i = 0$ and $\sum_i \lambda_i b_i > 0$.
--
--   **The cuts.** Write $\pi$ for the multipliers of the rows (7.2). A multiplier vector $\lambda$ of a descendant problem induces, in the ancestor's decision $x$, the affine function $\sum_i \lambda_i b_i(x) = \mathrm{const}(\lambda) - \mathrm{slope}(\lambda)^\top x$ with
--
--   $$
--   \mathrm{slope}(\lambda) = -\pi^\top B, \qquad \mathrm{const}(\lambda) = \pi^\top \xi + \rho^\top d + \sigma^\top e,
--   $$
--
--   where $\rho, \sigma$ are the multipliers of the descendant's own cuts (7.3), (7.4).
--
--   1. A **feasibility cut** $D^\top x \ge d$ of the ancestor is *generated* by a descendant when that descendant is infeasible at some ancestor decision $x^0$, certified by a Farkas certificate $\lambda$ of its constraint family at $x^0$, and $D = \mathrm{slope}(\lambda)$, $d = \mathrm{const}(\lambda)$ (the construction of Van Slyke and Wets that the paper cites).
--   2. The **optimality cut** of NDSPA Step 3a built from descendants $j' \in J'$ with weights $p_{j'}$ and multiplier vectors $\lambda_{j'}$ is $E^\top x + \theta \ge e$ with $E = \sum_{j'} p_{j'}\,\mathrm{slope}(\lambda_{j'})$ and $e = \sum_{j'} p_{j'}\,\mathrm{const}(\lambda_{j'})$.
--   3. An optimality cut $E^\top x + \theta \ge e$ is **valid** when $e - E^\top x \le \sum_{j'} p_{j'} (c_{j'}^\top y_{j'} + \theta_{j'})$ for every ancestor decision $x$ and every choice of feasible points $(y_{j'}, \theta_{j'})$ of the descendant problems at $x$; equivalently, $e - E^\top x$ minorizes the weighted sum of the descendants' optimal values wherever all descendants are feasible.
--
--   These are the objects about which Propositions 3 and 4 of the paper are stated.
--
--   **Formalization Note.** The paper suppresses transposes; here matrix–vector products are explicit, a row vector times a matrix ($\pi B$) is `vecMul`, and the variable vector is `Fin (n+1) → ℝ` with $\theta$ its last coordinate. The paper's Step 3a formula prints $E = -\sum_{d(j)} \pi B_t$ and $e = \sum_{d(j)} \pi\,\xi$; the definition completes it with the terms $\rho^\top d + \sigma^\top e$ from the descendants' own cuts (without which the cut is not a valid lower bound when the descendants carry cuts) and with weights $p_{j'}$ (the probabilities the expectation in (1) requires; $p \equiv 1$ recovers the printed sums). The data $A$, $B$ may differ between scenarios, which is more general than the paper, where they depend only on the period.
-- source:
--   Birge, Decomposition and Partitioning Methods for Multistage Stochastic Linear Programs, Operations Research 33(5), 1985, p. 994, Eqs. (7.1)-(7.5); p. 993 (feasibility cuts, finite-scenario assumption); p. 995, NDSPA Steps 0-3 (Step 3a cut formula, test (9))

import Mathlib
import Definitions.Def_BasicSolution

open Matrix LinearOptimization

namespace Birge1985.Degeneracy

/-- **Birge (1985), p. 994, problem (7).** The data of one scenario problem (7) of nested
decomposition at a node of the scenario tree whose ancestor decision lives in `ℝ^{nIn}`.

* `n` is the dimension `n_t` of the node's own decision `x_t^j`; `m` is the number of
  rows of (7.2); `r` and `s` are the current numbers `r_t^j`, `s_t^j` of feasibility cuts
  (7.3) and optimality cuts (7.4).
* `c` is the cost vector `c_t`, `A` the recourse matrix `A_t`, `B` the technology matrix
  `B_{t−1}` linking the ancestor decision to this node, `ξ` the scenario vector `ξ_t^j`.
* `D l`, `d l` are the coefficients of the `l`-th feasibility cut `D_t^{l,j} x ≥ d_t^{l,j}`;
  `E l`, `e l` those of the `l`-th optimality cut `E_t^{l,j} x + θ ≥ e_t^{l,j}`.
* `thetaFixed = true` means the problem carries the restriction `θ_t^j = 0` (NDSPA Step 0,
  p. 995, removed in Step 2); a last-period node (`z_{T+1} ≡ 0`, p. 992) is modelled with
  `thetaFixed = true` permanently. -/
structure NodeProblem (nIn : ℕ) where
  n : ℕ
  m : ℕ
  r : ℕ
  s : ℕ
  c : Fin n → ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  B : Matrix (Fin m) (Fin nIn) ℝ
  ξ : Fin m → ℝ
  D : Fin r → Fin n → ℝ
  d : Fin r → ℝ
  E : Fin s → Fin n → ℝ
  e : Fin s → ℝ
  thetaFixed : Bool

namespace NodeProblem

variable {nIn : ℕ}

/-- Index set of the constraints of (7): the rows of (7.2), the feasibility cuts (7.3),
the optimality cuts (7.4), the sign constraints (7.5) `x_i ≥ 0`, and (when present) the
restriction `θ = 0`. -/
abbrev Idx (P : NodeProblem nIn) : Type :=
  Fin P.m ⊕ Fin P.r ⊕ Fin P.s ⊕ Fin P.n ⊕ {_u : Unit // P.thetaFixed = true}

/-- The constraints of problem (7) as a finite family of linear constraints on the
variable vector `z = (x, θ) ∈ ℝ^{n+1}` (the last coordinate is the free scalar `θ`), with
ancestor decision `xIn` entering the right-hand side `ξ + B xIn` of (7.2). -/
def constraints (P : NodeProblem nIn) (xIn : Fin nIn → ℝ) :
    P.Idx → LinearConstraint (P.n + 1)
  | .inl k => ⟨Fin.snoc (α := fun _ => ℝ) (P.A k) 0, P.ξ k + (P.B *ᵥ xIn) k, .eq⟩
  | .inr (.inl l) => ⟨Fin.snoc (α := fun _ => ℝ) (P.D l) 0, P.d l, .ge⟩
  | .inr (.inr (.inl l)) => ⟨Fin.snoc (α := fun _ => ℝ) (P.E l) 1, P.e l, .ge⟩
  | .inr (.inr (.inr (.inl i))) => ⟨Pi.single (Fin.castSucc i) 1, 0, .ge⟩
  | .inr (.inr (.inr (.inr _))) => ⟨Pi.single (Fin.last P.n) 1, 0, .eq⟩

/-- The objective (7.1), `c x + θ`, of `z = (x, θ)`. -/
def objective (P : NodeProblem nIn) (z : Fin (P.n + 1) → ℝ) : ℝ :=
  Fin.snoc (α := fun _ => ℝ) P.c 1 ⬝ᵥ z

/-- The feasible set of problem (7) at ancestor decision `xIn`. -/
def feasibleSet (P : NodeProblem nIn) (xIn : Fin nIn → ℝ) : Set (Fin (P.n + 1) → ℝ) :=
  constraintSet (P.constraints xIn)

/-- `z` is an optimal solution of problem (7) at ancestor decision `xIn`. -/
def IsOptimalSolution (P : NodeProblem nIn) (xIn : Fin nIn → ℝ)
    (z : Fin (P.n + 1) → ℝ) : Prop :=
  z ∈ P.feasibleSet xIn ∧ ∀ z' ∈ P.feasibleSet xIn, P.objective z ≤ P.objective z'

end NodeProblem

/-- Sign conditions on a vector of multipliers for a constraint family: nonnegative on
`≥` rows, nonpositive on `≤` rows, free on `=` rows. -/
def IsSignedMultiplier {ι : Type} {N : ℕ} (C : ι → LinearConstraint N) (lam : ι → ℝ) : Prop :=
  ∀ i, ((C i).rel = .ge → 0 ≤ lam i) ∧ ((C i).rel = .le → lam i ≤ 0)

/-- `lam` is a feasible solution of the linear-programming dual of `min cost ⬝ᵥ z` over the
constraint family `C`: signed multipliers whose combination of constraint vectors equals
the cost vector. -/
def IsDualFeasible {ι : Type} [Fintype ι] {N : ℕ} (C : ι → LinearConstraint N)
    (cost : Fin N → ℝ) (lam : ι → ℝ) : Prop :=
  IsSignedMultiplier C lam ∧ ∑ i, lam i • (C i).a = cost

/-- The dual objective `∑ᵢ λᵢ bᵢ`. -/
def dualObjective {ι : Type} [Fintype ι] {N : ℕ} (C : ι → LinearConstraint N)
    (lam : ι → ℝ) : ℝ :=
  ∑ i, lam i * (C i).b

/-- `lam` is an optimal dual vector: dual feasible and maximizing the dual objective among
dual feasible vectors. -/
def IsDualOptimal {ι : Type} [Fintype ι] {N : ℕ} (C : ι → LinearConstraint N)
    (cost : Fin N → ℝ) (lam : ι → ℝ) : Prop :=
  IsDualFeasible C cost lam ∧
    ∀ μ : ι → ℝ, IsDualFeasible C cost μ → dualObjective C μ ≤ dualObjective C lam

/-- A Farkas certificate of infeasibility of the constraint family `C`: signed multipliers
whose combination of constraint vectors vanishes while the same combination of
right-hand sides is positive. -/
def IsFarkasCertificate {ι : Type} [Fintype ι] {N : ℕ} (C : ι → LinearConstraint N)
    (lam : ι → ℝ) : Prop :=
  IsSignedMultiplier C lam ∧ ∑ i, lam i • (C i).a = 0 ∧ 0 < ∑ i, lam i * (C i).b

namespace NodeProblem

variable {nIn : ℕ}

/-- The multipliers of a multiplier vector on the rows (7.2): the vector `π`. -/
def eqPart (P : NodeProblem nIn) (lam : P.Idx → ℝ) : Fin P.m → ℝ :=
  fun k => lam (Sum.inl k)

/-- Slope of the cut induced by the multipliers `lam` of this (descendant) problem in the
ancestor decision: the row vector `-π B`, where `π` is the (7.2) part of `lam`. -/
def cutSlope (P : NodeProblem nIn) (lam : P.Idx → ℝ) : Fin nIn → ℝ :=
  -(P.eqPart lam ᵥ* P.B)

/-- Constant of the cut induced by the multipliers `lam`: the part of `∑ᵢ λᵢ bᵢ(xIn)` that
does not depend on the ancestor decision, i.e. `π ξ + ρ d + σ e` with `π, ρ, σ` the
multipliers of (7.2), (7.3), (7.4). -/
def cutConst (P : NodeProblem nIn) (lam : P.Idx → ℝ) : ℝ :=
  ∑ i, lam i * (P.constraints 0 i).b

end NodeProblem

/-- **Feasibility cut (7.3) generated by a descendant (Birge 1985, p. 993 and NDSPA Steps 1
and 2b, p. 995, construction of Van Slyke and Wets).** The descendant problem `Q` is
infeasible at the ancestor decision `x0`, certified by the Farkas certificate `lam` of its
constraint family at `x0`; the cut added to the ancestor is `D x ≥ d` with `D = -π B` and
`d = π ξ + ρ d_Q + σ e_Q`, which says that the certificate's right-hand-side combination at
`x` is `≤ 0`. -/
def IsGeneratedFeasibilityCut {nIn : ℕ} (Q : NodeProblem nIn) (x0 : Fin nIn → ℝ)
    (lam : Q.Idx → ℝ) (D : Fin nIn → ℝ) (d : ℝ) : Prop :=
  IsFarkasCertificate (Q.constraints x0) lam ∧ D = Q.cutSlope lam ∧ d = Q.cutConst lam

/-- **Optimality cut (7.4), NDSPA Step 3a (Birge 1985, p. 995), completed.** For the
descendant problems `Q j` (`j ∈ J'`) with weights `p j` and multiplier vectors `lam j`, the
cut `E x + θ ≥ e` has `E = -∑_j p_j π_j B_j` and `e = ∑_j p_j (π_j ξ_j + ρ_j d_j + σ_j e_j)`.
(The printed formula omits the weights and the terms `ρ_j d_j + σ_j e_j` of the
descendants' own cuts.) -/
def optimalityCutSlope {nIn : ℕ} {J : Type} [Fintype J] (Q : J → NodeProblem nIn)
    (p : J → ℝ) (lam : ∀ j, (Q j).Idx → ℝ) : Fin nIn → ℝ :=
  ∑ j, p j • (Q j).cutSlope (lam j)

/-- The constant `e` of the completed Step 3a optimality cut; see `optimalityCutSlope`. -/
def optimalityCutConst {nIn : ℕ} {J : Type} [Fintype J] (Q : J → NodeProblem nIn)
    (p : J → ℝ) (lam : ∀ j, (Q j).Idx → ℝ) : ℝ :=
  ∑ j, p j * (Q j).cutConst (lam j)

/-- **Validity of an optimality cut `E x + θ ≥ e` (the invariant NDSPA maintains).** The
affine function `e - E x` never exceeds the weighted sum `∑_j p_j (c_j y_j + θ_j)` of
objective values of feasible points of the descendant problems at `x`; equivalently
`e - E x ≤ ∑_j p_j v_j(x)` at every `x` where all descendants are feasible, `v_j` being
their optimal values. -/
def IsValidOptimalityCut {nIn : ℕ} {J : Type} [Fintype J] (Q : J → NodeProblem nIn)
    (p : J → ℝ) (E : Fin nIn → ℝ) (e : ℝ) : Prop :=
  ∀ (x : Fin nIn → ℝ) (z : ∀ j, Fin ((Q j).n + 1) → ℝ),
    (∀ j, z j ∈ (Q j).feasibleSet x) → e - E ⬝ᵥ x ≤ ∑ j, p j * (Q j).objective (z j)

end Birge1985.Degeneracy


