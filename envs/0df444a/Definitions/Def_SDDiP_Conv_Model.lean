-- Prove2me | Definitions.Def_SDDiP_Conv_Model
-- name    : SDDiP_Conv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T03:44:24.441991+00:00
-- url     : https://prove2.me/theorems/ad6c76f6-5a98-4027-a8de-40f2aeb232d5
-- title:
--   Multistage stochastic MILP with binary states on a scenario tree: (A1), (2.1), value functions (2.3) and the extensive-form optimum
-- statement:
--   Let $\mathcal T$ be a finite scenario tree with $T$ stages. The root $1$ is the unique node of stage $1$; every other node $n$ has a parent $a(n)$ in the previous stage; $\mathcal C(n)$ is the set of children of $n$; the nodes of the last stage are the **scenarios**. Each node carries a probability $p_n > 0$ with $p_1 = 1$ and $p_n = \sum_{m\in\mathcal C(n)} p_m$ for every node before the last stage, and $q_{nm} = p_m/p_n$ is the conditional probability of moving from $n$ to its child $m$.
--
--   The data of node $n$ are a linear objective $f_n(x_n, y_n) = c_n^\top x_n + e_n^\top y_n$ and a constraint set $X_n \subseteq \mathbb R^d\times\mathbb R^d\times\mathbb R^\ell$ in the variables $(z_n, x_n, y_n)$, which is a nonempty compact mixed integer polyhedral set (assumption (A1)): the solutions of finitely many linear inequalities, some of whose coordinates are required to be integers. The **state** $x_n \in \{0,1\}^d$ is binary, the local variables $y_n \in \mathbb R^\ell$ are general. The root's parent state $\bar x_0 \in [0,1]^d$ is fixed. Every nodal problem is assumed feasible: at the root for $\bar x_0$, at every other node for every binary parent state.
--
--   The multistage program in the local-copy form (2.1) is
--   $$\min \sum_{n\in\mathcal T} p_n f_n(x_n, y_n)\quad\text{s.t.}\quad (z_n, x_n, y_n)\in X_n,\ z_n = x_{a(n)},\ z_n\in[0,1]^d,\ x_n\in\{0,1\}^d\quad\forall n\in\mathcal T,$$
--   with $x_{a(1)} = \bar x_0$. A tree solution $\{(x_n, y_n)\}_{n\in\mathcal T}$ is **optimal** if it is feasible and its cost is at most that of every feasible tree solution.
--
--   The value functions (2.3) are defined by backward recursion over the stages: for a binary parent state $x_{a(n)}$,
--   $$Q_n(x_{a(n)}) = \min_{x_n, y_n}\Big\{ f_n(x_n, y_n) + \mathcal Q_n(x_n) : (x_{a(n)}, x_n, y_n)\in X_n,\ x_n\in\{0,1\}^d \Big\},\qquad \mathcal Q_n(x) = \sum_{m\in\mathcal C(n)} q_{nm} Q_m(x),$$
--   so the expected cost-to-go function $\mathcal Q_n$ vanishes at the scenarios. More generally, for a parent state $\hat x$ and a function $\psi$ on $\{0,1\}^d$, the nodal value $\min\{f_n(x,y) + \psi(x) : (\hat x, x, y)\in X_n,\ x\in\{0,1\}^d\}$ is the optimal value of the nodal problem of $n$; with $\psi = \mathcal Q_n$ it is $Q_n$, at the root with $\hat x = \bar x_0$ it is the value of (2.2), and with an approximation $\psi = \psi^i_n$ it is $\underline Q^i_n(\hat x, \psi^i_n)$ of (3.1).
--
--   These objects are the model on which the stochastic nested decomposition (SND) algorithm and its convergence theorem are stated.
--
--   **Formalization Note** The tree is the platform's `StochasticProg.Multistage.Tree H` (stage $t$ of the paper is `stage = t − 1`). Binary vectors are `Fin d → Bool`, embedded in $\mathbb R^d$ by `toReal`. The copy variable $z_n$ is eliminated through $z_n = x_{a(n)}$, and (2.1c) holds because the parent state is binary or $\bar x_0\in[0,1]^d$. The minima are written as infima (`nodalValue`); under the standing assumptions every infimum that the theorems use is over a nonempty set, is bounded below and is attained, so it is the paper's minimum. Positivity of $p_n$ and nodal feasibility for binary parent states are hypotheses the paper uses without stating them (the latter replaces (A2), which Theorem 2 does not use); positivity also forces every node before the last stage to have a child.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), §1.1 pp. 463–464 (scenario tree, (1.1)–(1.3)); §2 p. 467 (A1), p. 468 (2.1)–(2.2), p. 469 (2.3)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree

namespace SDDiP.Conv

open StochasticProg.Multistage

/-- The real vector in `{0,1}^d ⊆ ℝ^d` represented by a Boolean vector: coordinate `j` is `1` if
`b j = true` and `0` otherwise. Binary state variables `x_n ∈ {0,1}^d` (Zou–Ahmed–Sun, p. 467 and
(2.1d), p. 468) are stored as `Fin d → Bool` and enter the constraint set `X_n` through this map. -/
def toReal {d : ℕ} (b : Fin d → Bool) : Fin d → ℝ := fun j => if b j then 1 else 0

/-- A mixed integer polyhedral subset of `ℝ^d × ℝ^d × ℝ^ℓ` (variables `(z, x, y)`), as in (A1) of
Zou–Ahmed–Sun (p. 467): the solutions of finitely many linear inequalities
`A^z_k z + A^x_k x + A^y_k y ≤ b_k` (equalities are pairs of inequalities) in which the coordinates
indexed by `Jz`, `Jx`, `Jy` are in addition required to be integers. -/
def IsMixedIntegerPolyhedral {d ℓ : ℕ} (S : Set ((Fin d → ℝ) × (Fin d → ℝ) × (Fin ℓ → ℝ))) : Prop :=
  ∃ (r : ℕ) (Az Ax : Fin r → Fin d → ℝ) (Ay : Fin r → Fin ℓ → ℝ) (b : Fin r → ℝ)
    (Jz Jx : Finset (Fin d)) (Jy : Finset (Fin ℓ)),
    S = {w | (∀ k, ∑ j, Az k j * w.1 j + ∑ j, Ax k j * w.2.1 j + ∑ j, Ay k j * w.2.2 j ≤ b k) ∧
      (∀ j ∈ Jz, ∃ c : ℤ, w.1 j = (c : ℝ)) ∧ (∀ j ∈ Jx, ∃ c : ℤ, w.2.1 j = (c : ℝ)) ∧
      (∀ j ∈ Jy, ∃ c : ℤ, w.2.2 j = (c : ℝ))}

/-- A multistage stochastic mixed integer linear program with binary state variables on a scenario
tree, as in Zou–Ahmed–Sun, *Stochastic dual dynamic integer programming*, Math. Program. 175 (2019),
§1.1 (p. 463), §2 (A1) (p. 467) and the reformulation (2.1) (p. 468).

* `T` is the scenario tree with `H` stages (paper: `T` levels); the paper's stage `t` is
  `T.stage n = t − 1`, the root node `1` is `T.root`, `a(n)` is `T.anc n` and `C(n)` is
  `T.children n`. Nodes of the last stage `H − 1` are the scenarios (leaves).
* `p n > 0` is the probability of node `n`, `p root = 1`, and the probability of a node that is not in
  the last stage is the sum of the probabilities of its children; `q n m = p m / p n` (p. 463).
  Positivity is implicit in the paper ("each one is sampled with a positive probability", p. 476);
  it also forces every node before the last stage to have a child.
* The objective of node `n` is the linear function `f_n(x, y) = ⟨c n, x⟩ + ⟨e n, y⟩` (A1).
* `X n ⊆ ℝ^d × ℝ^d × ℝ^ℓ` is the constraint set in the variables `(z_n, x_n, y_n)`; it is a nonempty
  compact mixed integer polyhedral set (A1).
* `x0` is the fixed parent state `x̄_0 = x_{a(1)}` of the root (p. 462, Algorithm 1 line 29); it lies in
  `[0,1]^d`, as (2.1c) requires of `z_1 = x_{a(1)}`.
* Added hypothesis (relatively complete recourse for binary states; it replaces the paper's (A2), which
  Theorem 2 does not use): every nodal problem is feasible, at the root for the parent state `x0` and at
  every other node for every binary parent state. It makes every minimum in (2.2), (2.3), (3.1) a
  minimum over a nonempty set. -/
structure Model (H d ℓ : ℕ) where
  T : Tree H
  hH : 0 < H
  p : T.Node → ℝ
  p_pos : ∀ n, 0 < p n
  p_root : p T.root = 1
  p_children : ∀ n, (T.stage n).val + 1 < H → p n = ∑ m ∈ T.children n, p m
  c : T.Node → Fin d → ℝ
  e : T.Node → Fin ℓ → ℝ
  X : T.Node → Set ((Fin d → ℝ) × (Fin d → ℝ) × (Fin ℓ → ℝ))
  X_polyhedral : ∀ n, IsMixedIntegerPolyhedral (X n)
  X_compact : ∀ n, IsCompact (X n)
  X_nonempty : ∀ n, (X n).Nonempty
  x0 : Fin d → ℝ
  x0_mem : ∀ j, 0 ≤ x0 j ∧ x0 j ≤ 1
  feasible_root : ∃ (x : Fin d → Bool) (y : Fin ℓ → ℝ), (x0, toReal x, y) ∈ X T.root
  feasible : ∀ n, n ≠ T.root → ∀ xa : Fin d → Bool,
    ∃ (x : Fin d → Bool) (y : Fin ℓ → ℝ), (toReal xa, toReal x, y) ∈ X n

namespace Model

variable {H d ℓ : ℕ} (D : Model H d ℓ)

/-- A node is a leaf (a scenario, a node of the final stage `S_T`) when it lies in the last stage. -/
def IsLeaf (n : D.T.Node) : Prop := (D.T.stage n).val + 1 = H

instance (n : D.T.Node) : Decidable (D.IsLeaf n) := inferInstanceAs (Decidable (_ = _))

/-- The scenarios: the nodes of the last stage `S_T`. -/
def Leaf : Type := {n : D.T.Node // D.IsLeaf n}

noncomputable instance : Fintype D.Leaf := Subtype.fintype _
instance : DecidableEq D.Leaf := inferInstanceAs (DecidableEq {n : D.T.Node // D.IsLeaf n})

/-- The conditional probability `q_{nm} = p_m / p_n` of moving from `n` to its child `m` (p. 463). -/
noncomputable def q (n m : D.T.Node) : ℝ := D.p m / D.p n

/-- The linear objective `f_n(x_n, y_n) = ⟨c_n, x_n⟩ + ⟨e_n, y_n⟩` of node `n` (A1), at a binary state. -/
noncomputable def f (n : D.T.Node) (x : Fin d → Bool) (y : Fin ℓ → ℝ) : ℝ :=
  ∑ j, D.c n j * toReal x j + ∑ j, D.e n j * y j

/-- The feasible set of the nodal problem of node `n` when the parent state is `xa`: the pairs `(x, y)`
with `x ∈ {0,1}^d` and `(z, x, y) ∈ X_n` for the copy `z = xa` ((2.1a), (2.1b), (2.1d); the copy
variable `z_n` is eliminated through `z_n = x_{a(n)}`). -/
def feasibleSet (n : D.T.Node) (xa : Fin d → ℝ) : Set ((Fin d → Bool) × (Fin ℓ → ℝ)) :=
  {w | (xa, toReal w.1, w.2) ∈ D.X n}

/-- The optimal value `min { f_n(x, y) + ψ(x) : (xa, x, y) ∈ X_n, x ∈ {0,1}^d }` of the nodal problem of
node `n` with parent state `xa` and cost-to-go function `ψ` on `{0,1}^d`. With `ψ = 𝒬_n` this is the
value `Q_n(xa)` of (2.3) (and at the root with `xa = x̄_0`, the value of (2.2)); with `ψ = ψ^i_n` it is
`Q̲^i_n(xa, ψ^i_n)` of (3.1). It is written as an infimum; under the standing assumptions of `Model`
(feasibility, compactness of `X_n`, finiteness of `{0,1}^d`) the set is nonempty, bounded below and the
infimum is attained, so it is the paper's minimum. -/
noncomputable def nodalValue (n : D.T.Node) (xa : Fin d → ℝ) (ψ : (Fin d → Bool) → ℝ) : ℝ :=
  sInf ((fun w => D.f n w.1 w.2 + ψ w.1) '' D.feasibleSet n xa)

/-- `w = (x, y)` is an optimal solution of the nodal problem of node `n` with parent state `xa` and
cost-to-go function `ψ`. -/
def IsNodalOptimal (n : D.T.Node) (xa : Fin d → ℝ) (ψ : (Fin d → Bool) → ℝ)
    (w : (Fin d → Bool) × (Fin ℓ → ℝ)) : Prop :=
  w ∈ D.feasibleSet n xa ∧
    ∀ w' ∈ D.feasibleSet n xa, D.f n w.1 w.2 + ψ w.1 ≤ D.f n w'.1 w'.2 + ψ w'.1

/-- The true value function `Q_n(x_{a(n)})` of (2.3) (p. 468), at a binary parent state, defined by
backward recursion over the stages:
`Q_n(x_{a(n)}) = min f_n(x_n, y_n) + Σ_{m ∈ C(n)} q_{nm} Q_m(x_n)` over `(x_{a(n)}, x_n, y_n) ∈ X_n`,
`x_n ∈ {0,1}^d`. At a leaf the sum is empty. -/
noncomputable def Q (n : D.T.Node) (xa : Fin d → Bool) : ℝ :=
  D.nodalValue n (toReal xa) (fun x => ∑ m ∈ (D.T.children n).attach, D.q n m.1 * Q m.1 x)
termination_by H - (D.T.stage n).val
decreasing_by
  have hm := m.2
  simp only [Tree.children, Finset.mem_filter] at hm
  have := (D.T.stage m.1).isLt
  omega

/-- The expected cost-to-go function `𝒬_n(x) = Σ_{m ∈ C(n)} q_{nm} Q_m(x)` of node `n` (p. 464);
it is `0` at a leaf. -/
noncomputable def Qcal (n : D.T.Node) (x : Fin d → Bool) : ℝ :=
  ∑ m ∈ D.T.children n, D.q n m * D.Q m x

/-- The defining recursion (2.3): `Q_n(xa) = min { f_n(x, y) + 𝒬_n(x) }`. -/
theorem Q_eq (n : D.T.Node) (xa : Fin d → Bool) :
    D.Q n xa = D.nodalValue n (toReal xa) (D.Qcal n) := by
  rw [Q]
  congr 1
  funext x
  exact Finset.sum_attach (D.T.children n) (fun m => D.q n m * D.Q m x)

/-- A solution of the extensive form (2.1) over the tree: a binary state `x_n` and local variables
`y_n` at every node. -/
abbrev TreeSol := D.T.Node → (Fin d → Bool) × (Fin ℓ → ℝ)

/-- The parent state `x_{a(n)}` of node `n` in a tree solution; for the root it is the fixed `x̄_0`. -/
noncomputable def parentState (w : D.TreeSol) (n : D.T.Node) : Fin d → ℝ := by
  classical
  exact if n = D.T.root then D.x0 else toReal (w (D.T.anc n)).1

/-- Feasibility for (2.1): `(z_n, x_n, y_n) ∈ X_n` with `z_n = x_{a(n)}` at every node ((2.1a), (2.1b));
`x_n ∈ {0,1}^d` (2.1d) holds by the type, and (2.1c) by `x0_mem` and binarity. -/
def IsFeasible (w : D.TreeSol) : Prop :=
  ∀ n, (D.parentState w n, toReal (w n).1, (w n).2) ∈ D.X n

/-- The objective `Σ_{n ∈ T} p_n f_n(x_n, y_n)` of (2.1). -/
noncomputable def cost (w : D.TreeSol) : ℝ := ∑ n, D.p n * D.f n (w n).1 (w n).2

/-- `w` is an optimal solution of the multistage stochastic program (2.1): it is feasible and its cost
is at most the cost of every feasible tree solution. -/
def IsOptimal (w : D.TreeSol) : Prop :=
  D.IsFeasible w ∧ ∀ w', D.IsFeasible w' → D.cost w ≤ D.cost w'

end Model

end SDDiP.Conv


