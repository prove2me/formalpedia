-- Prove2me | Definitions.Def_LostSalesOldNew_StateReduction_Model
-- name    : LostSalesOldNew_StateReduction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:32.48282+00:00
-- url     : https://prove2.me/theorems/a159fe14-113e-43c9-a3a6-a8825602b808
-- title:
--   Zipkin's lost-sales system: pipeline transition, demand laws, partial sums v_l, the sets X(s) and Z(s), vector base-stock policies and state trajectories
-- statement:
--   This file sets up the periodic-review, single-item lost-sales inventory system of Zipkin (2008) with a positive integer lead time $L$, together with the objects of its state-reduction argument.
--
--   **State and transition.** The state is the $L$-vector $x=(x_0,x_1,\dots,x_{L-1})$: $x_0$ is the stock on hand after the order due this period has arrived, and $x_l$ ($1\le l\le L-1$) is the outstanding order that arrives $l$ periods later, so $x_{L-1}$ is the most recent order. Given the state $x$, the order $z\ge 0$ placed now and the demand $d\ge 0$, unmet demand is lost and the next state is
--   $$
--   x_+ = \bigl([x_0-d]^+ + x_1,\; x_2,\;\dots,\;x_{L-1},\; z\bigr),
--   $$
--   where $[a]^+=\max(a,0)$. For $L=1$ this reads $x_+ = [x_0-d]^+ + z$. The auxiliary map $\mathrm{shift}$ takes a vector $(x_0,\dots,x_m)$ and a demand $d$ to $([x_0-d]^+ + x_1, x_2,\dots,x_m)$; the transition is $\mathrm{shift}$ applied to $(x_0,\dots,x_{L-1},z)$.
--
--   **Demand.** A demand law is a probability measure $D$ on $\mathbb R$ with $D((-\infty,0))=0$, i.e. demand is nonnegative. Demands in successive periods are independent with common law $D$.
--
--   **Pipeline partial sums.** For $l=0,\dots,L-1$,
--   $$
--   v_l = \sum_{m=l}^{L-1} x_m, \qquad v_L = 0 .
--   $$
--   Thus $v_{L-1}=x_{L-1}$ is the most recent order and $v_0$ is the inventory position.
--
--   **Level vectors, $X(s)$ and $Z(s)$.** A level vector is an $(L+1)$-vector $s=(s_0,\dots,s_L)$ with $s_0\ge s_1\ge\dots\ge s_L\ge 0$. For such $s$,
--   $$
--   X(s) = \{x\ge 0 : v_l\le s_l,\ l=0,\dots,L-1\},
--   $$
--   and $Z(s)$ is the set of stationary policies $z$ (a nonnegative order $z(x)$ for every state $x\ge 0$) such that $z(x)=0$ for every state $x\ge 0$ outside $X(s)$, and
--   $$
--   v_l + z(x)\le s_l, \qquad l=0,\dots,L,\ x\in X(s).
--   $$
--
--   **Vector base-stock policies.** The vector base-stock policy with parameter $s$ is equation (5) of the paper with $s$ in place of Morton's $\bar s$:
--   $$
--   z(x) = \Bigl[\min\{s_l - v_l,\ l=0,\dots,L\}\Bigr]^+ .
--   $$
--
--   **Trajectories.** For a stationary policy $z$, an initial state $x$ and a demand path $(d_t)_{t\ge 0}$, the state process is $x_0 = x$ (period $0$) and $x_{t+1} = (x_t)_+$ computed with order $z(x_t)$ and demand $d_t$.
--
--   These objects are the vocabulary of Claim 1 (states outside $X(s)$ are transient under any policy in $Z(s)$) and its proof. The transition, the map $\mathrm{shift}$ (the paper's $x_+^{l-1}$ of a subvector $x^l$, which involves no new order) and the demand law are also the dynamics on which the one-period costs $q^l$, the optimality equation (3) and the lead-time comparison of §5 are built.
--
--   **Formalization Note.** States are functions `Fin L → ℝ`; the vector $(x, z)$ is `Fin.snoc x z`. The definitions accept every real vector, while the theorems quantify over nonnegative states (the paper's state space is the nonnegative orthant). `v` takes a natural-number index and vanishes for $l\ge L$, so $v_L=0$ holds by definition. In $Z(s)$ the nonnegativity of orders and the condition "$z(x)=0$ for $x\notin X(s)$" range over states $x\ge 0$: the paper's state space is the orthant, and read over all of $\mathbb R^L$ the vector base-stock policy itself would not belong to $Z(s)$. Policies are arbitrary functions of the state (no measurability is imposed). The trajectory is indexed from period $0$.
-- source:
--   Zipkin, Old and New Methods for Lost-Sales Inventory Systems, Operations Research 56(5) (2008), §2 Formulation, pp. 1256–1257; §3 (definition of v_l and (5)), p. 1258; §4 State Reduction (X(s), Z(s)), p. 1259

import Mathlib

namespace LostSalesOldNew.StateReduction

open MeasureTheory

/-- One period of the lost-sales pipeline with no new order (p. 1257). From the vector
`(x_0, …, x_m)` and the demand `d` it returns the first `m` components of the next state,
`([x_0 − d]^+ + x_1, x_2, …, x_m)`. This is the paper's `x_+^{m−1}` of `x^m`. -/
noncomputable def shift {m : ℕ} (x : Fin (m + 1) → ℝ) (d : ℝ) : Fin m → ℝ :=
  fun i => if (i : ℕ) = 0 then max (x 0 - d) 0 + x i.succ else x i.succ

/-- The state transition of the system with lead time `L` (p. 1257):
`x_+ = ([x_0 − d]^+ + x_1, x_2, …, x_{L−1}, z)`. -/
noncomputable def next {L : ℕ} (x : Fin L → ℝ) (z d : ℝ) : Fin L → ℝ :=
  shift (Fin.snoc (α := fun _ => ℝ) x z) d

/-- A demand law (p. 1257: demands are independent, nonnegative and stationary): a probability law on
`[0, ∞)`. -/
structure IsDemand (D : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure D
  nonneg : D (Set.Iio 0) = 0

/-- `v_l = Σ_{m=l}^{L−1} x_m` for `l ≤ L − 1`, and `v_L = 0` (p. 1258). Defined for every `l : ℕ`;
it vanishes for `l ≥ L`. -/
def v {L : ℕ} (x : Fin L → ℝ) (l : ℕ) : ℝ :=
  ∑ m : Fin L, if l ≤ (m : ℕ) then x m else 0

/-- A level vector `s = (s_0, …, s_L)` with `s_0 ≥ s_1 ≥ ⋯ ≥ s_L ≥ 0` (p. 1259). -/
def IsLevelVector {L : ℕ} (s : Fin (L + 1) → ℝ) : Prop :=
  Antitone s ∧ 0 ≤ s (Fin.last L)

/-- `X(s) = {x ≥ 0 : v_l ≤ s_l, l = 0, …, L − 1}` (p. 1259). -/
def Xs {L : ℕ} (s : Fin (L + 1) → ℝ) : Set (Fin L → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ l : Fin L, v x l ≤ s l.castSucc}

/-- `Z(s)` (p. 1259): stationary policies `z` (an order `z(x) ≥ 0` in every state `x ≥ 0`) with
`z(x) = 0` for states `x ≥ 0` outside `X(s)`, and `v_l + z(x) ≤ s_l` for `l = 0, …, L` and
`x ∈ X(s)`. -/
def Zs {L : ℕ} (s : Fin (L + 1) → ℝ) : Set ((Fin L → ℝ) → ℝ) :=
  {z | (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → 0 ≤ z x) ∧
       (∀ x : Fin L → ℝ, (∀ i, 0 ≤ x i) → x ∉ Xs s → z x = 0) ∧
       (∀ x ∈ Xs s, ∀ l : Fin (L + 1), v x l + z x ≤ s l)}

/-- The vector base-stock policy with parameter `s`, (5) with `s` in place of `s̄` (p. 1258):
`z(x) = [min{s_l − v_l, l = 0, …, L}]^+`. -/
noncomputable def vectorBaseStock {L : ℕ} (s : Fin (L + 1) → ℝ) (x : Fin L → ℝ) : ℝ :=
  max (Finset.univ.inf' Finset.univ_nonempty (fun l : Fin (L + 1) => s l - v x l)) 0

/-- The state in period `t` under the stationary policy `z`, from the initial state `x`, along the
demand path `ds` (`ds t` is the demand of period `t`): `x_{t+1} = (x_t)_+` with order `z(x_t)`. -/
noncomputable def traj {L : ℕ} (z : (Fin L → ℝ) → ℝ) (x : Fin L → ℝ) (ds : ℕ → ℝ) :
    ℕ → (Fin L → ℝ)
  | 0 => x
  | t + 1 => next (traj z x ds t) (z (traj z x ds t)) (ds t)

end LostSalesOldNew.StateReduction


