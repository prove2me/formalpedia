-- Prove2me | Definitions.Def_KallenbergLP_Constrained_Problem
-- name    : KallenbergLP_Constrained_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:00.149159+00:00
-- url     : https://prove2.me/theorems/586e6d07-c378-49e6-b7db-a892dae765af
-- title:
--   The constrained Markov decision problem (4.7.5) and its linear program (4.7.6)
-- statement:
--   This file states the constrained average-reward problem of Section 4.7 of Kallenberg's book and the linear program that solves it.
--
--   Fix an initial distribution $\beta$, constraint coefficients $q_{iak}$ and bounds $b_k$, $k=1,\dots,m$. The lower average reward of a policy $R$ is
--
--   $$\phi(\beta,R)=\liminf_{T\to\infty}\frac1T\sum_{t=1}^T\sum_j\sum_a\sum_i\beta_i\,\mathbb P_R(X_t=j,\ Y_t=a\mid X_1=i)\,r_{ja}.$$
--
--   The **constrained Markov decision problem** (4.7.5) is
--
--   $$\sup_{R\in C_1}\Big\{\phi(\beta,R)\ \Big|\ \sum_i\sum_a q_{iak}\,x_{ia}(R)\le b_k,\ k=1,\dots,m\Big\},$$
--
--   where $x(R)$ is the unique limit point of the frequencies of $R\in C_1$. A policy is feasible when it lies in $C_1$ and satisfies the constraints, and optimal when it is feasible and attains the supremum. The **linear program** (4.7.6) maximizes $\sum_i\sum_a r_{ia}x_{ia}$ over the pairs $(x,y)$ that satisfy (4.7.7) and $\sum_i\sum_a q_{iak}x_{ia}\le b_k$, $1\le k\le m$.
--
--   The file also records the stationary decision rule (4.7.14) built from an optimal $(x^*,y^*)$: $\pi^*_{ia}=x^*_{ia}/\sum_a x^*_{ia}$ when $i\in E_{x^*}$, $\pi^*_{ia}=y^*_{ia}/\sum_a y^*_{ia}$ when $i\in E_{y^*}\setminus E_{x^*}$, and arbitrary elsewhere, where $E_x=\{i:\sum_a x_{ia}>0\}$.
--
--   **Formalization Note** Both optima are taken in the extended reals as suprema of the attained objective values, so an infeasible problem has optimum $-\infty$ (`⊥`). The rule (4.7.14) is a predicate `IsRule4714 x y π`; the "arbitrary" values are left free.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 137, (4.7.4)–(4.7.6); p. 141, (4.7.12); p. 144, (4.7.14); p. 36, Notation 3.1.1

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses Filter Topology

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- `φ(β, R) := liminf_{T→∞} (1/T) ∑_{t=1}^T ∑_j ∑_a ∑_i β_i ℙ_R(X_t = j, Y_t = a | X_1 = i) r_{ja}`,
the lower average reward of `R` under the initial distribution `β`.  Kallenberg (1983), p. 137. -/
noncomputable def avgReward {M : StationaryMDP S A} (β : S → ℝ) (R : AvgHRPolicy M) : ℝ :=
  liminf (fun T : ℕ => ∑ p : KallenbergLP.AverageLP.Pair M, freq β R T p * M.reward p.1.1 p.1.2) atTop

/-- Feasibility for the constrained problem (4.7.5): `R ∈ C_1` and its (unique) limit point
`x(R)` satisfies `∑_i ∑_a q_{iak} x_{ia}(R) ≤ b_k` for `k = 1, …, m`.  Kallenberg (1983), p. 137. -/
def Feasible475 {M : StationaryMDP S A} {m : ℕ} (β : S → ℝ) (q : KallenbergLP.AverageLP.Pair M → Fin m → ℝ)
    (b : Fin m → ℝ) (R : AvgHRPolicy M) : Prop :=
  IsC1 β R ∧ ∀ x ∈ limitPoints β R, ∀ k, ∑ p, q p k * x p ≤ b k

/-- An optimal solution of (4.7.5): a feasible `R` attaining `sup_{R ∈ C_1} {φ(β, R) | …}`. -/
def Optimal475 {M : StationaryMDP S A} {m : ℕ} (β : S → ℝ) (q : KallenbergLP.AverageLP.Pair M → Fin m → ℝ)
    (b : Fin m → ℝ) (R : AvgHRPolicy M) : Prop :=
  Feasible475 β q b R ∧ ∀ R', Feasible475 β q b R' → avgReward β R' ≤ avgReward β R

/-- The optimum of (4.7.5), `sup_{R ∈ C_1} {φ(β, R) | ∑_i ∑_a q_{iak} x_{ia}(R) ≤ b_k}`, in the
extended reals (`⊥` when the problem is infeasible). -/
noncomputable def value475 {M : StationaryMDP S A} {m : ℕ} (β : S → ℝ) (q : KallenbergLP.AverageLP.Pair M → Fin m → ℝ)
    (b : Fin m → ℝ) : EReal :=
  sSup ((fun R : AvgHRPolicy M => (avgReward β R : EReal)) '' {R | Feasible475 β q b R})

/-- The objective `∑_i ∑_a r_{ia} x_{ia}` of the linear program (4.7.6). -/
def lpObjective {M : StationaryMDP S A} (x : KallenbergLP.AverageLP.Pair M → ℝ) : ℝ :=
  ∑ p : KallenbergLP.AverageLP.Pair M, M.reward p.1.1 p.1.2 * x p

/-- Feasibility for the linear program (4.7.6) (= (4.7.12)): `(x, y)` satisfies (4.7.7) and
`∑_i ∑_a q_{iak} x_{ia} ≤ b_k`, `1 ≤ k ≤ m`.  Kallenberg (1983), p. 137. -/
def Feasible476 (M : StationaryMDP S A) {m : ℕ} (β : S → ℝ) (q : KallenbergLP.AverageLP.Pair M → Fin m → ℝ)
    (b : Fin m → ℝ) (x y : KallenbergLP.AverageLP.Pair M → ℝ) : Prop :=
  IsFeasible477 M β x y ∧ ∀ k, ∑ p, q p k * x p ≤ b k

/-- An optimal solution of the linear program (4.7.6). -/
def Optimal476 (M : StationaryMDP S A) {m : ℕ} (β : S → ℝ) (q : KallenbergLP.AverageLP.Pair M → Fin m → ℝ)
    (b : Fin m → ℝ) (x y : KallenbergLP.AverageLP.Pair M → ℝ) : Prop :=
  Feasible476 M β q b x y ∧
    ∀ x' y', Feasible476 M β q b x' y' → lpObjective x' ≤ lpObjective x

/-- The optimum of (4.7.6), in the extended reals (`⊥` when infeasible). -/
noncomputable def value476 (M : StationaryMDP S A) {m : ℕ} (β : S → ℝ) (q : KallenbergLP.AverageLP.Pair M → Fin m → ℝ)
    (b : Fin m → ℝ) : EReal :=
  sSup ((fun xy : (KallenbergLP.AverageLP.Pair M → ℝ) × (KallenbergLP.AverageLP.Pair M → ℝ) => (lpObjective xy.1 : EReal)) ''
    {xy | Feasible476 M β q b xy.1 xy.2})

/-- `∑_{a ∈ A(i)} x_{ia}`; the set `E_x = {i | ∑_a x_{ia} > 0}` of Notation 3.1.1, p. 36. -/
def stateMass {M : StationaryMDP S A} (x : KallenbergLP.AverageLP.Pair M → ℝ) (i : S) : ℝ :=
  ∑ a ∈ (M.admissible i).attach, x ⟨(i, a.1), a.2⟩

/-- (4.7.14): `π_{ia} = x_{ia} / ∑_a x_{ia}` for `i ∈ E_x`, `π_{ia} = y_{ia} / ∑_a y_{ia}` for
`i ∈ E_y \ E_x`, arbitrary elsewhere.  Kallenberg (1983), p. 144. -/
def IsRule4714 {M : StationaryMDP S A} (x y π : KallenbergLP.AverageLP.Pair M → ℝ) : Prop :=
  ∀ p : KallenbergLP.AverageLP.Pair M,
    (0 < stateMass x p.1.1 → π p = x p / stateMass x p.1.1) ∧
    (¬ 0 < stateMass x p.1.1 → 0 < stateMass y p.1.1 → π p = y p / stateMass y p.1.1)

end KallenbergLP.Constrained


