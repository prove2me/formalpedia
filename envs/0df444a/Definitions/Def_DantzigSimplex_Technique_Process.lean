-- Prove2me | Definitions.Def_DantzigSimplex_Technique_Process
-- name    : DantzigSimplex_Technique_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:05:25.437966+00:00
-- url     : https://prove2.me/theorems/74ce9c47-c767-4d0b-964b-026397d4c8f8
-- title:
--   Nondegeneracy, reference-point states, and the two-phase simplex transitions
-- statement:
--   The paper assumes every $m$ distinct indexed points among $P_0,P_1,\ldots,P_n$ are linearly independent. A Phase II state consists of a set $B$ of $m$ column indices, positive weights $\lambda_i$ on $B$ and zero weights elsewhere, with $\sum_{i\in B}\lambda_iP_i=P_0$. For each $j$, its coordinates $x_{ij}$ satisfy $P_j=\sum_{i\in B}x_{ij}P_i$ and $z_j=\sum_{i\in B}x_{ij}c_i$. A Phase II pivot selects $j$ with $c_j>z_j$, chooses the minimum positive ratio $\theta=\min_{i\in B:x_{ij}>0}\lambda_i/x_{ij}$, and replaces a minimizing basis index by $j$ with weights from (13).
--
--   A Phase I state uses a fixed reference point $G$, a set $S$ of $m-1$ indices, positive weights $w_i$ on $S$, and $\rho>0$ satisfying $G+\rho P_0=\sum_{i\in S}w_iP_i$. Coordinates satisfy $P_j=y_{0j}P_0+\sum_{i\in S}y_{ij}P_i$. A Phase I pivot selects $y_{0j}>0$, uses the minimum positive ratio $\theta=\min_{i\in S:y_{ij}>0}w_i/y_{ij}$, replaces the minimizing index by $j$, and updates $\rho$ to $\rho+\theta y_{0j}$. If $y_{0j}>0$ and all $y_{ij}\le0$, the hand-off forms the feasible weights in (39). The combined transition system has exactly these Phase I pivots, hand-offs, and Phase II pivots; a terminal state has no outgoing transition.
--
--   **Formalization Note** Each frame carries the coordinate equations and linear independence that make the coordinates unique. Every state carries strictly positive basic weights; the target of a pivot must satisfy the same invariants. The additional general-position condition says that every indexed family consisting of $G$, $P_0$, and $m-2$ of the $P_j$ is linearly independent. It excludes simultaneous vanishing in Phase I. For $m=1$ that family does not exist and Phase I has no pivot.
-- source:
--   Dantzig, Maximization of a Linear Function of Variables Subject to Linear Inequalities, in Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley 1951, Ch. XXI, pp. 340–342 and 345–347, Eqs. (7)–(10), (13), (16), (30), (34)–(41), conditions (17)–(18), (44)–(45)

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Problem

namespace DantzigSimplex.Technique

def Problem.point {m n : ℕ} (p : Problem m n) : Option (Fin n) → Fin m → ℝ
  | none => p.rhs
  | some j => p.col j

/-- Every indexed family of `m` among `P₀,P₁,...,Pₙ` is independent. -/
def Problem.Nondegenerate {m n : ℕ} (p : Problem m n) : Prop :=
  ∀ S : Finset (Option (Fin n)), S.card = m →
    LinearIndependent ℝ (fun a : {j // j ∈ S} => p.point a.1)

def augmentedPoint {m n : ℕ} (p : Problem m n) (G : Fin m → ℝ) :
    Option (Option (Fin n)) → Fin m → ℝ
  | none => G
  | some none => p.rhs
  | some (some j) => p.col j

/-- The reference point avoids simultaneous vanishing in the Phase I ratio test. -/
def GeneralPosition {m n : ℕ} (p : Problem m n) (G : Fin m → ℝ) : Prop :=
  ∀ S : Finset (Option (Option (Fin n))), S.card = m →
    none ∈ S → some none ∈ S →
    LinearIndependent ℝ (fun a : {j // j ∈ S} => augmentedPoint p G a.1)

/-- The Phase II basis and the unique coordinates in (9)--(10). -/
structure PhaseIIFrame {m n : ℕ} (p : Problem m n) where
  B : Finset (Fin n)
  hcard : B.card = m
  hind : LinearIndependent ℝ (fun a : {j // j ∈ B} => p.col a.1)
  x : Fin n → Fin n → ℝ
  hcoord : ∀ j, (fun a : Fin m => ∑ i ∈ B, x i j * p.col i a) = p.col j

def PhaseIIFrame.z {m n : ℕ} {p : Problem m n} (q : PhaseIIFrame p)
    (j : Fin n) : ℝ := ∑ i ∈ q.B, q.x i j * p.cost i

/-- A strictly positive `m`-column feasible state, as in (7)--(8). -/
structure PhaseIIState {m n : ℕ} (p : Problem m n) where
  frame : PhaseIIFrame p
  weight : Fin n → ℝ
  hpositive : ∀ i ∈ frame.B, 0 < weight i
  hzero : ∀ i ∉ frame.B, weight i = 0
  hfeasible : p.Feasible weight

/-- The Phase I basis `(P₀; P_i, i∈S)` and coordinates (30). -/
structure PhaseIFrame {m n : ℕ} (p : Problem m n) where
  S : Finset (Fin n)
  hcard : S.card + 1 = m
  hind : LinearIndependent ℝ
    (fun a : {j // j ∈ insert none (S.image some)} => p.point a.1)
  y0 : Fin n → ℝ
  y : Fin n → Fin n → ℝ
  hcoord : ∀ j, (fun a : Fin m =>
    y0 j * p.rhs a + ∑ i ∈ S, y i j * p.col i a) = p.col j

/-- Equation (35), with the fixed reference point and strictly positive basic weights. -/
structure PhaseIState {m n : ℕ} (p : Problem m n) (G : Fin m → ℝ) where
  frame : PhaseIFrame p
  weight : Fin n → ℝ
  rho : ℝ
  hrho : 0 < rho
  hpositive : ∀ i ∈ frame.S, 0 < weight i
  hzero : ∀ i ∉ frame.S, weight i = 0
  hreference : (fun a : Fin m => G a + rho * p.rhs a) = p.combine weight

/-- The family of coefficients in (13), for a nonbasic entering column. -/
def phaseIIWeights {m n : ℕ} {p : Problem m n} (s : PhaseIIState p)
    (j : Fin n) (θ : ℝ) : Fin n → ℝ :=
  fun k => if k = j then θ else if k ∈ s.frame.B then
    s.weight k - θ * s.frame.x k j else 0

/-- The Phase I weights in (37). -/
def phaseIWeights {m n : ℕ} {p : Problem m n} {G : Fin m → ℝ}
    (s : PhaseIState p G) (j : Fin n) (θ : ℝ) : Fin n → ℝ :=
  fun k => if k = j then θ else if k ∈ s.frame.S then
    s.weight k - θ * s.frame.y k j else 0

/-- The explicit feasible weights in (39). -/
noncomputable def handoffWeights {m n : ℕ} {p : Problem m n} {G : Fin m → ℝ}
    (s : PhaseIState p G) (j : Fin n) : Fin n → ℝ :=
  fun k => if k = j then 1 / s.frame.y0 j else if k ∈ s.frame.S then
    -(s.frame.y k j) / s.frame.y0 j else 0

/-- A Phase II pivot with an attained minimum in (16). -/
def PhaseIIStep {m n : ℕ} {p : Problem m n}
    (s t : PhaseIIState p) : Prop :=
  ∃ (j i₀ : Fin n) (θ : ℝ),
    j ∉ s.frame.B ∧ i₀ ∈ s.frame.B ∧
    p.cost j > s.frame.z j ∧ 0 < s.frame.x i₀ j ∧
    θ = s.weight i₀ / s.frame.x i₀ j ∧
    (∀ i ∈ s.frame.B, 0 < s.frame.x i j →
      θ ≤ s.weight i / s.frame.x i j) ∧
    t.frame.B = insert j (s.frame.B.erase i₀) ∧
    t.weight = phaseIIWeights s j θ

/-- A Phase I pivot with an attained minimum in (40), and (41). -/
def PhaseIStep {m n : ℕ} {p : Problem m n} {G : Fin m → ℝ}
    (s t : PhaseIState p G) : Prop :=
  ∃ (j i₀ : Fin n) (θ : ℝ),
    j ∉ s.frame.S ∧ i₀ ∈ s.frame.S ∧
    0 < s.frame.y0 j ∧ 0 < s.frame.y i₀ j ∧
    θ = s.weight i₀ / s.frame.y i₀ j ∧
    (∀ i ∈ s.frame.S, 0 < s.frame.y i j →
      θ ≤ s.weight i / s.frame.y i j) ∧
    t.frame.S = insert j (s.frame.S.erase i₀) ∧
    t.weight = phaseIWeights s j θ ∧
    t.rho = s.rho + θ * s.frame.y0 j

/-- The transition from (45) to the Phase II solution (39). -/
def HandOff {m n : ℕ} {p : Problem m n} {G : Fin m → ℝ}
    (s : PhaseIState p G) (t : PhaseIIState p) : Prop :=
  ∃ j : Fin n, j ∉ s.frame.S ∧ 0 < s.frame.y0 j ∧
    (∀ i ∈ s.frame.S, s.frame.y i j ≤ 0) ∧
    t.frame.B = insert j s.frame.S ∧
    t.weight = handoffWeights s j

abbrev SimplexState {m n : ℕ} (p : Problem m n) (G : Fin m → ℝ) :=
  PhaseIState p G ⊕ PhaseIIState p

inductive SimplexStep {m n : ℕ} {p : Problem m n} {G : Fin m → ℝ} :
    SimplexState p G → SimplexState p G → Prop
  | phaseI {s t} : PhaseIStep s t → SimplexStep (Sum.inl s) (Sum.inl t)
  | handoff {s t} : HandOff s t → SimplexStep (Sum.inl s) (Sum.inr t)
  | phaseII {s t} : PhaseIIStep s t → SimplexStep (Sum.inr s) (Sum.inr t)

def Terminal {m n : ℕ} {p : Problem m n} {G : Fin m → ℝ}
    (s : SimplexState p G) : Prop := ¬ ∃ t, SimplexStep s t

end DantzigSimplex.Technique


