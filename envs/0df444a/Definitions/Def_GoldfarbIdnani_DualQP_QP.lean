-- Prove2me | Definitions.Def_GoldfarbIdnani_DualQP_QP
-- name    : GoldfarbIdnani_DualQP_QP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:02:50.364982+00:00
-- url     : https://prove2.me/theorems/fc872042-65f0-4ca0-8268-9a6b0f461373
-- title:
--   The strictly convex QP (1.1), subproblems $P(J)$, the operators $N^*$ and $H$ (2.1)–(2.2), S-pairs and V-triples
-- statement:
--   This module fixes the problem and the linear-algebra objects of Goldfarb and Idnani's dual method.
--
--   **Data and problem (1.1).** Let $n, m \in \mathbb N$, $a \in \mathbb R^n$, $G$ an $n\times n$ matrix, $C$ an $n \times m$ matrix and $b \in \mathbb R^m$. The quadratic program is
--
--   $$
--   \text{minimize } f(x) = a^{\mathsf T}x + \tfrac12 x^{\mathsf T}Gx \quad\text{subject to}\quad s(x) \equiv C^{\mathsf T}x - b \ge 0 .
--   $$
--
--   The index set of the constraints is $K = \{1,\dots,m\}$; the normal $n_i$ of constraint $i$ is the $i$-th column of $C$, so $s_i(x) = n_i^{\mathsf T}x - b_i$. The gradient of $f$ is $g(x) = Gx + a$. A point $x$ is *feasible* if $s(x) \ge 0$, and *optimal* if it is feasible and $f(x) \le f(y)$ for every feasible $y$.
--
--   **Subproblems.** For $J \subseteq K$, the subproblem $P(J)$ minimizes $f$ subject only to the constraints $s_i(x) \ge 0$, $i \in J$; $x$ is optimal for $P(J)$ if it satisfies these constraints and $f(x) \le f(y)$ for every $y$ that does. A set $A \subseteq K$ of constraints is *linearly independent* if the normals $\{n_i\}_{i \in A}$ are linearly independent.
--
--   **Operators (2.1)–(2.2).** For $A \subseteq K$ let $N$ be the $n \times |A|$ matrix with columns $n_i$, $i \in A$. Then
--
--   $$
--   N^* = (N^{\mathsf T}G^{-1}N)^{-1}N^{\mathsf T}G^{-1}, \qquad H = G^{-1} - G^{-1}N(N^{\mathsf T}G^{-1}N)^{-1}N^{\mathsf T}G^{-1}.
--   $$
--
--   For $A = \emptyset$, $H = G^{-1}$. The vector $N^*w$ is written with one entry per constraint index: the entry belonging to $i \in A$, and $0$ for $i \notin A$. With $w = g(x)$ this is the multiplier vector $u(x) = N^*g(x)$ of (2.3); with $w = n^+ = n_p$ it is the vector $r = N^*n^+$ of infeasibility multipliers (2.5); for $A^+ = A \cup \{p\}$ the same construction gives $H^+$ and $u^+(x) = (N^+)^*g(x)$, whose entry at $p$ is the paper's $u^+_{q+1}(x)$, $q = |A|$. The dual update $u^+ + t(-r; 1)$ adds $t$ to the entry at $p$ and subtracts $t\,r_i$ from every other entry $i$.
--
--   **S-pair (p. 3).** $(x, A)$ is an S-pair if the constraints in $A$ are linearly independent, $s_i(x) = 0$ for all $i \in A$, and $x$ is the optimal solution of $P(A)$.
--
--   **V-triple (Definition 1, p. 7).** $(x, A, p)$ with $p \in K \setminus A$ is a V-triple if the normals of $A^+ = A \cup \{p\}$ are linearly independent and
--
--   1. $s_p(x) < 0$, (3.1)
--   2. $s_i(x) = 0$ for all $i \in A$, (3.2)
--   3. $H^+g(x) = 0$, (3.3)
--   4. $u^+(x) \equiv (N^+)^*g(x) \ge 0$. (3.4)
--
--   **Partial step length (3.13).** For multipliers $u$ and $r$, $t_1 = \min\{u_j/r_j : j \in A,\ r_j > 0\}$ if some $r_j$, $j \in A$, is positive, and $t_1 = +\infty$ otherwise.
--
--   These are the objects in which Lemma 1 and Theorems 1–3 of the paper are stated.
--
--   **Formalization Note.** Vectors are functions `Fin n → ℝ`, active sets are `Finset (Fin m)`, and multiplier vectors are indexed by the constraint index (`Fin m → ℝ`, zero off the active set) rather than by position in $A$, so the paper's "element $k \in K$ corresponds to the $l$-th element in $A$" is not needed. Lean's matrix inverse is $0$ on singular matrices, so $N^*$ and $H$ carry their paper meaning only for linearly independent $A$ and positive definite $G$; every theorem using them assumes both. The S-pair is the reading in which $x$ solves $P(A)$ itself (the reading every later use in the paper relies on); the paper's p. 3 wording speaks of a solution of $P(J)$ lying on an independent active set $A \subseteq J$. $t_1$ takes values in `WithTop ℝ`, with $\top$ for $+\infty$.
-- source:
--   Goldfarb and Idnani, A numerically stable dual method for solving strictly convex quadratic programs, Math. Programming 27 (1983), p. 1, Eq. (1.1); pp. 3–4 (subproblems, S-pairs, linear independence); p. 5, Eqs. (2.1)–(2.5); p. 7, Definition 1 and (3.1)–(3.4); p. 8, Eq. (3.13)

import Mathlib

namespace GoldfarbIdnani.DualQP

open Matrix

variable {n m : ℕ}

/-- The objective (1.1a): `f(x) = aᵀx + ½ xᵀGx`. -/
noncomputable def f (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  a ⬝ᵥ x + (1 / 2 : ℝ) * (x ⬝ᵥ (G *ᵥ x))

/-- The gradient `g(x) = Gx + a` of `f` (p. 5). -/
def grad (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  G *ᵥ x + a

/-- The normal `nᵢ` of the `i`-th constraint: the `i`-th column of `C` (p. 4). -/
def normal (C : Matrix (Fin n) (Fin m) ℝ) (i : Fin m) : Fin n → ℝ :=
  fun k => C k i

/-- The constraint function (1.1b): `sᵢ(x) = nᵢᵀx − bᵢ`, i.e. `s(x) = Cᵀx − b`. -/
def slack (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  normal C i ⬝ᵥ x - b i

/-- `x` satisfies the constraints indexed by `J ⊆ K` (the constraints of the subproblem
`P(J)`, p. 3). -/
def FeasibleFor (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (J : Finset (Fin m))
    (x : Fin n → ℝ) : Prop :=
  ∀ i ∈ J, 0 ≤ slack C b x i

/-- `x` is feasible for the QPP (1.1): `Cᵀx − b ≥ 0`. -/
def Feasible (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ slack C b x i

/-- `x` is an optimal solution of the subproblem `P(J)`: feasible for the constraints in `J`
and no feasible point of `P(J)` has a smaller objective value. -/
def IsOptimalFor (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) (J : Finset (Fin m)) (x : Fin n → ℝ) : Prop :=
  FeasibleFor C b J x ∧ ∀ y, FeasibleFor C b J y → f a G x ≤ f a G y

/-- `x` is an optimal solution of the QPP (1.1). -/
def IsOptimal (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  Feasible C b x ∧ ∀ y, Feasible C b y → f a G x ≤ f a G y

/-- Linear independence of the constraints indexed by `A`: their normals are linearly
independent (p. 4). -/
def LinIndep (C : Matrix (Fin n) (Fin m) ℝ) (A : Finset (Fin m)) : Prop :=
  LinearIndependent ℝ (fun i : A => normal C i)

/-- `N`: the `n × q` matrix whose columns are the normals `nᵢ`, `i ∈ A` (p. 4), with columns
indexed by the elements of `A`. -/
def Nmat (C : Matrix (Fin n) (Fin m) ℝ) (A : Finset (Fin m)) : Matrix (Fin n) A ℝ :=
  fun k i => C k i

/-- The operator (2.1): `N* = (NᵀG⁻¹N)⁻¹NᵀG⁻¹`. -/
noncomputable def Nstar (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) : Matrix A (Fin n) ℝ :=
  ((Nmat C A)ᵀ * G⁻¹ * Nmat C A)⁻¹ * (Nmat C A)ᵀ * G⁻¹

/-- The operator (2.2): `H = G⁻¹ − G⁻¹N(NᵀG⁻¹N)⁻¹NᵀG⁻¹`. For `A = ∅` it is `G⁻¹`. -/
noncomputable def Hmat (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) : Matrix (Fin n) (Fin n) ℝ :=
  G⁻¹ - G⁻¹ * Nmat C A * ((Nmat C A)ᵀ * G⁻¹ * Nmat C A)⁻¹ * (Nmat C A)ᵀ * G⁻¹

/-- `N* w`, written as a vector indexed by the constraint indices `K = Fin m`: its entry at
`i ∈ A` is the entry of `N* w` belonging to constraint `i`, and it is `0` at `i ∉ A`.
With `w = g(x)` this is the multiplier vector `u(x)` of (2.3); with `w = n⁺` it is the
vector of infeasibility multipliers `r` of (2.5); with `A⁺ = A ∪ {p}` in place of `A`
it is `u⁺(x) = (N⁺)*g(x)`, whose entry at `p` is the paper's `u⁺_{q+1}`. -/
noncomputable def multVec (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) (w : Fin n → ℝ) : Fin m → ℝ :=
  fun i => if h : i ∈ A then (Nstar G C A *ᵥ w) ⟨i, h⟩ else 0

/-- Restriction of a vector indexed by `K` to the index set `S`: entries outside `S` are set
to `0`. -/
def restrict (S : Finset (Fin m)) (v : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if i ∈ S then v i else 0

/-- The dual update `u⁺ + t(−r; 1)` of (3.9) and Step 2(c), on vectors indexed by `K`:
the entry at `p` is increased by `t` and every other entry `i` is decreased by `t rᵢ`. -/
def dualStep (u r : Fin m → ℝ) (p : Fin m) (t : ℝ) : Fin m → ℝ :=
  fun i => if i = p then u i + t else u i - t * r i

/-- Solution pair (S-pair), p. 3: the constraints of `A` are linearly independent, active at
`x` (`sᵢ(x) = 0`, `i ∈ A`), and `x` is the optimal solution of the subproblem `P(A)`. -/
def IsSPair (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (A : Finset (Fin m)) : Prop :=
  LinIndep C A ∧ (∀ i ∈ A, slack C b x i = 0) ∧ IsOptimalFor a G C b A x

/-- V (violated)-triple, Definition 1, p. 7: `p ∈ K ∖ A`, the normals of `A⁺ = A ∪ {p}` are
linearly independent, and (3.1)–(3.4) hold: `s_p(x) < 0`, `sᵢ(x) = 0` for `i ∈ A`,
`H⁺g(x) = 0` and `u⁺(x) = (N⁺)*g(x) ≥ 0`. -/
def IsVTriple (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m) : Prop :=
  p ∉ A ∧ LinIndep C (insert p A) ∧
    slack C b x p < 0 ∧
    (∀ i ∈ A, slack C b x i = 0) ∧
    Hmat G C (insert p A) *ᵥ grad a G x = 0 ∧
    (∀ i ∈ insert p A, 0 ≤ multVec G C (insert p A) (grad a G x) i)

/-- The partial step length `t₁` of (3.13) and Step 2(b)(i): `+∞` if no `rⱼ`, `j ∈ A`, is
positive (in particular if `q = 0`), and otherwise `min {uⱼ / rⱼ : j ∈ A, rⱼ > 0}`. -/
noncomputable def t1 (A : Finset (Fin m)) (u r : Fin m → ℝ) : WithTop ℝ :=
  if h : (A.filter (fun j => 0 < r j)).Nonempty then
    (((A.filter (fun j => 0 < r j)).inf' h (fun j => u j / r j) : ℝ) : WithTop ℝ)
  else ⊤

end GoldfarbIdnani.DualQP


