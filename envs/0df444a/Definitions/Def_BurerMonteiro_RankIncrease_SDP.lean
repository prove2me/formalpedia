-- Prove2me | Definitions.Def_BurerMonteiro_RankIncrease_SDP
-- name    : BurerMonteiro_RankIncrease_SDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:54:53.713865+00:00
-- url     : https://prove2.me/theorems/733fc2b6-ce68-47c7-8e51-6f6a267cd304
-- title:
--   The standard-form SDP (1), its dual (3), the trace inner product and the standing assumptions
-- statement:
--   This module fixes the primal–dual pair of semidefinite programs studied by Burer and Monteiro.
--
--   For real $p\times q$ matrices $A, B$ the **trace inner product** is $A\bullet B = \operatorname{trace}(A^{T}B)$. The data are a symmetric matrix $C\in\mathcal S^n$, symmetric matrices $A_1,\dots,A_m\in\mathcal S^n$ and a vector $b\in\mathbb R^m$. The **primal SDP** (1) and the **dual SDP** (3) are
--   $$\min\{\,C\bullet X : A_i\bullet X=b_i,\ i=1,\dots,m,\ X\succeq 0\,\},\qquad \max\Big\{\,b^{T}y : S=C-\sum_{i=1}^m y_iA_i,\ S\succeq 0\,\Big\}.$$
--
--   1. $S(y)=C-\sum_i y_iA_i$ is the **slack matrix** of $y$ (equation (8)).
--   2. $X$ is **primal feasible** if $X$ is symmetric positive semidefinite and $A_i\bullet X=b_i$ for every $i$; it is **primal optimal** if moreover $C\bullet X\le C\bullet X'$ for every primal feasible $X'$.
--   3. $(S,y)$ is **dual feasible** if $S=S(y)$ and $S\succeq 0$; it is **dual optimal** if moreover $b^Ty'\le b^Ty$ for every dual feasible $(S',y')$.
--   4. The **standing assumptions** of §2.1 are: $A_1,\dots,A_m$ are linearly independent, and there exist a primal feasible $X^*$ and a dual feasible $(S^*,y^*)$ with $C\bullet X^*=b^Ty^*$ (both problems have optimal solutions and the duality gap is zero).
--
--   These are the objects with respect to which the optimality certificates of Propositions 2.1, 2.4 and 2.5 are stated: optimality is over the whole feasible set of the SDP, not over factorized matrices.
--
--   **Formalization Note** Matrices are indexed by `Fin n`, `Fin m` (0-based). Over $\mathbb R$, Mathlib's `PosSemidef` includes symmetry, so "$X$ symmetric and $X\succeq 0$" is one clause. Optimality quantifies over every feasible point. The standing assumptions are a separate predicate, carried as a hypothesis by the theorems of §2, and are not built into feasibility or optimality.
-- source:
--   Burer & Monteiro, A nonlinear programming algorithm for solving semidefinite programs via low-rank factorization (manuscript of March 9, 2001; Math. Program. 95 (2003)), p. 2, Eq. (1); p. 4, §1.1 and §2.1, Eq. (3) and the standing assumptions; p. 6, Eq. (8)

import Mathlib

open Matrix

namespace BurerMonteiro.RankIncrease

/-- The trace inner product `A • B = trace(Aᵀ B)` of two real `p × q` matrices (§1.1, p. 4). -/
def frob {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  (Aᵀ * B).trace

/-- The dual slack matrix `S(y) = C − ∑ᵢ yᵢ Aᵢ` of (3) and (8) (pp. 4, 6). -/
def slack {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (y : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  C - ∑ i, y i • A i

/-- `X` is feasible for the primal SDP (1): `X` is symmetric positive semidefinite and
`Aᵢ • X = bᵢ` for every `i` (p. 2). -/
def IsPrimalFeasible {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.PosSemidef ∧ ∀ i, frob (A i) X = b i

/-- `(S, y)` is feasible for the dual SDP (3): `S = C − ∑ᵢ yᵢ Aᵢ` and `S ⪰ 0` (p. 4). -/
def IsDualFeasible {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) :
    Prop :=
  S = slack C A y ∧ S.PosSemidef

/-- `X` is optimal for the primal SDP (1): feasible, with `C • X ≤ C • X'` for every feasible
`X'`. -/
def IsPrimalOptimal {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    Prop :=
  IsPrimalFeasible A b X ∧ ∀ X', IsPrimalFeasible A b X' → frob C X ≤ frob C X'

/-- `(S, y)` is optimal for the dual SDP (3): feasible, with `bᵀy' ≤ bᵀy` for every feasible
`(S', y')`. -/
def IsDualOptimal {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin m → ℝ) : Prop :=
  IsDualFeasible C A S y ∧ ∀ S' y', IsDualFeasible C A S' y' → b ⬝ᵥ y' ≤ b ⬝ᵥ y

/-- The standing assumptions of §2.1 (p. 4): the constraint matrices `{Aᵢ}` are linearly
independent, and there are feasible `X∗` and `(S∗, y∗)` with `C • X∗ = bᵀy∗`. -/
def StandingAssumptions {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  LinearIndependent ℝ A ∧
    ∃ X S y, IsPrimalFeasible A b X ∧ IsDualFeasible C A S y ∧ frob C X = b ⬝ᵥ y

end BurerMonteiro.RankIncrease


