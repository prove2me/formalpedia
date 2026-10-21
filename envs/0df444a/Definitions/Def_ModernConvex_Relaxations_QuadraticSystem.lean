-- Prove2me | Definitions.Def_ModernConvex_Relaxations_QuadraticSystem
-- name    : ModernConvex_Relaxations_QuadraticSystem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:04.434377+00:00
-- url     : https://prove2.me/theorems/c5722b16-c1c4-453c-ba89-b2416b1769db
-- title:
--   The setting (SL.??): max of xᵀAx on {xᵀBᵢx ≤ dᵢ}, its relaxation (SDP) and the dual (SDD)
-- statement:
--   This file fixes the setting (SL.??) of Ben-Tal–Nemirovski, pp. 313–314. Let $B_1, \dots, B_m$ and $A$ be $n\times n$ matrices and $d_1, \dots, d_m$ real numbers. Consider the system of quadratic inequalities
--   $$(S')\qquad x^TB_ix \le d_i,\quad i = 1,\dots,m,$$
--   and the homogeneous quadratic form $f(x) = x^TAx$.
--
--   1. $(S')$ is **strictly feasible** if some $x$ satisfies $x^TB_ix < d_i$ for every $i$.
--   2. $f^*$ is the optimal value of $(P)\ \max_x\{f(x) : x^TB_ix \le d_i\}$: the least upper bound of $x^TAx$ over the solutions of $(S')$.
--   3. $F^*$ is the optimal value of the standard semidefinite relaxation
--   $$(SDP)\qquad \max_X\big\{F(X) \equiv \operatorname{Tr}(AX) : \operatorname{Tr}(B_iX) \le d_i,\ i = 1,\dots,m,\ X = X^T \succeq 0\big\},$$
--   the least upper bound of $\operatorname{Tr}(AX)$ over its feasible set.
--   4. The semidefinite dual of (SDP) is
--   $$(SDD)\qquad \min_\lambda\Big\{\sum_{i=1}^m \lambda_id_i : \sum_{i=1}^m \lambda_iB_i \succeq A,\ \lambda \ge 0\Big\},$$
--   and "(SDD) is solvable with the optimal value $v$" means that some feasible $\lambda$ has $\sum_i\lambda_id_i = v$ and every feasible $\lambda$ has $\sum_i\lambda_id_i \ge v$.
--
--   These are the objects of Propositions 4.10.5 and 4.10.6.
--
--   **Formalization Note** The book's standing condition "all $d_i \ge 0$" and the symmetry of the matrices are not built into the structure; the theorems carry them as hypotheses. Optimal values are predicates (`IsLUB`, `IsLeast`), never a bare `sSup`/`sInf`. The multipliers $\lambda$ are named `lam`. $\sum_i\lambda_iB_i \succeq A$ is `Matrix.PosSemidef` of the difference, which includes its symmetry.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 313 ((SL.??), (S′), (P), (SDP)), p. 314 ((SDD))

import Mathlib

open Matrix

namespace ModernConvex.Relaxations

/-- The data of the setting (SL.??) of Ben-Tal–Nemirovski, p. 313: a system of quadratic
inequalities `(S′) : xᵀBᵢx ≤ dᵢ, i = 1, …, m` (the book assumes all `dᵢ ≥ 0`) and a homogeneous
quadratic form `f(x) = xᵀAx`, with `x ∈ ℝⁿ`. -/
structure QuadraticSystem (n m : ℕ) where
  B : Fin m → Matrix (Fin n) (Fin n) ℝ
  d : Fin m → ℝ
  A : Matrix (Fin n) (Fin n) ℝ

namespace QuadraticSystem

variable {n m : ℕ}

/-- `x` solves the system `(S′) : xᵀBᵢx ≤ dᵢ, i = 1, …, m`. -/
def Solves (S : QuadraticSystem n m) (x : Fin n → ℝ) : Prop :=
  ∀ i, x ⬝ᵥ (S.B i *ᵥ x) ≤ S.d i

/-- `(S′)` is strictly feasible: some `x` has `xᵀBᵢx < dᵢ` for every `i`. -/
def StrictlyFeasible (S : QuadraticSystem n m) : Prop :=
  ∃ x : Fin n → ℝ, ∀ i, x ⬝ᵥ (S.B i *ᵥ x) < S.d i

/-- `v` is `f∗`, the optimal value of `(P) : max_x {f(x) : xᵀBᵢx ≤ dᵢ}`: the least upper bound
of `xᵀAx` over the solution set of `(S′)`. -/
def IsPValue (S : QuadraticSystem n m) (v : ℝ) : Prop :=
  IsLUB ((fun x => x ⬝ᵥ (S.A *ᵥ x)) '' {x | S.Solves x}) v

/-- `X` is feasible for `(SDP) : max_X {F(X) ≡ Tr(AX) : Tr(BᵢX) ≤ dᵢ, i = 1, …, m, X = Xᵀ ⪰ 0}`. -/
def SDPFeasible (S : QuadraticSystem n m) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, (S.B i * X).trace ≤ S.d i) ∧ X.PosSemidef

/-- `v` is `F∗`, the optimal value of `(SDP)`: the least upper bound of `Tr(AX)` over its
feasible set. -/
def IsSDPValue (S : QuadraticSystem n m) (v : ℝ) : Prop :=
  IsLUB ((fun X => (S.A * X).trace) '' {X | S.SDPFeasible X}) v

/-- `λ ∈ ℝᵐ` is feasible for `(SDD) : min_λ {Σᵢ λᵢdᵢ : Σᵢ λᵢBᵢ ⪰ A, λ ≥ 0}`, p. 314. -/
def SDDFeasible (S : QuadraticSystem n m) (lam : Fin m → ℝ) : Prop :=
  (∑ i, lam i • S.B i - S.A).PosSemidef ∧ ∀ i, 0 ≤ lam i

/-- `(SDD)` is solvable with the optimal value `v`: `v = Σᵢ λᵢdᵢ` for some feasible `λ`, and no
feasible `λ` does better (the minimum is attained and equals `v`). -/
def SDDSolvableWithValue (S : QuadraticSystem n m) (v : ℝ) : Prop :=
  IsLeast ((fun lam => ∑ i, lam i * S.d i) '' {lam | S.SDDFeasible lam}) v

end QuadraticSystem

end ModernConvex.Relaxations


