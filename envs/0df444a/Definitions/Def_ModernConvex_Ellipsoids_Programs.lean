-- Prove2me | Definitions.Def_ModernConvex_Ellipsoids_Programs
-- name    : ModernConvex_Ellipsoids_Programs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:12.110368+00:00
-- url     : https://prove2.me/theorems/41d8821f-229d-4fe4-8225-d055a7e1eb89
-- title:
--   The block matrices Bⁱ, M[Z] and the LMI blocks of (4.9.111)–(4.9.112); the programs (SDP) of (D), (Õ), (Ĩ); the setting (SL.??)
-- statement:
--   This file fixes the matrix objects and semidefinite programs of §4.9 and of the setting (SL.??) of §4.10.5 of Ben-Tal–Nemirovski. A matrix $X$ is **positive semidefinite**, $X\succeq0$, if it is symmetric and $v^TXv\ge0$ for all $v$. $P\succeq Q$ means $P-Q\succeq0$.
--
--   1. **Three-block matrices** (p. 262). For $P\in\mathbb R^{n\times n}$, $p\in\mathbb R^n$, $R\in\mathbb R^{n\times q}$, $s\in\mathbb R$ and $Q\in\mathbb R^{q\times q}$, the $(n+1+q)\times(n+1+q)$ matrix
--   $$\begin{pmatrix} P & p & R\\ p^T & s & 0\\ R^T & 0 & Q\end{pmatrix}.$$
--   Blank entries in the displays (4.9.111)–(4.9.112) are zero blocks.
--   2. **$B^i$ and $M[Z]$** (p. 266). For $n\times n$ matrices $B_1,\dots,B_m$, $B^i$ is the $(mn)\times(mn)$ block-diagonal matrix with $m$ diagonal blocks of size $n\times n$. Every block is zero except the $i$-th, which is $B_i$. For an $n\times n$ matrix $Z$, $M[Z]$ is the $(mn)\times(mn)$ matrix of $m^2$ blocks of size $n\times n$, all equal to $Z$.
--   3. **(SDP) of (D)** (p. 267). An $(mn)\times(mn)$ matrix $X$ is feasible for $\max_X\{\operatorname{Tr}(M[Z]X) \mid \operatorname{Tr}(B^iX)\le1,\ i=1,\dots,m,\ X\succeq0\}$ if it satisfies these constraints.
--   4. **(Õ)** (p. 268). A triple $(t,Z,\lambda)$ with $t\in\mathbb R$, $Z\in\mathbb R^{n\times n}$, $\lambda\in\mathbb R^m$ is **feasible** for
--   $$\max_{t,Z,\lambda}\Big\{t \;\Big|\; t\le\operatorname{Det}^{1/n}(Z),\ \sum_{i=1}^m\lambda_iB^i\succeq M[Z],\ \lambda_i\ge0,\ Z\succeq0,\ \sum_{i=1}^m\lambda_i=1\Big\}$$
--   if it satisfies all five constraints. It is **optimal** if it is feasible and no feasible triple has a larger $t$.
--   5. **(Ĩ)** (p. 274). For $n\times n$ matrices $A_1,\dots,A_m$, a family $X_1,\dots,X_m\in\mathbb R^{n\times n}$ together with $t\in\mathbb R$ is **feasible** if (a) $t\le\big(\operatorname{Det}(\tfrac12\sum_i[X_i^TA_i+A_iX_i])\big)^{1/n}$, (b) $\sum_i[X_i^TA_i+A_iX_i]\succeq0$, and (c) $\begin{pmatrix}I_n&-X_i^T\\-X_i&I_n\end{pmatrix}\succeq0$ for every $i$. It is **optimal** if it is feasible and no feasible solution has a larger $t$.
--   6. **(SL.??)** (p. 313). The data are matrices $B_1,\dots,B_m$, reals $d_1,\dots,d_m$ and a matrix $A$, all on $\mathbb R^n$. They define the system $(S')$: $x^TB_ix\le d_i$, $i=1,\dots,m$, the form $f(x)=x^TAx$, and three problems:
--      - (P) $\max\{f(x) : x \text{ solves } (S')\}$, whose value $f^*$ is the least upper bound of $f$ over the solutions of $(S')$;
--      - (SDP) $\max_X\{\operatorname{Tr}(AX) : \operatorname{Tr}(B_iX)\le d_i,\ X=X^T\succeq0\}$, whose value $F^*$ is the least upper bound of $\operatorname{Tr}(AX)$ over its feasible set;
--      - (SDD) $\min_\lambda\{\sum_i\lambda_id_i : \sum_i\lambda_iB_i\succeq A,\ \lambda\ge0\}$.
--
--      "(SDD) is solvable with optimal value $v$" means that some feasible $\lambda$ attains $\sum_i\lambda_id_i=v$ and no feasible $\lambda$ gives less. $(S')$ is **strictly feasible** if some $x$ has $x^TB_ix<d_i$ for all $i$.
--
--   **Formalization Note** The $(mn)$ coordinates are indexed by pairs (block, position in block), `Fin m × Fin n`. The $n+1+q$ coordinates of item 1 are indexed by `(Fin n ⊕ Unit) ⊕ Fin q`. Neither choice affects positive semidefiniteness. $\succeq0$ is Mathlib's `PosSemidef`, which includes symmetry; this matches the book's $Z\in\mathbf S^n$ and $X\in\mathbf S^{mn}$. $\operatorname{Det}^{1/n}$ is the real power `Real.rpow` of the determinant, nonnegative wherever the constraints $Z\succeq0$ or (b) hold. Optimal values are encoded only through least-upper-bound and attainment predicates, never as a bare supremum. The (SL.??) objects duplicate the draft definition `ModernConvex.Relaxations.QuadraticSystem` of the series' Lecture-4 relaxations mission. A draft cannot import another mission's draft, so they are restated here.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 262 (4.9.111)–(4.9.112), p. 266 (Bⁱ, M[Z]), p. 267 (SDP), p. 268 (Õ), p. 274 (Ĩ), pp. 313–314 (SL.??), (S′), (P), (SDP), (SDD)

import Mathlib

open Matrix

namespace ModernConvex.Ellipsoids

/-- The symmetric `(n + 1 + q) × (n + 1 + q)` block matrix
```
( P   p   R
  pᵀ  s   0
  Rᵀ  0   Q )
```
with `P ∈ M^{n,n}`, `p ∈ ℝⁿ`, `R ∈ M^{n,q}`, `s ∈ ℝ`, `Q ∈ M^{q,q}` (blank entries of the book's
displays (4.9.111)–(4.9.112), p. 262, are zero blocks). Rows and columns are indexed by
`(Fin n ⊕ Unit) ⊕ Fin q`: first the `n` coordinates, then the single middle one, then the `q`. -/
def block3 {n q : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) (R : Matrix (Fin n) (Fin q) ℝ)
    (s : ℝ) (Q : Matrix (Fin q) (Fin q) ℝ) :
    Matrix ((Fin n ⊕ Unit) ⊕ Fin q) ((Fin n ⊕ Unit) ⊕ Fin q) ℝ :=
  Matrix.of fun r c =>
    match r, c with
    | .inl (.inl i), .inl (.inl j) => P i j
    | .inl (.inl i), .inl (.inr _) => p i
    | .inl (.inl i), .inr k => R i k
    | .inl (.inr _), .inl (.inl j) => p j
    | .inl (.inr _), .inl (.inr _) => s
    | .inl (.inr _), .inr _ => 0
    | .inr k, .inl (.inl j) => R j k
    | .inr _, .inl (.inr _) => 0
    | .inr k, .inr l => Q k l

/-- `Bⁱ` (p. 266): the `(mn) × (mn)` block-diagonal matrix with `m` diagonal blocks of size `n × n`,
all zero except the `i`th one, which is `Bᵢ`. Rows and columns are indexed by `Fin m × Fin n`
(block index, index within the block). -/
def blockSel {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (i : Fin m) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ :=
  Matrix.of fun r c => if r.1 = i ∧ c.1 = i then B i r.2 c.2 else 0

/-- `M[Z]` (p. 266): the `(mn) × (mn)` matrix of `m²` blocks of size `n × n`, every block equal to
`Z`. Indexed by `Fin m × Fin n` as `blockSel`. -/
def blockAll {m n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ :=
  Matrix.of fun r c => Z r.2 c.2

/-- `X` is feasible for the semidefinite program (SDP) of (D), p. 267:
`max_X { Tr(M[Z]X) | Tr(BⁱX) ≤ 1, i = 1, …, m, X ⪰ 0 }`. -/
def DFeasible {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ) : Prop :=
  (∀ i, (blockSel B i * X).trace ≤ 1) ∧ X.PosSemidef

/-- `(t, Z, λ)` is feasible for the semidefinite program (Õ) of Proposition 4.9.4, p. 268:
`t ≤ Det^{1/n}(Z)`, `Σᵢ λᵢBⁱ ⪰ M[Z]`, `λᵢ ≥ 0`, `Z ⪰ 0`, `Σᵢ λᵢ = 1`. Here `Z ⪰ 0` is Mathlib's
`PosSemidef` (symmetric and positive semidefinite, the book's `Z ∈ Sⁿ₊`) and `Det^{1/n}` is the real
power `Real.rpow` of the (nonnegative) determinant. -/
def OFeasible {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) (lam : Fin m → ℝ) : Prop :=
  t ≤ Z.det ^ ((1 : ℝ) / n) ∧
    (∑ i, lam i • blockSel B i - blockAll Z).PosSemidef ∧
    (∀ i, 0 ≤ lam i) ∧ Z.PosSemidef ∧ ∑ i, lam i = 1

/-- `(t, Z, λ)` is an optimal solution of (Õ): feasible, and no feasible solution has a larger
objective `t`. -/
def OOptimal {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) (lam : Fin m → ℝ) : Prop :=
  OFeasible B t Z lam ∧
    ∀ (t' : ℝ) (Z' : Matrix (Fin n) (Fin n) ℝ) (lam' : Fin m → ℝ), OFeasible B t' Z' lam' → t' ≤ t

/-- `({Xᵢ}, t)` is feasible for the semidefinite program (Ĩ) of Proposition 4.9.6, p. 274:
(a) `t ≤ (Det(½ Σᵢ [XᵢᵀAᵢ + AᵢXᵢ]))^{1/n}`, (b) `Σᵢ [XᵢᵀAᵢ + AᵢXᵢ] ⪰ 0`,
(c) `( Iₙ  −Xᵢᵀ ; −Xᵢ  Iₙ ) ⪰ 0`, `i = 1, …, m`, with `Xᵢ ∈ M^{n,n}`, `t ∈ ℝ`. -/
def IFeasible {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (X : Fin m → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Prop :=
  t ≤ (((1 : ℝ) / 2) • ∑ i, ((X i)ᵀ * A i + A i * X i)).det ^ ((1 : ℝ) / n) ∧
    (∑ i, ((X i)ᵀ * A i + A i * X i)).PosSemidef ∧
    ∀ i, (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-(X i)ᵀ) (-(X i)) 1).PosSemidef

/-- `({Xᵢ}, t)` is an optimal solution of (Ĩ): feasible, and no feasible solution has a larger
objective `t`. -/
def IOptimal {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (X : Fin m → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Prop :=
  IFeasible A X t ∧
    ∀ (X' : Fin m → Matrix (Fin n) (Fin n) ℝ) (t' : ℝ), IFeasible A X' t' → t' ≤ t

/-! ### The setting (SL.??) of p. 313, restated for Proposition 4.10.5 -/

/-- The data of (SL.??), p. 313: a system of quadratic inequalities
`(S′) : xᵀBᵢx ≤ dᵢ, i = 1, …, m` and a homogeneous quadratic form `f(x) = xᵀAx` on `ℝⁿ`. -/
structure QuadraticSystem (n m : ℕ) where
  B : Fin m → Matrix (Fin n) (Fin n) ℝ
  d : Fin m → ℝ
  A : Matrix (Fin n) (Fin n) ℝ

namespace QuadraticSystem

variable {n m : ℕ}

/-- `x` solves `(S′) : xᵀBᵢx ≤ dᵢ, i = 1, …, m`. -/
def Solves (S : QuadraticSystem n m) (x : Fin n → ℝ) : Prop :=
  ∀ i, x ⬝ᵥ (S.B i *ᵥ x) ≤ S.d i

/-- `(S′)` is strictly feasible: some `x` has `xᵀBᵢx < dᵢ` for every `i`. -/
def StrictlyFeasible (S : QuadraticSystem n m) : Prop :=
  ∃ x : Fin n → ℝ, ∀ i, x ⬝ᵥ (S.B i *ᵥ x) < S.d i

/-- `v` is `f∗`, the optimal value of `(P) : max_x {f(x) : xᵀBᵢx ≤ dᵢ}`: the least upper bound of
`xᵀAx` over the solution set of `(S′)`. -/
def IsPValue (S : QuadraticSystem n m) (v : ℝ) : Prop :=
  IsLUB ((fun x => x ⬝ᵥ (S.A *ᵥ x)) '' {x | S.Solves x}) v

/-- `X` is feasible for `(SDP) : max_X {Tr(AX) : Tr(BᵢX) ≤ dᵢ, i = 1, …, m, X = Xᵀ ⪰ 0}`. -/
def SDPFeasible (S : QuadraticSystem n m) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, (S.B i * X).trace ≤ S.d i) ∧ X.PosSemidef

/-- `v` is `F∗`, the optimal value of `(SDP)`: the least upper bound of `Tr(AX)` over its feasible
set. -/
def IsSDPValue (S : QuadraticSystem n m) (v : ℝ) : Prop :=
  IsLUB ((fun X => (S.A * X).trace) '' {X | S.SDPFeasible X}) v

/-- `λ ∈ ℝᵐ` is feasible for `(SDD) : min_λ {Σᵢ λᵢdᵢ : Σᵢ λᵢBᵢ ⪰ A, λ ≥ 0}`, p. 314. -/
def SDDFeasible (S : QuadraticSystem n m) (lam : Fin m → ℝ) : Prop :=
  (∑ i, lam i • S.B i - S.A).PosSemidef ∧ ∀ i, 0 ≤ lam i

/-- `(SDD)` is solvable with the optimal value `v`: `v = Σᵢ λᵢdᵢ` for some feasible `λ`, and no
feasible `λ` does better. -/
def SDDSolvableWithValue (S : QuadraticSystem n m) (v : ℝ) : Prop :=
  IsLeast ((fun lam => ∑ i, lam i * S.d i) '' {lam | S.SDDFeasible lam}) v

end QuadraticSystem

end ModernConvex.Ellipsoids


