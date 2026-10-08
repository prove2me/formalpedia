-- Prove2me | Definitions.Def_PatakiRank_Mult_Setting
-- name    : PatakiRank_Mult_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:43.585524+00:00
-- url     : https://prove2.me/theorems/c6de54e9-830f-40aa-857a-978c51b37357
-- title:
--   §1–§4, pp. 339–349 — t, τ, f_k, mult, faces and dimension, the SDPs (3.14)/(3.18)/(4.26), Theorem 2.2's feasible set, Ω_k(B), A(x), Θ, F*
-- statement:
--   This module fixes the objects of Pataki's paper on the rank of extreme matrices in semidefinite programs. Throughout, $\mathcal S^n$ is the space of real symmetric $n\times n$ matrices, $X\succeq 0$ means that $X$ is symmetric positive semidefinite, and $A\bullet B=\sum_{i,j}a_{ij}b_{ij}=\operatorname{trace}(A^TB)$.
--
--   1. **Triangular numbers and $\tau$.** $t(i)=i(i+1)/2$, and for an integer $l$ and natural numbers $r,s$
--   $$\tau(l,r,s)=\max\{\,i+j:\ i,j\in\mathbb N,\ t(i)+t(j)\le l,\ i\le r,\ j\le s\,\}.$$
--   The set is nonempty exactly when $l\ge 0$; the empty maximum is $0$ by convention, a case that never arises in the statements that use $\tau$.
--   2. **Eigenvalues.** For $B\in\mathcal S^n$, $\lambda_1(B)\ge\dots\ge\lambda_n(B)$ are its eigenvalues in nonincreasing order, $f_k(B)=\lambda_1(B)+\dots+\lambda_k(B)$, and $\operatorname{mult}(\lambda_i(B))$ is the largest $p\ge1$ such that $\lambda_j(B)=\dots=\lambda_i(B)=\dots=\lambda_{j+p-1}(B)$ for some $j\le i\le j+p-1$ (with $1\le j$ and $j+p-1\le n$).
--   3. **Faces and dimension.** A face of a set $S$ is a convex subset $F\subseteq S$ such that $x\in F$, $y,z\in S$ and $x=\tfrac12(y+z)$ imply $y,z\in F$. An extreme point of $S$ is a point $x$ for which $\{x\}$ is a face. The dimension of $S$ is $\dim S=\max\{p : v^1,\dots,v^p\in S \text{ affinely independent}\}-1$, an integer, with $\dim\emptyset=-1$.
--   4. **The SDP (3.14) and $\Omega_k(B)$.** For $B\in\mathcal S^n$ and $k$, the SDP (3.14) is $\min\{kz+I\bullet V:\ V,W\succeq0,\ zI+V-W=B\}$ over $(z,V,W)$; $\Omega_k(B)$ is its set of optimal solutions (feasible points whose objective value is no larger than that of any feasible point). The LP (3.18) is $\min\{kz+e^Tv:\ v,w\ge0,\ ze+v-w=\lambda\}$ for $\lambda\in\mathbb R^n$, and for a number $z$ we write
--   $$v^*=(\lambda_1-z,\dots,\lambda_k-z,0,\dots,0)^T,\qquad w^*=(0,\dots,0,z-\lambda_{k+1},\dots,z-\lambda_n)^T.$$
--   5. **The multi-block SDP of Theorem 2.2.** For symmetric matrices $A_{ij}$, $D_{ij}$, $B_i$ of order $n$ and scalars $a_{ij}$, $b_i$, its feasible set is the set of $(X_1,\dots,X_p,y)\in(\mathcal S^n)^p\times\mathbb R^q$ with $X_j\succeq0$, $\sum_j A_{ij}\bullet X_j=b_i$ ($i\le m_1$) and $\sum_j a_{ij}X_j+\sum_j y_jD_{ij}=B_i$ ($i\le m_2$).
--   6. **The affine eigenvalue problem.** For matrices $A_0,\dots,A_m$, $A(x)=A_0+\sum_{i=1}^m x_iA_i$; $\Theta$ is the set of optimal solutions of $(EV_k)\ \min\{f_k(A(x)):x\in\mathbb R^m\}$; the feasible set of (4.26) is the set of $(x,z,V,W)$ with $V,W\succeq0$, $zI+V-W=A(x)$; and $F^*=\{x^*\}\times\Omega_k(A(x^*))$.
--
--   These are the objects of every statement of the mission: the rank bounds of §2 are about faces of SDP feasible sets, §3 computes $\Omega_k(B)$ explicitly, and §4 bounds the multiplicity of $\lambda_k$ at extreme points of $\Theta$.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin n) ℝ`; $A\bullet B$ is the published `frob`, and $I\bullet V$ is `frob 1 V`. Eigenvalues are the published `eig`, Mathlib's nonincreasing `eigenvalues₀` (junk $0$ for a non-symmetric matrix, so every statement assumes symmetry); indices are 0-based, `eig B i` being $\lambda_{i+1}(B)$, and `mult B i` is $\operatorname{mult}(\lambda_{i+1}(B))$, defined as the supremum of the admissible run lengths $p$ (a nonempty set bounded by $n$). `convDim` is stated for finite-dimensional real vector spaces (where the set of $p$ is bounded) and is integer valued. $\Theta$ is the argmin set $\{x:\ f_k(A(x))\le f_k(A(y))\ \forall y\}$, which equals the paper's $\{x: f_k(A(x))=f_k^*\}$ without referring to an infimum. Theorem 2.2's feasible set uses one common matrix order $n$ for all $X_j$ and $B_i$.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), pp. 339–341 ((1.1)–(1.3), notation and preliminaries), p. 343 (Theorem 2.2's feasible set), pp. 345–348 ((3.14), (3.18), Ω_k(B)), pp. 348–349 ((4.26)–(4.28), Lemma 4.2's F*)

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet

open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- The triangular number `t(i) = i(i + 1)/2` (p. 341 and (4.28), p. 349). -/
def tri (i : ℕ) : ℕ := i * (i + 1) / 2

/-- `τ(l, r, s) = max {i + j : t(i) + t(j) ≤ l, i ≤ r, j ≤ s}` ((4.28), p. 349), the maximum
over natural numbers `i, j`. The maximum of an empty set (only possible when `l < 0`) is `0`. -/
def tau (l : ℤ) (r s : ℕ) : ℕ :=
  (((Finset.range (r + 1)) ×ˢ (Finset.range (s + 1))).filter
    (fun ij : ℕ × ℕ => ((tri ij.1 + tri ij.2 : ℕ) : ℤ) ≤ l)).sup (fun ij => ij.1 + ij.2)

/-- `f_k(B) = λ₁(B) + ⋯ + λ_k(B)`, the sum of the `k` largest eigenvalues ((1.3), p. 340).
`eig B i` is the paper's `λ_{i+1}(B)` (0-based index). -/
noncomputable def fk {n : ℕ} (k : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n with i.val < k, eig B i

/-- `mult(λ_{i+1}(B))` (p. 341): the maximal `p ≥ 1` such that
`λ_j(B) = ⋯ = λ_{i+1}(B) = ⋯ = λ_{j+p−1}(B)` for some run `j ≤ i+1 ≤ j + p − 1` inside
`{1, …, n}`; written with 0-based indices: a run `j, …, j + p − 1` of indices `< n` that contains
`i`, on which every eigenvalue equals `eig B i`. -/
noncomputable def mult {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℕ :=
  sSup {p : ℕ | 1 ≤ p ∧ ∃ j : ℕ, j ≤ (i : ℕ) ∧ (i : ℕ) ≤ j + p - 1 ∧ j + p ≤ n ∧
    ∀ l : ℕ, ∀ hl : l < n, j ≤ l → l < j + p → eig B ⟨l, hl⟩ = eig B i}

/-- A face of `S` (p. 341): a convex subset `F ⊆ S` such that `x ∈ F`, `y, z ∈ S`,
`x = ½(y + z)` imply `y, z ∈ F`. -/
def IsFace {E : Type*} [AddCommGroup E] [Module ℝ E] (S F : Set E) : Prop :=
  F ⊆ S ∧ Convex ℝ F ∧
    ∀ x ∈ F, ∀ y ∈ S, ∀ z ∈ S, x = (1 / 2 : ℝ) • (y + z) → y ∈ F ∧ z ∈ F

/-- An extreme point (vertex) of `S` (p. 341): a face of `S` consisting of a single element. -/
def IsExtremePt {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) (x : E) : Prop :=
  IsFace S {x}

/-- `dim S = max {p | v¹, …, vᵖ ∈ S are affinely independent} − 1` (p. 341), as an integer;
`dim ∅ = −1`. Only used on finite-dimensional spaces, where the set of such `p` is bounded. -/
noncomputable def convDim {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (S : Set E) : ℤ :=
  ((sSup {p : ℕ | ∃ v : Fin p → E, (∀ i, v i ∈ S) ∧ AffineIndependent ℝ v} : ℕ) : ℤ) - 1

/-- The feasible set of the semidefinite program of Theorem 2.2 (p. 343), with one common matrix
order `n`: `(X₁, …, X_p, y)` with `X_j ⪰ 0`, `∑_j A_ij • X_j = b_i` (`i = 1, …, m₁`) and
`∑_j a_ij X_j + ∑_j y_j D_ij = B_i` (`i = 1, …, m₂`). -/
def multiFeas {n p q m₁ m₂ : ℕ} (Ablk : Fin m₁ → Fin p → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m₁ → ℝ) (a : Fin m₂ → Fin p → ℝ) (D : Fin m₂ → Fin q → Matrix (Fin n) (Fin n) ℝ)
    (Bm : Fin m₂ → Matrix (Fin n) (Fin n) ℝ) :
    Set ((Fin p → Matrix (Fin n) (Fin n) ℝ) × (Fin q → ℝ)) :=
  {Xy | (∀ j, (Xy.1 j).PosSemidef) ∧ (∀ i, ∑ j, frob (Ablk i j) (Xy.1 j) = b i) ∧
    ∀ i, ∑ j, a i j • Xy.1 j + ∑ j, Xy.2 j • D i j = Bm i}

/-- `p` is an optimal solution of `min {obj p : feas p}`: feasible and no worse than every
feasible point. -/
def IsOptimal {α : Type*} (feas : α → Prop) (obj : α → ℝ) (p : α) : Prop :=
  feas p ∧ ∀ q, feas q → obj p ≤ obj q

/-- Feasibility in the LP (3.18) (p. 346): `v, w ≥ 0`, `z e + v − w = λ`. -/
def lpFeas {n : ℕ} (lam : Fin n → ℝ) (p : ℝ × (Fin n → ℝ) × (Fin n → ℝ)) : Prop :=
  0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ (fun _ => p.1) + p.2.1 - p.2.2 = lam

/-- The objective `k z + eᵀ v` of the LP (3.18). -/
def lpObj {n : ℕ} (k : ℕ) (p : ℝ × (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  k * p.1 + ∑ i, p.2.1 i

/-- `v* = (λ₁ − z, …, λ_k − z, 0, …, 0)ᵀ` of (3.20)/(3.25). -/
def vStar {n : ℕ} (k : ℕ) (lam : Fin n → ℝ) (z : ℝ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < k then lam i - z else 0

/-- `w* = (0, …, 0, z − λ_{k+1}, …, z − λ_n)ᵀ` of (3.20)/(3.25). -/
def wStar {n : ℕ} (k : ℕ) (lam : Fin n → ℝ) (z : ℝ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < k then 0 else z - lam i

/-- Feasibility in the SDP (3.14) (p. 345): `V, W ⪰ 0`, `z I + V − W = B`. -/
def sdpFeas {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (p : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) : Prop :=
  p.2.1.PosSemidef ∧ p.2.2.PosSemidef ∧ p.1 • (1 : Matrix (Fin n) (Fin n) ℝ) + p.2.1 - p.2.2 = B

/-- The objective `k z + I • V` of the SDP (3.14). -/
def sdpObj {n : ℕ} (k : ℕ) (p : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  k * p.1 + frob (1 : Matrix (Fin n) (Fin n) ℝ) p.2.1

/-- `Ω_k(B)`, the set of optimal solutions `(z, V, W)` of (3.14) (p. 348). -/
def Omega {n : ℕ} (k : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Set (ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  {p | IsOptimal (sdpFeas B) (sdpObj k) p}

/-- The affine matrix function `A(x) = A₀ + ∑ᵢ xᵢ Aᵢ` (§4, p. 348). -/
def Aff {n m : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A0 + ∑ i, x i • A i

/-- `Θ` (4.27): the set of optimal solutions of `(EV_k) min {f_k(A(x)) : x ∈ ℝ^m}`, written as
the argmin set `{x | f_k(A(x)) ≤ f_k(A(y)) for all y}`. -/
def Theta {n m : ℕ} (k : ℕ) (A0 : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  {x | ∀ y, fk k (Aff A0 A x) ≤ fk k (Aff A0 A y)}

/-- The feasible set of (4.26) (p. 348): `(x, z, V, W)` with `V, W ⪰ 0`, `z I + V − W = A(x)`. -/
def feas426 {n m : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Set ((Fin m → ℝ) × ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  {p | sdpFeas (Aff A0 A p.1) p.2}

/-- `F* = {x*} × Ω_k(A(x*))` (Lemma 4.2, p. 349). -/
def Fstar {n m : ℕ} (k : ℕ) (A0 : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (xs : Fin m → ℝ) :
    Set ((Fin m → ℝ) × ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  {p | p.1 = xs ∧ p.2 ∈ Omega k (Aff A0 A xs)}

end PatakiRank.Mult


