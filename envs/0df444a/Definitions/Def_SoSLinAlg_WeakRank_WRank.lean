-- Prove2me | Definitions.Def_SoSLinAlg_WeakRank_WRank
-- name    : SoSLinAlg_WeakRank_WRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:29:53.800504+00:00
-- url     : https://prove2.me/theorems/c7286b2e-5a26-4f9e-b941-28f07226511d
-- title:
--   Weak Rank polynomial system
-- statement:
--   For nonnegative integers $n,r$, let $X$ and $Y$ be two independent $n\times r$ matrices of real indeterminates. Write $\mathcal P_{n,r}=\mathbb R[X,Y]$ and let $A$ be a real $n\times n$ matrix. The family $\operatorname{WRank}_r^n(A)$ consists of the $n^2$ polynomials
--   $$p_{ij}=\sum_{k=1}^r X_{ik}Y_{jk}-A_{ij}=(XY^\top)_{ij}-A_{ij}.$$
--   Setting the family equal to zero expresses the factorization $XY^\top=A$. The definition does not assert feasibility or infeasibility. In the mission's theorems $n>r\ge1$ and $\operatorname{rank}A\ge r+1$.
--
--   The module supplies the two disjoint variable types, their coordinate polynomials, and the entries of $XY^\top$. It uses zero-based finite indices. No Boolean axioms or norm constraints accompany these equations.
-- source:
--   Dmitriy Kunisky, Xifan Yu, The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission #1181 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf, Definition 1.3, PDF p.5 (printed p.3); standing conventions PDF p.4 (printed p.2)

import Mathlib

noncomputable section

namespace SoSLinAlg.WeakRank

/-- Entries of X and Y, in disjoint summands; Definition 1.3, PDF p.5. -/
abbrev Var (n r : ℕ) := (Fin n × Fin r) ⊕ (Fin n × Fin r)
abbrev Poly (n r : ℕ) := MvPolynomial (Var n r) ℝ

def x {n r : ℕ} (i : Fin n) (k : Fin r) : Poly n r :=
  MvPolynomial.X (Sum.inl (i, k))

def y {n r : ℕ} (j : Fin n) (k : Fin r) : Poly n r :=
  MvPolynomial.X (Sum.inr (j, k))

/-- The (i,j) entry of XYᵀ. -/
def xy {n r : ℕ} (i j : Fin n) : Poly n r :=
  ∑ k : Fin r, x i k * y j k

/-- Definition 1.3: the n² equations XYᵀ - A = 0, with no Boolean axioms. -/
def WRank {n : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n × Fin n) → Poly n r :=
  fun ij => xy ij.1 ij.2 - MvPolynomial.C (A ij.1 ij.2)

end SoSLinAlg.WeakRank
end


