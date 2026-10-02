-- Prove2me | Definitions.Def_tegmark_pde_classification
-- name    : tegmark_pde_classification
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T01:44:26.728983+00:00
-- url     : https://prove2.me/theorems/479c4ebb-1676-49b9-a77b-08848f7fa487
-- title:
--   PDE type (elliptic / hyperbolic / ultrahyperbolic) via eigenvalue signs
-- statement:
--   Let $A$ be a real $d\times d$ matrix. Write $N_+(A)$ and $N_-(A)$ for the number of positive and the number of negative real roots of the characteristic polynomial $\det(X I-A)$, each counted with multiplicity. For symmetric $A$ these are the numbers of positive and of negative eigenvalues.
--
--   The second-order linear PDE
--   $$\sum_{i,j=1}^d A_{ij}\,\partial_i\partial_j u+\sum_{i=1}^d b_i\,\partial_i u+c\,u=0$$
--   with symmetric coefficient matrix $A$ is called
--
--   1. **elliptic** if $A$ is symmetric and $N_+(A)=d$ or $N_-(A)=d$ (all eigenvalues positive or all negative);
--   2. **hyperbolic** if $A$ is symmetric and either $N_+(A)=1,\ N_-(A)=d-1$ or $N_-(A)=1,\ N_+(A)=d-1$ (one eigenvalue of one sign, the rest of the other);
--   3. **ultrahyperbolic** if $A$ is symmetric, $N_+(A)\ge2$ and $N_-(A)\ge2$.
--
--   The paper uses this classification to sort spacetime dimensionalities $(n,m)$ by the causal structure of their field equations.
--
--   **Formalization Note** The type depends only on the constant matrix $A$, i.e. the classification is taken at a single point. A symmetric matrix with a zero eigenvalue is never elliptic or hyperbolic, but it is ultrahyperbolic as soon as it has at least two positive and two negative eigenvalues (the paper's 'remaining case'). For $d=1$ a nonzero matrix is both elliptic and hyperbolic, exactly as the paper's wording permits. $d-1$ is natural-number subtraction.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L72–L73, classification of the PDE (1)

import Mathlib

namespace TegmarkDimensionality

/-- The number of positive eigenvalues of a real square matrix `A`, counted with
multiplicity: the number of positive real roots of the characteristic polynomial of `A`,
counted with multiplicity. -/
noncomputable def numPosEigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℕ :=
  Multiset.card (A.charpoly.roots.filter (fun x : ℝ => 0 < x))

/-- The number of negative eigenvalues of a real square matrix `A`, counted with
multiplicity: the number of negative real roots of the characteristic polynomial of `A`,
counted with multiplicity. -/
noncomputable def numNegEigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℕ :=
  Multiset.card (A.charpoly.roots.filter (fun x : ℝ => x < 0))

/-- A second-order linear PDE `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ u + ∑ᵢ bᵢ ∂ᵢ u + c u = 0` with symmetric
coefficient matrix `A` (at a point) is *elliptic* if all eigenvalues of `A` are positive
or all are negative. -/
def IsElliptic {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : Prop :=
  A.IsSymm ∧ (numPosEigenvalues A = Fintype.card ι ∨ numNegEigenvalues A = Fintype.card ι)

/-- The PDE is *hyperbolic* if one eigenvalue of `A` is positive and the rest are
negative, or vice versa. -/
def IsHyperbolic {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : Prop :=
  A.IsSymm ∧
    ((numPosEigenvalues A = 1 ∧ numNegEigenvalues A = Fintype.card ι - 1) ∨
      (numNegEigenvalues A = 1 ∧ numPosEigenvalues A = Fintype.card ι - 1))

/-- The PDE is *ultrahyperbolic* if at least two eigenvalues of `A` are positive and at
least two are negative. -/
def IsUltrahyperbolic {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : Prop :=
  A.IsSymm ∧ 2 ≤ numPosEigenvalues A ∧ 2 ≤ numNegEigenvalues A

end TegmarkDimensionality


