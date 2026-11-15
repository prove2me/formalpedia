-- Prove2me | Definitions.Def_AlgebraicFPT_HittingSet_Supplement_Geometry
-- name    : AlgebraicFPT_HittingSet_Supplement_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:41:32.705195+00:00
-- url     : https://prove2.me/theorems/e5ce6ea9-6066-44d3-b627-57e396f98aee
-- title:
--   Rational coordinate subspaces and their actual geometric codimension
-- statement:
--   For a vertex set $S$ in a graph with $n$ vertices, define the rational coordinate subspace and the query indicator by
--
--   $$L_S=\{z\in\mathbb Q^n: z_x=0\text{ for all }x\in S\},\qquad (\mathbf1_Q)_x=\begin{cases}1&x\in Q,\\0&x\notin Q.\end{cases}$$
--
--   For a finite family $A$ of ordered paths define its geometric locus $Z(A)=\bigcup_{P\in A}L_{V(P)}$. Thus $X_{h,s,v}=Z(\mathcal P_{h,s,v})$, and $Y_{h,s,v}=Z(R_{h,s,v})$ for a retained subfamily. The union over an empty family is empty. All points of $L_S$ range over $\mathbb Q^n$; the indicators alone have Boolean coordinates.
--
--   An actual subset $L\subseteq\mathbb Q^n$ has codimension $h$ here precisely when there is a natural number $r$ such that its geometric dimension is $r$ and $r+h=n$. Dimension is the Krull dimension of $\mathbb Q[z_1,\ldots,z_n]/I(L)$, using the published affine-geometry definition. No equality between coordinate codimension and $|S|$ is assumed in these definitions; this is part of Theorem 5.1.
--
--   This layer supplies the geometric content of bounded sufficiency, without using the base mission's complex-only geometry.
--
--   **Formalization Note** $L_S$ uses the published polynomial zero-set operation on the coordinate polynomials indexed by $S$. Krull dimension takes values in $\operatorname{WithBot}(\mathbb N\cup\{\infty\})$; the codimension predicate explicitly requires a finite dimension and the equation $r+h=n$.
-- source:
--   Liming Cai, Sixiang Zhang, STOC 2027 submission #1035 (October 2026), p.10, Section 5.1; p.11, Theorem 5.1

import Definitions.Def_AlgebraicFPT_HittingSet_Supplement_Paths
import Definitions.Def_RSCapacity_AffineGeometry

set_option autoImplicit false

namespace AlgebraicFPT.HittingSet.Supplement

/-- Section 5.1, p.10: the rational coordinate subspace L_S as an actual polynomial zero set.
Its points range over all of ℚⁿ, without a Boolean constraint. -/
def coordinateSpace {n : ℕ} (S : Finset (Fin n)) : Set (Fin n → ℚ) :=
  RSCapacity.zeroSet {f : MvPolynomial (Fin n) ℚ | ∃ x ∈ S, f = MvPolynomial.X x}

/-- Only the query points are Boolean: 1_Q, regarded as a rational point. -/
def indicator {n : ℕ} (Q : Finset (Fin n)) : Fin n → ℚ := fun x => if x ∈ Q then 1 else 0

/-- X for the full family and Y for a retained family; an empty union is empty. -/
def familyLocus {n : ℕ} (A : Finset (List (Fin n))) : Set (Fin n → ℚ) :=
  {z | ∃ P ∈ A, z ∈ coordinateSpace (support P)}

/-- Actual geometric codimension h: the Krull dimension is finite, r, with r + h = n.
No numerical codimension label or unproved coordinate-dimension identity is built in. -/
def HasCodimension {n : ℕ} (L : Set (Fin n → ℚ)) (h : ℕ) : Prop :=
  ∃ r : ℕ, RSCapacity.algDim L = ((r : ℕ∞) : WithBot ℕ∞) ∧ r + h = n

end AlgebraicFPT.HittingSet.Supplement


