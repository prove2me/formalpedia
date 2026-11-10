-- Prove2me | Definitions.Def_AlgebraicFPT_HittingSet_Geometry
-- name    : AlgebraicFPT_HittingSet_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:56:15.049303+00:00
-- url     : https://prove2.me/theorems/f61c8577-e7c5-436c-ba05-5f8705c2625d
-- title:
--   Zariski components and genuine Krull codimension
-- statement:
--   Let $X\subseteq\mathbb C^n$. Its algebraic closure has vanishing ideal $I(X)\subseteq\mathbb C[z_1,\ldots,z_n]$. Define its Zariski component collection by
--   $$\operatorname{Irr}(X)=\{\mathcal V(\mathfrak p):\mathfrak p\text{ is a minimal prime of }I(X)\}.$$
--   For algebraic $X$ this is precisely its whole collection of nonempty irreducible components in the Zariski topology. No Euclidean topology is used. A component has codimension $c\in\mathbb N$ when there is a finite $s\in\mathbb N$ with $\dim Z=s$ and $s+c=n$, where dimension is the Krull dimension of $\mathbb C[z]/I(Z)$. The collection $\mathcal X_{\le k}(X)$ contains exactly the components with such a codimension $c\le k$.
--
--   The dimension and degree primitives are reused from the published affine geometry definition. This interface exposes codimension without truncating natural subtraction or converting infinite dimensions to zero. Empty sets have no codimension witness; the empty algebraic set has no components. No finiteness or degree inequality is assumed.
-- source:
--   Liming Cai, Sixiang Zhang, STOC 2027 submission #1035 (October 2026), pp.3–5, §2.2, §3 and Lemma 3.1; minimal-prime representation of Zariski components

import Definitions.Def_RSCapacity_AffineGeometry

set_option autoImplicit false

namespace AlgebraicFPT.HittingSet

/-- All Zariski irreducible components of the algebraic closure of X, represented
as zero loci of all minimal primes of its vanishing ideal. For the algebraic sets
in the statements this is exactly the component collection of X, including the
empty collection when X is empty. The topology is Zariski, not complex Euclidean. -/
def components {n : ℕ} (X : Set (Fin n → ℂ)) : Set (Set (Fin n → ℂ)) :=
  {Z | ∃ p ∈ (MvPolynomial.vanishingIdeal ℂ X).minimalPrimes,
    Z = RSCapacity.zeroSet (p : Set (MvPolynomial (Fin n) ℂ))}

/-- Codimension c means genuine finite Krull dimension s and s+c=n.
No subtraction, dimension truncation, or infinity-to-zero conversion occurs.
It is false on the empty set and on a set with infinite Krull dimension. -/
def HasCodim {n : ℕ} (Z : Set (Fin n → ℂ)) (c : ℕ) : Prop :=
  ∃ s : ℕ, RSCapacity.algDim Z = ((s : ℕ∞) : WithBot ℕ∞) ∧ s + c = n

/-- Every component of codimension at most k, without a finiteness assumption. -/
def lowComponents {n : ℕ} (X : Set (Fin n → ℂ)) (k : ℕ) :
    Set (Set (Fin n → ℂ)) :=
  {Z | Z ∈ components X ∧ ∃ c : ℕ, c ≤ k ∧ HasCodim Z c}

end AlgebraicFPT.HittingSet


