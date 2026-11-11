-- Prove2me | Definitions.Def_HypercliqueRefutation_FourClique_WeightedProducts
-- name    : HypercliqueRefutation_FourClique_WeightedProducts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:36.323195+00:00
-- url     : https://prove2.me/theorems/b983fc7c-9d71-4629-a782-89e953b238b5
-- title:
--   Cancellation identity, fixed-index weighted products and rectangular operands
-- statement:
--   Let n,n_A,n_B,L be nonnegative integers. For a field K, weights w_ℓ in K and coefficients h^{(ℓ)}_{a,b} in K, the cancellation predicate is
--
--   $$\frac12\sum_{\ell\in[L]}w_\ell\big(h^{(\ell)}_{a,b}h^{(\ell)}_{a',b'}+h^{(\ell)}_{a,b'}h^{(\ell)}_{a',b}\big)=\mathbf1[a=a']\mathbf1[b=b'].$$
--
--   For each fixed ℓ, define the matrix
--
--   $$P^{(\ell)}[x,y]=\sum_{z,a,b}h^{(\ell)}_{a,b}A_a[x,z]B_b[z,y],\qquad Q=\sum_{x,y,\ell}w_\ell P^{(\ell)}[x,y]P^{(\ell)}[y,x].$$
--
--   The corrected definition holds ℓ fixed, as required by Observation 2.5. The rectangular operand formulas are
--
--   $$\widehat A[(x,\ell),(z,b)]=\sum_a h^{(\ell)}_{a,b}A_a[x,z],\qquad\widehat B[(z,b),y]=B_b[z,y].$$
--
--   The left operand depends on h and A, and has no B argument. Pair indices express the source's product dimensions without choosing a flattening order. All finite expressions other than the cancellation predicate also work over any commutative semiring.
--
--   These are formulas and a predicate only. They do not assert the existence of a cancellation family, sparsity, construction time, a costed matrix product, or an operational reduction. In particular, the rectangular definitions are not substitutes for Theorem 2.6.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026), held source.pdf SHA-256 fda90f18867fd07883366a1bc49a8afa652b8712f71402e11ccd45e6633b127a; Lemma 2.4 Eq.(2), p.4; Observation 2.5 (corrected fixed ℓ) and Theorem 2.6 operand definitions, p.5.

import Mathlib
import Definitions.Def_HypercliqueRefutation_FourClique_Contractions

set_option autoImplicit false

namespace HypercliqueRefutation.FourClique

/- Chan--Itakura--Ma--Yu, STOC 2027 submission #1431 (October 2026),
   Lemma 2.4 Eq.(2), p.4, and Observation 2.5 and Theorem 2.6, p.5.
   The cancellation identity is a predicate, not an existence axiom or an algorithm.
   The observation takes an existing family; no family is assumed for the goal. -/

def CancellationIdentity {K : Type*} [Field K] {nA nB L : ℕ}
    (h : Fin L → Fin nA → Fin nB → K) (w : Fin L → K) : Prop :=
  ∀ a a' b b',
    (1 / 2 : K) * ∑ l, w l * (h l a b * h l a' b' + h l a b' * h l a' b) =
      (if a = a' then 1 else 0) * (if b = b' then 1 else 0)

/-- The index l is fixed; only z, a and b are summed. -/
def weightedProduct {K : Type*} [CommSemiring K] {n nA nB L : ℕ}
    (h : Fin L → Fin nA → Fin nB → K)
    (A : Fin nA → Matrix (Fin n) (Fin n) K)
    (B : Fin nB → Matrix (Fin n) (Fin n) K)
    (l : Fin L) (x y : Fin n) : K :=
  ∑ z, ∑ a, ∑ b, h l a b * A a x z * B b z y

def weightedTrace {K : Type*} [CommSemiring K] {n nA nB L : ℕ}
    (h : Fin L → Fin nA → Fin nB → K) (w : Fin L → K)
    (A : Fin nA → Matrix (Fin n) (Fin n) K)
    (B : Fin nB → Matrix (Fin n) (Fin n) K) : K :=
  ∑ x, ∑ y, ∑ l, w l * weightedProduct h A B l x y * weightedProduct h A B l y x

/-- Its arguments enforce the independence of this operand from every B matrix.
    These definitions alone make no construction-time or reduction claim. -/
def leftOperand {K : Type*} [CommSemiring K] {n nA nB L : ℕ}
    (h : Fin L → Fin nA → Fin nB → K)
    (A : Fin nA → Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n × Fin L) (Fin n × Fin nB) K :=
  fun xl zb => ∑ a, h xl.2 a zb.2 * A a xl.1 zb.1

def rightOperand {K : Type*} [CommSemiring K] {n nB : ℕ}
    (B : Fin nB → Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n × Fin nB) (Fin n) K :=
  fun zb y => B zb.2 zb.1 y

end HypercliqueRefutation.FourClique


