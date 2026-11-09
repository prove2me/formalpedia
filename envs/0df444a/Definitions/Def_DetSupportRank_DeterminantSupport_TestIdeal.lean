-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_TestIdeal
-- name    : DetSupportRank_DeterminantSupport_TestIdeal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:59.824228+00:00
-- url     : https://prove2.me/theorems/76dbb3c3-3c29-43cf-b39a-91162d6360ac
-- title:
--   Integer test polynomials and elementary symmetric zero sets
-- statement:
--   Write $z$ and $\alpha$ for two independent $n$-tuples of variables. The integer test objects are
--   $$q_{a,b}(z)=\sum_i(z^{b_i}-z^{a_i}),\qquad J=\bigcap_{\sigma\in S_n}(1-\alpha_jz_{\sigma(j)}:j\in[n]).$$
--   The notation $q\le J$ means that one integer polynomial $Q\in J$ satisfies $Q(z,1)=q(z)$. Also define $e_k(y)=\sum_{|S|=k}\prod_{i\in S}y_i$, $E_r=\{y:e_1(y)=\cdots=e_r(y)=0\}$, and the finite coefficient test $\sum_v[z^v]q\,(v\cdot y)^r$.
--
--   The integer coefficient domain is independent of the field of the original polynomial. A common lift in the intersection is required; separate lifts for different permutations do not suffice.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §5.1, p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DegreeVarieties

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport

/-- The integer test polynomial of §5.1, target shifts minus source shifts. -/
def relationTest {n N : ℕ} (a b : Fin N → Fin n → ℕ) : MvPolynomial (Fin n) ℤ :=
  ∑ i, (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (b i)) (1 : ℤ) -
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (a i)) (1 : ℤ))

/-- Left variables are z, right variables are α, in the single ambient integer ring. -/
def permutationIdeal {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Ideal (MvPolynomial (Fin n ⊕ Fin n) ℤ) :=
  Ideal.span (Set.range fun j => (1 : MvPolynomial (Fin n ⊕ Fin n) ℤ) -
    MvPolynomial.X (Sum.inr j) * MvPolynomial.X (Sum.inl (σ j)))

def testIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n ⊕ Fin n) ℤ) :=
  ⨅ σ : Equiv.Perm (Fin n), permutationIdeal σ

/-- q ≤ J means a single common lift Q in J, specializing every α to 1. -/
def HasTestLift {n : ℕ} (q : MvPolynomial (Fin n) ℤ) : Prop :=
  ∃ Q : MvPolynomial (Fin n ⊕ Fin n) ℤ, Q ∈ testIdeal n ∧
    MvPolynomial.eval₂ MvPolynomial.C (Sum.elim MvPolynomial.X (fun _ => 1)) Q = q

/-- Genuine elementary symmetric evaluation, including the usual e₀ = 1 convention. -/
def elementarySymmetricValue {n : ℕ} (k : ℕ) (y : Fin n → ℂ) : ℂ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ S, y i

def elementaryZeroSet (n r : ℕ) : Set (Fin n → ℂ) :=
  {y | ∀ k : ℕ, 1 ≤ k → k ≤ r → elementarySymmetricValue k y = 0}

/-- A finite-support integer test evaluated on r-th powers of bilinear degree forms. -/
def powerTest {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (r : ℕ) (y : Fin n → ℂ) : ℂ :=
  ∑ e ∈ q.support, ((q.coeff e : ℤ) : ℂ) * (∑ i, (e i : ℂ) * y i) ^ r

end DetSupportRank.DeterminantSupport


