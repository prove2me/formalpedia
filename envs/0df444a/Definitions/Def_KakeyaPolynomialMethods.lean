-- Prove2me | Definitions.Def_KakeyaPolynomialMethods
-- name    : KakeyaPolynomialMethods
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-23T06:26:03.449149+00:00
-- url     : https://prove2.me/theorems/431c4acb-88be-4be5-836a-5d79f24e8810
-- title:
--   Hasse derivatives and polynomial restriction to affine lines
-- statement:
--   For polynomials over a commutative semiring, this interface defines multivariate Hasse derivatives by their coefficients, without division by factorials. If $i$ is the derivative multi-index, the coefficient at $b$ of $H_iP$ is the coefficient of $P$ at $b+i$ multiplied by the product of the binomial coefficients $\binom{b_j+i_j}{i_j}$. It also defines multi-index total order and the algebra homomorphism restricting a polynomial to the affine line $t\mapsto a+tb$. These operations provide the statement interface for the mixed-jet polynomial detection lemma used in the sharp finite-field Kakeya proof. They are valid in positive characteristic.
-- source:
--   Bukh and Chao, Sharp density bounds on the finite field Kakeya problem, arXiv:2108.00074v2, Discrete Analysis 2021:26, pp. 3–4, Definition 4 (Hasse derivatives) and Definition 8 (vanishing along a line). Coefficient formula is the binomial expansion of P(X+Y); affine line restriction is polynomial substitution. Necessary interface for Lemma 9 and public target448b0e69-57fd-4028-ab8b-07964b7b3c5b.

import Mathlib

/-! Multivariate Hasse derivatives, valid in arbitrary characteristic. -/

open scoped BigOperators
open MvPolynomial

namespace KakeyaHasse

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

/-- The multi-index binomial coefficient, interpreted in the coefficient semiring. -/
noncomputable def multiChoose (a i : σ →₀ ℕ) : R :=
  ∏ j : σ, (Nat.choose (a j) (i j) : R)

/-- The Hasse derivative. Its coefficients are defined directly, without factorial division. -/
noncomputable def hasse (i : σ →₀ ℕ) (P : MvPolynomial σ R) : MvPolynomial σ R := by
  classical
  exact AddMonoidAlgebra.ofCoeff (Finsupp.onFinset
    (P.support.image fun a => a - i)
    (fun b => multiChoose (b + i) i * P.coeff (b + i)) (by
      intro b hb
      have hc : P.coeff (b + i) ≠ 0 := by
        intro hc
        simp only [hc, mul_zero] at hb
        exact hb rfl
      exact Finset.mem_image.mpr ⟨b + i, mem_support_iff.mpr hc, by simp⟩))

/-- The total order of a multi-index. -/
def order (i : σ →₀ ℕ) : ℕ := i.sum fun _ e => e

end KakeyaHasse

namespace KakeyaPolynomialMethods

/-- Restriction of a multivariate polynomial to the affine line `t ↦ a + t • b`. -/
noncomputable def lineMap {σ F : Type*} [CommSemiring F] (a b : σ → F) :
    MvPolynomial σ F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval (fun j => Polynomial.C (a j) + Polynomial.X * Polynomial.C (b j))

end KakeyaPolynomialMethods


