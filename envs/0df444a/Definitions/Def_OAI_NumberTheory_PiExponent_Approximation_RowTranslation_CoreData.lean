-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
-- name    : OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-11T14:31:22.413162+00:00
-- url     : https://prove2.me/theorems/73744b41-5d27-45ae-a5c7-6230fc07a4dc
-- title:
--   Polynomial translation and finite multi-index data
-- statement:
--   Let $R$ be a commutative semiring and $\sigma$ an index type. For $c:\sigma\to R$, define the polynomial translation homomorphism and its monomial coefficient by
--
--   $$\tau_c(X_i)=X_i+c_i,\qquad S_c(\beta,a)=[X^\beta]\tau_c(X^a).$$
--
--   Here $a,\beta:\sigma\to_0\mathbb N$ are finitely supported exponent vectors. When $\sigma$ is finite, the finite multi-index map converts $a:\sigma\to\mathbb N$ to the same vector viewed as a finitely supported function. These are the original data used to expand shifted interpolation polynomials.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/RowTranslation.lean#L13-L68

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

namespace OAI

namespace PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial

section PolynomialShift
variable {σ R : Type*} [CommSemiring R]

noncomputable def shift (c : σ → R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => X i + C (c i))

noncomputable def shiftCoefficient (c : σ → R) (β a : σ →₀ ℕ) : R :=
  (shift c (monomial a 1)).coeff β

end PolynomialShift

section FiniteExpansion
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

noncomputable def multiIndex (a : σ → ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm a

end FiniteExpansion

end PiExponent.RowTranslation

end OAI


