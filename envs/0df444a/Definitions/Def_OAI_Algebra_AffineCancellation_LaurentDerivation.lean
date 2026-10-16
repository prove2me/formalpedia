-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
-- name    : OAI_Algebra_AffineCancellation_LaurentDerivation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:57:03.307956+00:00
-- url     : https://prove2.me/theorems/1ef68a1c-d312-471f-b742-6048d23d90d2
-- title:
--   Coefficientwise extension of a derivation to Laurent polynomials $R[T,T^{-1}]$
-- statement:
--   Let $k$ be a commutative ring, $R$ a commutative $k$-algebra, $D$ a $k$-linear derivation of $R$, and $R[T,T^{-1}]$ the ring of Laurent polynomials in one variable $T$ with coefficients in $R$.
--
--   1. **Coefficientwise map.** $\tilde D$ is the $k$-linear endomorphism of $R[T,T^{-1}]$ that applies $D$ to every coefficient:
--   $$\tilde D\Bigl(\sum_{n\in\mathbb{Z}}r_nT^n\Bigr)=\sum_{n\in\mathbb{Z}}D(r_n)\,T^n .$$
--   On monomials $\tilde D(rT^n)=D(r)\,T^n$, and $\tilde D$ satisfies the Leibniz rule $\tilde D(gh)=g\,\tilde D(h)+h\,\tilde D(g)$.
--
--   2. **Extension derivation.** $\tilde D$ is therefore a $k$-linear derivation of $R[T,T^{-1}]$. It extends $D$, since $\tilde D(r)=D(r)$ for constants $r\in R$, and it kills every power of the variable: $\tilde D(T^n)=0$ for all $n\in\mathbb{Z}$.
--
--   This is the standard way to extend a derivation to a Laurent polynomial ring while treating $T$ as a constant. It is the basic tool for extending derivations to Laurent extensions, as needed in Rees-algebra degeneration arguments. A separate result shows that $\tilde D$ is locally nilpotent whenever $D$ is.
--
--   **Formalization Note** `linear D` is assembled from the coefficient equivalence `AddMonoidAlgebra.coeffLinearEquiv` and `Finsupp.mapRange.linearMap D`, and `extension D` is obtained with `Derivation.mk'`. The simp lemmas `extension_monomial`, `extension_C` and `extension_T` record the values on $rT^n$, $r$ and $T^n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/LaurentDerivation.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/LaurentDerivation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order

namespace OAI

noncomputable section

namespace ComplexCancellation.LaurentDerivation
open LaurentPolynomial
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
def linear (D : Derivation k R R) : LaurentPolynomial R →ₗ[k] LaurentPolynomial R :=
  (AddMonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap D.toLinearMap ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap
@[simp] lemma linear_single (D : Derivation k R R) (n : ℤ) (r : R) :
    linear D (C r*T n)=C (D r)*T n := by
  rw [← single_eq_C_mul_T,← single_eq_C_mul_T]
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapRange D (map_zero D) (Finsupp.single n r)=Finsupp.single n (D r)
  exact Finsupp.mapRange_single
lemma linear_mul (D : Derivation k R R) (r s : LaurentPolynomial R) :
    linear D (r*s)=r*linear D s+s*linear D r := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => simp only [add_mul,map_add,hr,hs]; ring
  | C_mul_T n a =>
    induction s using LaurentPolynomial.induction_on' with
    | add r s hr hs => simp only [mul_add,map_add,hr,hs]; ring
    | C_mul_T m b =>
      have he : C a*T n*(C b*T m)=C (a*b)*T (n+m) := by rw [map_mul,T_add]; ring
      rw [he,linear_single,linear_single,linear_single,Derivation.leibniz,
        map_add,smul_eq_mul,smul_eq_mul,map_mul,map_mul,T_add]
      ring

def extension (D : Derivation k R R) : Derivation k (LaurentPolynomial R) (LaurentPolynomial R) :=
  Derivation.mk' (linear D) (by intro r s; exact linear_mul D r s)
@[simp] lemma extension_monomial (D : Derivation k R R) (n : ℤ) (r : R) :
    extension D (C r*T n)=C (D r)*T n := linear_single D n r
@[simp] lemma extension_C (D : Derivation k R R) (r : R) : extension D (C r)=C (D r) := by
  simpa using extension_monomial D 0 r
@[simp] lemma extension_T (D : Derivation k R R) (n : ℤ) : extension D (T n)=0 := by
  simpa using extension_monomial D n 1
end ComplexCancellation.LaurentDerivation

end

end OAI


