-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_LaurentEuler
-- name    : OAI_Algebra_AffineCancellation_LaurentEuler
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:36:30.107997+00:00
-- url     : https://prove2.me/theorems/8b086b12-39d6-49b4-92da-0dd3f8ec12f1
-- title:
--   The Euler derivation $T\,\frac{d}{dT}$ on Laurent polynomials
-- statement:
--   Let $k$ and $R$ be commutative rings with $R$ a $k$-algebra, and let $R[T,T^{-1}]$ be the ring of Laurent polynomials over $R$.
--
--   1. **The Euler operator.** The $k$-linear map $\mathcal{E}:R[T,T^{-1}]\to R[T,T^{-1}]$ that multiplies the coefficient of $T^n$ by the integer $n$:
--   $$\mathcal{E}\Bigl(\sum_{n\in\mathbb{Z}}r_nT^n\Bigr)=\sum_{n\in\mathbb{Z}}n\,r_nT^n .$$
--   2. **Leibniz rule.** $\mathcal{E}(fg)=f\,\mathcal{E}(g)+g\,\mathcal{E}(f)$ for all Laurent polynomials $f,g$, so $\mathcal{E}$ is a $k$-derivation of $R[T,T^{-1}]$: it is the derivation $T\,\frac{d}{dT}$.
--   3. **Values.** $\mathcal{E}(rT^n)=n\,rT^n$ for $r\in R$ and $n\in\mathbb{Z}$; in particular $\mathcal{E}(r)=0$ for constants $r\in R$ and $\mathcal{E}(T^n)=nT^n$.
--
--   The Euler derivation is the infinitesimal form of the $\mathbb{Z}$-grading of $R[T,T^{-1}]$ by powers of $T$: elements homogeneous of degree $n$ are eigenvectors of $\mathcal{E}$ with eigenvalue $n$. In the construction it is compared, through the forward map attached to a frame, with the Euler derivation of the fiber grading on the affine modification $B$.
--
--   **Formalization Note** `linear` is defined with `Finsupp.lsum` as $n$ times `AddMonoidAlgebra.lsingle n` on each coefficient, `linear_single` and `linear_mul` are the formula on monomials and the Leibniz rule, `derivation` packages them with `Derivation.mk'`, and `monomial`, `coefficient`, `T_apply` are the values of item 3. Multiplication by $n$ is the $\mathbb{Z}$-action `n •`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/LaurentEuler.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/LaurentEuler.lean by skeleton subtraction
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
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorInverse
import Definitions.Def_OAI_Algebra_AffineCancellation_ReplicaLift

namespace OAI

noncomputable section

namespace ComplexCancellation.LaurentEuler
open LaurentPolynomial
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
def linear : LaurentPolynomial R →ₗ[k] LaurentPolynomial R :=
  (Finsupp.lsum k (fun n : ℤ => n • (AddMonoidAlgebra.lsingle n : R →ₗ[k] LaurentPolynomial R))) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap
lemma linear_single (n : ℤ) (r : R) : linear (k := k) (C r*T n)=n • (C r*T n) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.lsum k _ (Finsupp.single n r)=_
  rw [Finsupp.lsum_single]
  rfl
lemma linear_mul (r s : LaurentPolynomial R) :
    linear (k := k) (r*s)=r*linear (k := k) s+s*linear (k := k) r := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => simp only [add_mul,map_add,hr,hs]; ring
  | C_mul_T n a =>
    induction s using LaurentPolynomial.induction_on' with
    | add r s hr hs => simp only [mul_add,map_add,hr,hs]; ring
    | C_mul_T m b =>
      have he : C a*T n*(C b*T m)=C (a*b)*T (n+m) := by rw [map_mul,T_add]; ring
      rw [he,linear_single,linear_single,linear_single,← he,add_zsmul]
      simp only [mul_smul_comm]
      rw [mul_comm (C b*T m),add_comm]
def derivation : Derivation k (LaurentPolynomial R) (LaurentPolynomial R) :=
  Derivation.mk' linear (by intro r s; exact linear_mul r s)
@[simp] lemma monomial (n : ℤ) (r : R) : derivation (k := k) (C r*T n)=n • (C r*T n) := linear_single n r
@[simp] lemma coefficient (r : R) : derivation (k := k) (C r)=0 := by simpa using monomial (k := k) 0 r
@[simp] lemma T_apply (n : ℤ) : derivation (k := k) (T n : LaurentPolynomial R)=n • T n := by simpa using monomial (k := k) n (1 : R)
end ComplexCancellation.LaurentEuler

namespace ComplexCancellation.LaurentEuler
open LaurentPolynomial
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
end ComplexCancellation.LaurentEuler

end

end OAI


