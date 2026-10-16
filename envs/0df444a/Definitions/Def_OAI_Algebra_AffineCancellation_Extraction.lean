-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
-- name    : OAI_Algebra_AffineCancellation_Extraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:09:37.530718+00:00
-- url     : https://prove2.me/theorems/4210c5fb-ea7a-4a0d-8432-d3851818cf77
-- title:
--   Euler-type derivation on $R[\tau,V]/(\tau^2V-v)$ induced by a derivation $H$ with $H(v)=2v$
-- statement:
--   Let $k$ be a field, $R$ a commutative $k$-algebra and $v\in R$. Let $T_v=R[X_0,X_1]/(X_0^2X_1-v)$ with quotient map $\pi$, $\tau=\pi(X_0)$ and $V=\pi(X_1)$, and let $\iota_v\colon R\to T_v$ be the structure map, viewed as a $k$-algebra homomorphism.
--
--   1. **On the polynomial ring.** For a $k$-derivation $H$ of $R$, let $\hat H$ be the $k$-derivation of $R[X_0,X_1]$ that acts as $H$ on the coefficients and satisfies $\hat H(X_0)=0$ and $\hat H(X_1)=2X_1$. If $H(v)=2v$, then
--   $$\hat H\bigl(X_0^2X_1-v\bigr)=2\,\bigl(X_0^2X_1-v\bigr).$$
--   2. **On the modification.** Hence, if $H(v)=2v$, the derivation $\hat H$ maps the ideal $(X_0^2X_1-v)$ into itself and induces a $k$-derivation $E_H$ of $T_v$ with $E_H(\pi(q))=\pi(\hat H(q))$ for all $q\in R[X_0,X_1]$. It satisfies
--   $$E_H(\iota_v(r))=\iota_v(H(r))\quad(r\in R),\qquad E_H(\tau)=0,\qquad E_H(V)=2V.$$
--
--   If $H$ is the Euler derivation of a grading of $R$ in which $v$ is homogeneous of degree $2$, then $E_H$ extends it to $T_v$ consistently with the relation $\tau^2V=v$, giving $\tau$ weight $0$ and $V$ weight $2$. Derivations of $T_v$ that commute with $E_H$ can then be compared with derivations of $R$ that are homogeneous with respect to $H$.
--
--   **Formalization Note** `coefficientHom v` is the map $\iota_v$; `eulerPoly H` is `PolynomialDerivation.mv H ![0, 2*X 1]` and item 1 is `eulerPoly_relation`; `euler v H hH` is built with `QuotientDerivation.derivation` and `span_singleton_stable`, with computation rules `euler_π`, `euler_coefficient`, `euler_τ` and `euler_V`. The section also declares that `k` has characteristic zero and that `R` is a domain, but none of these definitions and lemmas uses those hypotheses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Extraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Extraction.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
variable (v : R) (hv : v ≠ 0)
def coefficientHom : R →ₐ[k] T R v := IsScalarTower.toAlgHom k R (T R v)
def eulerPoly (H : Derivation k R R) : Derivation k (P R) (P R) :=
  PolynomialDerivation.mv H ![0,2*X 1]
omit [CharZero k] [IsDomain R] in
lemma eulerPoly_relation (H : Derivation k R R) (hH : H v=2*v) :
    eulerPoly H (rel R v)=2*rel R v := by
  simp only [rel,eulerPoly,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
    PolynomialDerivation.mv_X,PolynomialDerivation.mv_C,hH,map_mul,map_ofNat,
    Matrix.cons_val_zero,Matrix.cons_val_one,smul_eq_mul]
  ring

def euler (H : Derivation k R R) (hH : H v=2*v) : Derivation k (T R v) (T R v) :=
  QuotientDerivation.derivation _ (eulerPoly H)
    (QuotientDerivation.span_singleton_stable _ (by
      rw [eulerPoly_relation v H hH]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
omit [CharZero k] [IsDomain R] in
@[simp] lemma euler_π (H : Derivation k R R) (hH : H v=2*v) (p : P R) :
    euler v H hH (π R v p)=π R v (eulerPoly H p) := rfl
omit [CharZero k] [IsDomain R] in
@[simp] lemma euler_coefficient (H : Derivation k R R) (hH : H v=2*v) (r : R) :
    euler v H hH (coefficientHom (k := k) v r)=coefficientHom (k := k) v (H r) := by
  change euler v H hH (π R v (C r))=π R v (C (H r))
  rw [euler_π]
  simp [eulerPoly]
omit [CharZero k] [IsDomain R] in
@[simp] lemma euler_τ (H : Derivation k R R) (hH : H v=2*v) : euler v H hH (τ R v)=0 := by
  simp [τ,eulerPoly]
omit [CharZero k] [IsDomain R] in
@[simp] lemma euler_V (H : Derivation k R R) (hH : H v=2*v) : euler v H hH (V R v)=2*V R v := by
  simp only [V,euler_π,eulerPoly,PolynomialDerivation.mv_X,Matrix.cons_val_one,Matrix.cons_val_zero,map_mul,map_ofNat]
end ComplexCancellation.AffineModification

end

end OAI


