-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
-- name    : OAI_Algebra_AffineCancellation_PositiveInvariant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:35:06.718857+00:00
-- url     : https://prove2.me/theorems/a764ab73-74cd-458e-a83b-7b50b781f389
-- title:
--   Transporting a derivation along an algebra isomorphism
-- statement:
--   Let $k$ be a field, let $R$ and $S$ be commutative $k$-algebras, let $e:R\to S$ be an isomorphism of $k$-algebras, and let $D$ be a $k$-derivation of $S$. The conjugate of $D$ by $e$ is the map
--   $$D^{e}=e^{-1}\circ D\circ e:R\to R,\qquad D^{e}(r)=e^{-1}\bigl(D(e(r))\bigr),$$
--   and it is a $k$-derivation of $R$: it is $k$-linear, and the Leibniz rule
--   $$D^{e}(rs)=r\,D^{e}(s)+s\,D^{e}(r)\qquad(r,s\in R)$$
--   follows from the Leibniz rule for $D$ because $e$ and $e^{-1}$ are multiplicative.
--
--   Since $(D^{e})^{n}=e^{-1}\circ D^{n}\circ e$, conjugation preserves local nilpotence. In the cancellation argument this is applied to a hypothetical isomorphism between the main algebra and the polynomial ring $\mathbb{C}[X_1,X_2,X_3,X_4]$: a partial derivative $\partial/\partial X_j$ transported back gives a nonzero locally nilpotent derivation of the main algebra that kills the preimage of every other coordinate $X_i$, which is the starting point for producing a homogeneous invariant of positive degree.
--
--   **Formalization Note** The definition is `LND.conjugate e D`, built with `Derivation.mk'` from the linear map `e.symm ∘ₗ D ∘ₗ e`; the section variables require `k` to be a field. The file also opens the namespace `ComplexCancellation.Rees` without adding declarations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/PositiveInvariant.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/PositiveInvariant.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.LND
variable {k R S : Type*} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
def conjugate (e : R ≃ₐ[k] S) (D : Derivation k S S) : Derivation k R R :=
  Derivation.mk' (e.symm.toLinearMap ∘ₗ D.toLinearMap ∘ₗ e.toLinearMap) (by
    intro r s
    change e.symm (D (e (r*s))) = r*e.symm (D (e s))+s*e.symm (D (e r))
    simp only [map_mul,Derivation.leibniz,smul_eq_mul,map_add,AlgEquiv.symm_apply_apply])
end ComplexCancellation.LND

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
end ComplexCancellation.Rees

end

end OAI


