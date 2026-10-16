-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
-- name    : OAI_Algebra_AffineCancellation_Dimension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:51:12.667326+00:00
-- url     : https://prove2.me/theorems/859c907a-41c4-4ef8-abfe-04d947edaec6
-- title:
--   The hypersurface ring $A=\mathbb{C}[p,s,u,F,J]/(H)$ is a Noetherian integral domain
-- statement:
--   Let $P=\mathbb{C}[p,s,u,F,J]$ be the polynomial ring in five variables over $\mathbb{C}$, let $x=s^2+u^3+p^2F$, and let
--   $$H=x^2F-(1+2sx)J-p^2J^2-pu,\qquad A=P/(H).$$
--   This file records two structural properties of $A$.
--
--   1. **Integral domain.** $A$ is an integral domain. Equivalently, $(H)$ is a prime ideal of $P$.
--
--   2. **Noetherian.** $A$ is a Noetherian ring, being a finitely generated $\mathbb{C}$-algebra (Hilbert basis theorem).
--
--   Being an integral domain is one of the clauses of the cancellation statement for $A$. The Noetherian property is what makes the formula $\dim A[t]=\dim A+1$ available. Combined with the isomorphism $A[t]\cong\mathbb{C}[p,s,u,F,J]$, that formula gives $\dim A=4$.
--
--   **Formalization Note** Both facts are registered as instances, `domain : IsDomain A` and `noetherian : IsNoetherianRing A`. The domain instance is pulled back along the coefficient map $\kappa:A\to\mathbb{C}[p,s,u,F,J]$, which is injective because it is the restriction to constants of the explicit isomorphism $A[t]\cong\mathbb{C}[p,s,u,F,J]$. The Noetherian instance comes from Mathlib's `Algebra.FiniteType.isNoetherianRing`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Dimension.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Dimension.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder

namespace OAI

noncomputable section

namespace ComplexCancellation

instance domain : IsDomain A :=
  Function.Injective.isDomain Cylinder.coefficientMap (by
    intro r s hrs
    apply Polynomial.C_injective
    apply Cylinder.equivalence.injective
    simpa only [Cylinder.equivalence, AlgEquiv.ofAlgHom_apply,
      Cylinder.forward_C] using hrs)

instance noetherian : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A

end ComplexCancellation

end

end OAI


