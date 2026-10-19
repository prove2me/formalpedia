-- Prove2me | Definitions.Def_MazurTransfer_AffineOpenSectionsAlgEquiv
-- name    : MazurTransfer_AffineOpenSectionsAlgEquiv
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T05:57:33.138084+00:00
-- url     : https://prove2.me/theorems/b6aff01d-63d7-4fa1-95b2-3865c1b2718b
-- title:
--   The structural R-algebra comparison for an affine open
-- statement:
--   Let $R$ be a commutative ring, let $c:X\to\operatorname{Spec}R$, let $U$ be an open subscheme of $X$, and let $B$ be an $R$-algebra. An isomorphism $e:\operatorname{Spec}B\cong U$ compatible with the maps to $\operatorname{Spec}R$ determines the specified isomorphism $\Gamma(X,U)\cong_R B$. Its underlying ring isomorphism is the canonical global-sections comparison. Both actual finite-chart polynomial-basis transports use this constructor.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. A structural constructor using the Proved public coefficient compatibility theorem. The original canonical section-ring comparison is retained as the underlying ring equivalence. The R-action on sections is precisely TwoAffineOpenCover.algebraOfHom. Native, strict and full frontend checks pass with standard axioms only, and the new constructor has a closed type. Named downstream consumers are both actual finite-chart polynomial-basis transports in original order-thirteen FiniteMapData.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the specified affine-open section comparison as an R-algebra isomorphism, given its actual compatibility with the base morphism.
Named downstream consumers: both actual finite-chart polynomial-basis transports in original order-thirteen FiniteMapData. -/
import Mathlib
import Definitions.Def_MazurTransfer_ActualAffineSectionRingTransport
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_MazurTransfer_ActualAffineSectionRingBasicOpenTransport_sectionsRingIso_coefficients_of_over
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace MazurTransfer.ActualAffineSectionRingBasicOpenTransport

def sectionsAlgEquiv_of_over (R : Type u) [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (U : X.Opens) (B : Type u) [CommRing B] [Algebra R B]
    (e : Spec (.of B) ≅ U.toScheme)
    (he : e.hom ≫ U.ι ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Γ(X, U) ≃ₐ[R] B := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  refine { (sectionsRingIso U e).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of B => f.hom r)
    (sectionsRingIso_coefficients_of_over R c U B e he)

end MazurTransfer.ActualAffineSectionRingBasicOpenTransport
#print axioms MazurTransfer.ActualAffineSectionRingBasicOpenTransport.sectionsAlgEquiv_of_over


