-- Prove2me | Definitions.Def_MazurTransfer_ActualAffineSectionRingTransport
-- name    : MazurTransfer_ActualAffineSectionRingTransport
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T04:53:01.918986+00:00
-- url     : https://prove2.me/theorems/0cbe5f80-997e-474f-903c-6472dd11473d
-- title:
--   Actual affine-open section-ring comparison and transported sections
-- statement:
--   Let $X$ be a scheme, let $U$ be an open subset of $X$, let $B$ be a commutative ring, and let $e:\operatorname{Spec}B\xrightarrow{\sim}U$ be an isomorphism of schemes. The specified comparison isomorphism $$\Gamma(X,U)\xrightarrow{\sim}B$$ is the composite of the restriction identification, the global-sections map of $e$, and the canonical global-sections isomorphism for $\operatorname{Spec}B$. For $b\in B$, its transported section is the inverse image of $b$ under this isomorphism. These two constructors supply the exact coordinate-to-section comparison used by the actual order-thirteen finite-map parameters.
-- source:
--   The unchanged sectionsRingIso and transportedSection constructors from checked MazurTheorem ActualAffineSectionRingBasicOpenTransport.lean. Complete Lean frontend declaration and namespace ranges retain exactly the two constructors. Both complete original kernel types are verified by closed witnesses. Original per-file attribution, Apache-2.0, and named actual finite-map downstream consumers are retained. Vas and contributors.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: basic opens transport through an actual Spec-to-open
isomorphism and its exact global section-ring comparison.
Named downstream consumers: the two actual single-section parameters in
order-13 FiniteMapData. No parameter or curve-specific identity is assumed.
-/
import Mathlib

noncomputable section
universe u
namespace MazurTransfer.ActualAffineSectionRingBasicOpenTransport
open CategoryTheory AlgebraicGeometry
variable {X : Scheme.{u}} (U : X.Opens) {B : Type u} [CommRing B]

def sectionsRingIso (e : Spec (.of B) ≅ U.toScheme) : Γ(X, U) ≅ CommRingCat.of B :=
  U.topIso.symm ≪≫ Scheme.Γ.mapIso e.op ≪≫ Scheme.ΓSpecIso (.of B)

def transportedSection (e : Spec (.of B) ≅ U.toScheme) (b : B) : Γ(X, U) :=
  (sectionsRingIso U e).commRingCatIsoToRingEquiv.symm b
end MazurTransfer.ActualAffineSectionRingBasicOpenTransport
#print axioms MazurTransfer.ActualAffineSectionRingBasicOpenTransport.sectionsRingIso
#print axioms MazurTransfer.ActualAffineSectionRingBasicOpenTransport.transportedSection


