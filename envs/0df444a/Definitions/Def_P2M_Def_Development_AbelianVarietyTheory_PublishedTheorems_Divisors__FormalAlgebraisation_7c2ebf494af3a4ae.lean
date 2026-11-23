-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:35.613796+00:00
-- url     : https://prove2.me/theorems/1f701f4d-308f-43cb-8e54-4b9a4eb56b64
-- title:
--   Formal Algebraisation
-- statement:
--   Definitions and structural lemmas for Formal Algebraisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/FormalAlgebraisation.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.Published
namespace FormalAlgebraisation
def Morphisms : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      IsSeparated Z.hom → LocallyOfFiniteType Z.hom → QuasiCompact Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) →
    ∀ f : ∀ e, (Y e).left ⟶ Z.left,
      (∀ e, f e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ f (e + 1) = f e) →
      ∃! g : X ⟶ Z, ∀ e, b e ≫ g.left = f e
def Schemes : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left),
      (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) →
      (∀ e, IsProper (Y e).hom) →
    ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) →
      RelAmple (Y 0) (N 0) →
      ∃ (X : Over (Spec (CommRingCat.of R))) (M : LB X.left) (b : ∀ e, (Y e).left ⟶ X.left),
        IsProper X.hom ∧ M.IsLB ∧ RelAmple X M ∧
        (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧
        ∀ e, LBIso (N e) (M.pull (b e))
end FormalAlgebraisation
def FormalAlgebraisation : Prop :=
  FormalAlgebraisation.Morphisms ∧ FormalAlgebraisation.Schemes
namespace FormalAlgebraisation
variable {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
end FormalAlgebraisation
end GlobalTheory.Published


