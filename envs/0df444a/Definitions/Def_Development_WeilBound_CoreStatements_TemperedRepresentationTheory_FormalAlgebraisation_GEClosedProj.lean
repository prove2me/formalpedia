-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_FormalAlgebraisation_GEClosedProj
-- name    : Development_WeilBound_CoreStatements_TemperedRepresentationTheory_FormalAlgebraisation_GEClosedProj
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:37.339347+00:00
-- url     : https://prove2.me/theorems/0b9805fa-4d4f-50a3-af2d-eca521e6feb3
-- title:
--   GEClosed Proj
-- statement:
--   Definitions and structural lemmas for GEClosed Proj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/FormalAlgebraisation/GEClosedProj.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out
namespace PositivityTheory.FormalThickening
def GEClosed : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (P : Over (Spec (CommRingCat.of R))), IsSeparated P.hom → LocallyOfFiniteType P.hom →
      QuasiCompact P.hom →
    ∀ (C : ℕ → Scheme.{0}) (i : ∀ e, C e ⟶ (thickObj R I e P).left) (β : ∀ e, C e ⟶ C (e + 1)),
      (∀ e, IsClosedImmersion (i e)) →
      (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P)) →
      IsProper (i 0 ≫ (thickObj R I 0 P).hom) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ P.left) (b : ∀ e, C e ⟶ C'),
      IsClosedImmersion j ∧ IsProper (j ≫ P.hom) ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst P.hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e
def GEClosedProj : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ N : ℕ,
    let P : Over (Spec (CommRingCat.of R)) :=
      Over.mk (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)
    ∀ (C : ℕ → Scheme.{0}) (i : ∀ e, C e ⟶ (thickObj R I e P).left) (β : ∀ e, C e ⟶ C (e + 1)),
      (∀ e, IsClosedImmersion (i e)) →
      (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P)) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ P.left) (b : ∀ e, C e ⟶ C'),
      IsClosedImmersion j ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst P.hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e
def IsoOfThick : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X C : Over (Spec (CommRingCat.of R))) (p : C ⟶ X), IsProper X.hom → IsProper p.left →
      (∀ e, IsIso ((Over.pullback (thick R I e)).map p).left) → IsIso p
end PositivityTheory.FormalThickening


