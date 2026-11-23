-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:24.716571+00:00
-- url     : https://prove2.me/theorems/fc4269ee-01e1-4788-a3d0-1d30219604f2
-- title:
--   Split Torus Is Comm Mon Obj St
-- statement:
--   Definitions and structural lemmas for Split Torus Is Comm Mon Obj St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/SplitTori/SplitTorusIsCommMonObjSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Semi
def splitTorus_isCommMonObjSt : Prop :=
  ∀ (S : Scheme.{u}) (X : Type u) [AddCommGroup X], IsCommMonObj (splitTorus S X)
def characters_splitTorusSt : Prop :=
  ∀ (S : Scheme.{u}) [Nonempty S] [ConnectedSpace S] (X : Type u) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X],
    ∃ e : X ≃ characters (splitTorus S X),
      ∀ a b : X, (e (a + b)).1 = lift (e a).1 (e b).1 ≫ μ
def mulN_isMonHomSt : Prop :=
  ∀ (S : Scheme.{u}) (G : Over S) [GrpObj G] [IsCommMonObj G] (m : ℕ), IsMonHom (mulN G m)
end ReciprocityTheory.ChartRestriction.G.Semi


