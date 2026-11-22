-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:27.305901+00:00
-- url     : https://prove2.me/theorems/db7cfc7a-fa9d-435e-a168-ad5842d5430d
-- title:
--   Sab Comp
-- statement:
--   Definitions and structural lemmas for Sab Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabComp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
def pushPt {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) {T : Over S'} (x : T ⟶ G') : Over.mk (T.hom ≫ f) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, w, ← Category.assoc, Over.w x])
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


