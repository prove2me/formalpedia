-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:24.254902+00:00
-- url     : https://prove2.me/theorems/c3d5ca84-c5cb-468e-9f09-593a22f6a158
-- title:
--   Cocycle Identity Iso
-- statement:
--   Definitions and structural lemmas for Cocycle Identity Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/CocycleIdentityIso.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

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
open scoped CategoryTheory.Obj
section Bundles
variable {X : Scheme.{0}}
def idIso (L : LB X) : LB.Iso L L := ⟨fun p => L.g p.1 p.2⟩
def gv {L' L : LB X} (w : LB.Iso L' L) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y _ (w.s (j, k))
def isoPullId {L' L : LB X} (w : LB.Iso L' L) {F : X ⟶ X} (hF : F = 𝟙 X) : LB.Iso L' (L.pull F) :=
  ⟨fun p => res (fun y hy => ⟨by have := mem_pull.1 hy.1; rw [hF] at this; exact this, hy.2⟩ :
    (LB.pull L F).U p.1 ⊓ L'.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L'.U p.2) (w.s (p.1 PUnit.unit, p.2))⟩
end Bundles
section Unif
open ReciprocityTheory.ChartRestriction.G.Out
end Unif
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


