-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:05.200219+00:00
-- url     : https://prove2.me/theorems/9610465c-53fd-4b00-9e9b-a94aabc833e9
-- title:
--   Int Cast Mem Reg Max At
-- statement:
--   Definitions and structural lemmas for Int Cast Mem Reg Max At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IntCastMemRegMaxAt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
theorem regRing_mem_locRing {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((x : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W :=
  x.2 W hW hPW
def regToLoc (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) : regRing P →+* locRing P W where
  toFun x := ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)
def regMaxAt (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    Ideal (regRing P) :=
  (IsLocalRing.maximalIdeal (locRing P W)).comap (regToLoc P W hW hPW)
end
end GroundTheory.Heights₂.Heights.Inter


