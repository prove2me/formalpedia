-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:45.373725+00:00
-- url     : https://prove2.me/theorems/1f1409d0-e71d-4c22-91f7-0ec444dacbfc
-- title:
--   Loc Ring
-- statement:
--   Definitions and structural lemmas for Loc Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocRing.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraAlt
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
def locRing {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) :
    Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u v : MRing ι) (a : K → ℕ)
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)),
    v ∉ W ∧ IsMultiHomog u a ∧ IsMultiHomog v a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩}
def locIdeal {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)) : Ideal (locRing P W) :=
  Ideal.span {z | (z : FractionRing (MRing ι ⧸ P)) = y}
def specZTwo : Ideal (MRing (PBlk 1)) := Ideal.span {C 2}
end
end GroundTheory.Heights₂.Heights.Inter


