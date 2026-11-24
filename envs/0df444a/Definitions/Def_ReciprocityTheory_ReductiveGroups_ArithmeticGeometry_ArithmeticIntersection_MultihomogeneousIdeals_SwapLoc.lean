-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:56.366333+00:00
-- url     : https://prove2.me/theorems/8f0b1514-c6f5-49af-b64a-6c91b0dd1424
-- title:
--   Swap Loc
-- statement:
--   Definitions and structural lemmas for Swap Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/SwapLoc.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI
def IsLocData (R T : Type*) [CommRing R] [CommRing T] [Algebra R T] (S : Submonoid R)
    (V : Ideal R) : Prop :=
  (∀ s ∈ S, IsUnit (algebraMap R T s)) ∧
  (∀ y : T, ∃ r : R, ∃ s ∈ S, algebraMap R T r = y * algebraMap R T s) ∧
  (∀ r : R, algebraMap R T r = 0 → ∃ s ∈ S, s * r ∈ V) ∧
  (∀ v ∈ V, algebraMap R T v = 0)
section LocData
variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] {S : Submonoid R} {V : Ideal R}
end LocData
open Classical in

noncomputable def lenAt {R : Type*} [CommRing R] (J W : Ideal R) : ℕ∞ :=
  if h : W.IsPrime then
    haveI := h
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J))
  else 0
section Local
variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {S : Submonoid R}
  {V Z : Ideal R} [Z.IsPrime]
end Local
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc


