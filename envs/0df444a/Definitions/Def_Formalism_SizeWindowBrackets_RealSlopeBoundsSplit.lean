-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_RealSlopeBoundsSplit
-- name    : Formalism_SizeWindowBrackets_RealSlopeBoundsSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:49:50.753955+00:00
-- url     : https://prove2.me/theorems/a521dff4-7999-4ac3-a819-a4bbbefc477f
-- title:
--   Real Slope Bounds Split
-- statement:
--   Definitions and structural lemmas for Real Slope Bounds Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/RealSlopeBoundsSplit.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice.Fold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas
open Finset
noncomputable section
def wmean {ι : Type*} [Fintype ι] (d X : ι → ℝ) : ℝ :=
  (∑ u, d u * X u) / ∑ u, d u
def umax {ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty X
def sF {ι : Type*} [Fintype ι] (d muN h : ι → ℝ) : ℝ :=
  wmean d (fun u => muN u - h u)
def uF {ι : Type*} [Fintype ι] [Nonempty ι] (d muMaxN muN h : ι → ℝ) : ℝ :=
  umax (fun u => muMaxN u - h u) - sF d muN h
def Slopes2 {ι : Type*} (muMaxN muN muMaxM muM dr BE : ι → ℝ) (Sg0 : ℝ) : Prop :=
  (∀ u, muMaxN u ≤ muMaxM u + (Sg0 - dr u)) ∧ (∀ u, muN u = muM u + (Sg0 - dr u) - BE u)
def Slopes2ge {ι : Type*} (muMaxN muN muMaxM muM dr BE : ι → ℝ) (Sg0 : ℝ) : Prop :=
  (∀ u, muMaxN u ≤ muMaxM u + (Sg0 - dr u)) ∧ (∀ u, muM u + (Sg0 - dr u) - BE u ≤ muN u)
def rhsU {ι : Type*} [Fintype ι] [Nonempty ι] (d muMaxM muM h dr BE : ι → ℝ) : ℝ :=
  umax (fun u => muMaxM u - h u) - wmean d (fun u => muM u - h u) + wmean d (fun u => dr u + BE u)
def LemmaU (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2 muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE
def LemmaUge (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE
def LemmaUNeedsDr : Prop :=
  ¬ ∀ (d muMaxN muN muMaxM muM h dr BE : Unit → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → Slopes2 muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE
def LemmaUSharp : Prop :=
  ∃ (d muMaxN muN muMaxM muM h dr BE : Bool → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) ∧ (∀ u, 0 ≤ dr u) ∧ (∀ u, 0 < BE u) ∧ (∃ u, 0 < dr u) ∧
    Slopes2 muMaxN muN muMaxM muM dr BE Sg0 ∧
    uF d muMaxN muN h = rhsU d muMaxM muM h dr BE
def RealSlopeBounds (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 A A' V : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    (∀ u, muMaxM u ≤ A) → (∀ u, -A' ≤ muM u) → (∀ u u', |h u - h u'| ≤ V) →
    uF d muMaxN muN h ≤ A + A' + V + wmean d (fun u => dr u + BE u)
def RealSlopeBoundsSplit (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE lT : ι → ℝ) (Sg0 A A' sa V1 Lk : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    (∀ u, muMaxM u ≤ A) → (∀ u, -A' ≤ muM u) →
    (∀ u u', |(h u + sa * lT u) - (h u' + sa * lT u')| ≤ V1) →
    (∀ u u', |lT u - lT u'| ≤ Lk) →
    uF d muMaxN muN h ≤ A + A' + (V1 + |sa| * Lk) + wmean d (fun u => dr u + BE u)
end
end Formalism.LFunctionChainParameters.WeightedMeanLemmas


