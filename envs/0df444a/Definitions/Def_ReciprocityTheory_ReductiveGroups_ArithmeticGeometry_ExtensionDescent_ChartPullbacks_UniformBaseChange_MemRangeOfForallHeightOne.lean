-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:55.949812+00:00
-- url     : https://prove2.me/theorems/ffe8e980-734b-4c59-81e3-fbdc7c0fa851
-- title:
--   Mem Range Of Forall Height One
-- statement:
--   Definitions and structural lemmas for Mem Range Of Forall Height One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/MemRangeOfForallHeightOne.lean

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Integer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]
def denIdeal {ι : Type*} (x : ι → K) : Ideal A where
  carrier := {r | ∀ i, algebraMap A K r * x i ∈ (algebraMap A K).range}
  add_mem' := by
    intro a b ha hb i
    obtain ⟨u, hu⟩ := ha i
    obtain ⟨v, hv⟩ := hb i
    exact ⟨u + v, by rw [map_add, hu, hv, map_add, add_mul]⟩
  zero_mem' := fun i => ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha i
    obtain ⟨u, hu⟩ := ha i
    exact ⟨c * u, by rw [map_mul, hu, smul_eq_mul, map_mul, mul_assoc]⟩
end ReciprocityTheory.ChartRestriction.G.Out.KrullAlg


