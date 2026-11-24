-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:33.954841+00:00
-- url     : https://prove2.me/theorems/781b307e-c4e1-482a-9e96-4b217496a5d2
-- title:
--   KHComb Cyclic St
-- statement:
--   Definitions and structural lemmas for KHComb Cyclic St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/KHCombCyclicSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeObj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
def KHCombCyclic.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (J : ∀ k, Finset (ι k)) (n : ℕ),
    (∀ k, J k = ∅ ∨ J k = Finset.univ) →
      combD S J n (singOne S J n) = 0 ∧
        ∀ f : CombC S J n, combD S J n f = 0 → ∃ s : S, f - s • singOne S J n ∈ combB S J n
end
end GroundTheory.Heights₂.Heights.Kleiman


