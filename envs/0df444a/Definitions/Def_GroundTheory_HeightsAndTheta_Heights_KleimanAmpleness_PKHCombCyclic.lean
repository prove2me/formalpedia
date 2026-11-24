-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:34.446456+00:00
-- url     : https://prove2.me/theorems/46df8f66-b99a-4934-a748-c3073ea841be
-- title:
--   PKHComb Cyclic
-- statement:
--   Definitions and structural lemmas for PKHComb Cyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombCyclic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
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
namespace KHCombCyclic
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
abbrev FaceOK (J : ∀ k, Finset (ι k)) (n : ℕ) (G : ∀ k, Finset (ι k)) : Prop :=
  ((∀ l, (G l).Nonempty) ∧ ∑ l, ((G l).card - 1) = n) ∧ ∀ l, J l ⊆ G l
end KHCombCyclic
end
end GroundTheory.Heights₂.Heights.Kleiman


