-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivCycleEqZeroOfNotMem
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivCycleEqZeroOfNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:37:19.395509+00:00
-- url     : https://prove2.me/theorems/9664adb3-aecb-4194-a180-a6ee2096918b
-- title:
--   Div Cycle Eq Zero Of Not Mem
-- statement:
--   Definitions and structural lemmas for Div Cycle Eq Zero Of Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/DivCycleEqZeroOfNotMem.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ComapLiftFormConstChartPrimeExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
section Helpers
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
end Helpers
section Rel
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type u} [CommRing R]
  [IsNoetherianRing R]
end Rel
section Proof
end Proof
end
end GroundTheory.Heights₂.Heights.NumbersDVR


