-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:56.2597+00:00
-- url     : https://prove2.me/theorems/5a19184f-64fa-46f2-868a-b429e4633cf5
-- title:
--   Rrc Tendsto Vec
-- statement:
--   Definitions and structural lemmas for Rrc Tendsto Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise InnerProductSpace
section Cont
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : G → (H →L[ℂ] H)}
def rrc_C (π : G → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {x | Tendsto (fun h => π h x) (𝓝 1) (𝓝 x)}
  add_mem' := fun {a b} ha hb => by
    have := Tendsto.add ha hb
    simpa only [mem_ofPred_eq, map_add] using this
  zero_mem' := by
    simp only [mem_ofPred_eq, map_zero]
    exact tendsto_const_nhds
  smul_mem' := fun c a ha => by
    have := Tendsto.const_smul ha c
    simpa only [mem_ofPred_eq, map_smul] using this
end Cont
end Formalism.MainNotions.LeviCoordinates
end


