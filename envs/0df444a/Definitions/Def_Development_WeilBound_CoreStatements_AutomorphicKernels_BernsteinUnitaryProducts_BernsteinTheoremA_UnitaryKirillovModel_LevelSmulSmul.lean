-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_UnitaryKirillovModel_LevelSmulSmul
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_UnitaryKirillovModel_LevelSmulSmul
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:57:24.828107+00:00
-- url     : https://prove2.me/theorems/958fa6df-4526-489f-86c3-2168e2663454
-- title:
--   Level Smul Smul
-- statement:
--   Definitions and structural lemmas for Level Smul Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/UnitaryKirillovModel/LevelSmulSmul.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory
namespace PositivityTheory.PfBern.Unit
section Faith
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
section Level
variable {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
end Level
end Faith
end PositivityTheory.PfBern.Unit


