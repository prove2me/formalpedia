-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:12.695815+00:00
-- url     : https://prove2.me/theorems/01ac1413-ad3a-4c8d-b6f7-6def1de4c63b
-- title:
--   Continuous First Orbit Map
-- statement:
--   Definitions and structural lemmas for Continuous First Orbit Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousFirstOrbitMap.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
section Top
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [TopologicalSpace R2] [IsTopologicalRing R2]
variable {M : ℕ}
end Top
section Meas
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [LocallyCompactSpace R1] [T2Space R1]
  [SecondCountableTopology R1]
  [TopologicalSpace R2] [IsTopologicalRing R2] [LocallyCompactSpace R2] [T2Space R2]
  [SecondCountableTopology R2]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
end Meas
end PI.LevelKSplit.W.MVA


