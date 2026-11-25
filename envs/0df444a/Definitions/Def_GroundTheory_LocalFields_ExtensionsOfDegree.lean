-- Prove2me | Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
-- name    : GroundTheory_LocalFields_ExtensionsOfDegree
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:37.276264+00:00
-- url     : https://prove2.me/theorems/2445f615-33f7-584c-a8b9-2aef9909a2b4
-- title:
--   Extensions Of Degree
-- statement:
--   Definitions and structural lemmas for Extensions Of Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Polynomial IntermediateField ValuativeRel
namespace GroundTheory.LocalField
section Normed
variable {L : Type*} [NontriviallyNormedField L]
variable [CompleteSpace L] [IsUltrametricDist L]
end Normed
section MonicOfCoeffs
variable {R : Type*} [CommRing R]
def monicOfCoeffs {n : ℕ} (c : Fin n → R) : R[X] := X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
end MonicOfCoeffs
section Eisenstein
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
end Eisenstein
section Main
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Valued
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
end Valued
variable (Ω : Type*) [Field Ω] [Algebra K Ω]
end Main
end GroundTheory.LocalField


