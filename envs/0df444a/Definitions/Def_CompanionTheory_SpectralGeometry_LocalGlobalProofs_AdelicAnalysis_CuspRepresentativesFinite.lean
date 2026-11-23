-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFinite
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:09.501507+00:00
-- url     : https://prove2.me/theorems/22d9375d-8307-49a0-ad87-b0cd9f5379f9
-- title:
--   Cusp Representatives Finite
-- statement:
--   Definitions and structural lemmas for Cusp Representatives Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CuspRepresentativesFinite.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
namespace GlobalTheory.CompanionTheory.SW.Core.RowCompletion
open nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
def Adapted (A : FractionalIdeal (𝓞 F)⁰ F) (g : SL(2, F)) : Prop :=
  g 0 0 ∈ A⁻¹ ∧ g 0 1 ∈ A⁻¹ ∧ g 1 0 ∈ A ∧ g 1 1 ∈ A
end GlobalTheory.CompanionTheory.SW.Core.RowCompletion


