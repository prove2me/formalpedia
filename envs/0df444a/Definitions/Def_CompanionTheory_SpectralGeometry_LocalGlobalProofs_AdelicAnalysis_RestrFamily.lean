-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RestrFamily
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RestrFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:34.6885+00:00
-- url     : https://prove2.me/theorems/c79609a3-2977-4d96-8e01-46054d8e9e65
-- title:
--   Restr Family
-- statement:
--   Definitions and structural lemmas for Restr Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RestrFamily.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExistsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
namespace GlobalTheory.CompanionTheory.SW.FibreGlue
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Local
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y}
open Classical in

noncomputable def restr (B : Set X) (fam : X → Measure V) : X → Measure V :=
  fun b => if b ∈ B then fam b else 0
end Local
end GlobalTheory.CompanionTheory.SW.FibreGlue


