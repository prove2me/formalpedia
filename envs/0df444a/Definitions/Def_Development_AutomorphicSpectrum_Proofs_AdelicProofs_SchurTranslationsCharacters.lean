-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_AdelicProofs_SchurTranslationsCharacters
-- name    : Development_AutomorphicSpectrum_Proofs_AdelicProofs_SchurTranslationsCharacters
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:43.949892+00:00
-- url     : https://prove2.me/theorems/18d02786-413c-41a4-812d-d251b586fb7a
-- title:
--   Schur Translations Characters
-- statement:
--   Definitions and structural lemmas for Schur Translations Characters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean

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
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.SchurChar
section Basic
variable {V : Type} [TopologicalSpace V]
def Comm (T : (V → ℂ) → (V → ℂ)) (m : V → ℂ) : Prop :=
  IsLocallyConstant m ∧ ∀ φ, SB φ → T (fun u => m u * φ u) = fun u => m u * T φ u
end Basic
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
  {χ : V → V → ℂ} {μ : Measure V}
end GlobalTheory.CompanionTheory.SW.SchurChar


