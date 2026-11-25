-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTau
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTau
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:23.994191+00:00
-- url     : https://prove2.me/theorems/94ea96aa-d72b-5734-8d40-c8a81dac20a3
-- title:
--   Quantum Determinant Tau
-- statement:
--   Definitions and structural lemmas for Quantum Determinant Tau, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/QuantumDeterminantTau.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeDuality_GlRelTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.CapelliTwist
open Formalism.REAL (qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open CompanionTheory.RgExh.Hk
end GlobalTheory.CompanionTheory.CapelliTwist


