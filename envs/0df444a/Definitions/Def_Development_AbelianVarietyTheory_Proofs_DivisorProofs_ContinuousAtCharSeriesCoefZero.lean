-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:58.408733+00:00
-- url     : https://prove2.me/theorems/7f59cbcc-1d8c-4cbb-a607-0a8d2bc51ea2
-- title:
--   Continuous At Char Series Coef Zero
-- statement:
--   Definitions and structural lemmas for Continuous At Char Series Coef Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousAtCharSeriesCoefZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.CharSeriesCoef
noncomputable def avg {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y)
    (χ : AddChar Y ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ i, χ (w i)
end GlobalTheory.CharSeriesCoef


