-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSumFundamentalDomain
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSumFundamentalDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:42.814109+00:00
-- url     : https://prove2.me/theorems/9128c8b9-4bc1-4f03-a927-d40078c48bf5
-- title:
--   Double Coset Sum Fundamental Domain
-- statement:
--   Definitions and structural lemmas for Double Coset Sum Fundamental Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetSumFundamentalDomain.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace GlobalTheory.DoubleCosetAdjoint
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)
end GlobalTheory.DoubleCosetAdjoint


