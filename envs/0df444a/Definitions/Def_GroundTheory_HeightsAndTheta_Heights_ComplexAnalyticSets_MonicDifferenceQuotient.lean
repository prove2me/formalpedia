-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonicDifferenceQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonicDifferenceQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:37.129923+00:00
-- url     : https://prove2.me/theorems/c39edc29-cc2b-4126-a52f-6ca6a5655c08
-- title:
--   Monic Difference Quotient
-- statement:
--   Definitions and structural lemmas for Monic Difference Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/MonicDifferenceQuotient.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Finset
def monicDifferenceCoeff {d : ℕ} (C : Fin d → ℂ) (s : ℂ) (j : Fin d) : ℂ :=
  s ^ (d - 1 - (j : ℕ)) + ∑ k ∈ univ.filter (fun k : Fin d => (j : ℕ) < k), C k * s ^ ((k : ℕ) - 1 - j)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


