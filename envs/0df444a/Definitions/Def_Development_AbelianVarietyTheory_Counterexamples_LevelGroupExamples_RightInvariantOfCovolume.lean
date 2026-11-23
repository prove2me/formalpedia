-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RightInvariantOfCovolume
-- name    : Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RightInvariantOfCovolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:45.246316+00:00
-- url     : https://prove2.me/theorems/b7ed5881-ea83-435d-bae7-389c0df3dce4
-- title:
--   Right Invariant Of Covolume
-- statement:
--   Definitions and structural lemmas for Right Invariant Of Covolume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Pointwise
namespace GlobalTheory.AutQuotCheck
section Alg
variable {G : Type} [Group G] (Γ : Subgroup G)
abbrev cls (g : G) : Quotient (QuotientGroup.rightRel Γ) := Quotient.mk _ g
end Alg
section Top
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ]
end Top
end GlobalTheory.AutQuotCheck


