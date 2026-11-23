-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_SqPosOfNe
-- name    : Development_WeilBound_CoreStatements_ThetaDilations_SqPosOfNe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:06.720095+00:00
-- url     : https://prove2.me/theorems/7c6cb490-34f8-4c65-a71c-dc83e0b747fa
-- title:
--   Sq Pos Of Ne
-- statement:
--   Definitions and structural lemmas for Sq Pos Of Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean

import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups
noncomputable section
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]
variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}
variable (H : NAQuad ψ h B μ)
include H
end PositivityTheory.PlacePermOperatorBicommutantSpan


