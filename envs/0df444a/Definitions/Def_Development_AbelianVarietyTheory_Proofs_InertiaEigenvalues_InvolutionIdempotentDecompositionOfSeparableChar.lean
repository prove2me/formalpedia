-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:18.337978+00:00
-- url     : https://prove2.me/theorems/69f848a1-e527-4a7f-af07-08d49b5c1c9f
-- title:
--   Involution Idempotent Decomposition Of Separable Char
-- statement:
--   Definitions and structural lemmas for Involution Idempotent Decomposition Of Separable Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvolutionIdempotentDecompositionOfSeparableChar.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
namespace GlobalTheory.UnitLemma.Desc
open Classical
section Generic
variable {R : Type} [CommRing R]
def FieldIdem (f : R) : Prop :=
  IsIdempotentElem f ∧ f ≠ 0 ∧ ∀ y, f * y ≠ 0 → ∃ z, f * y * z = f
end Generic
end GlobalTheory.UnitLemma.Desc


