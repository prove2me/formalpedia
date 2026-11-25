-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverRelationUniqueness
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverRelationUniqueness
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:25.070336+00:00
-- url     : https://prove2.me/theorems/a5f4a20c-2d16-4eaf-8a41-30c66453555d
-- title:
--   Term Over Relation Uniqueness
-- statement:
--   Definitions and structural lemmas for Term Over Relation Uniqueness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermOverRelationUniqueness.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.PairingClass
section Mat
variable {E : Type} [CommRing E] {n : ℕ}
def UT (A : Matrix (Fin n) (Fin n) E) : Prop := (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1
def IntM (O : Subring E) (A : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, A i j ∈ O
def Tied (O : Subring E) (θ : E) (A A' : Matrix (Fin n) (Fin n) E) : Prop :=
  UT A ∧ UT A' ∧ IntM O A ∧ IntM O A' ∧ ∃ C, IntM O C ∧ A' = A + θ • C
variable {V : Type} [AddCommGroup V] [Module E V]
def act (g : Fin n → V) (A : Matrix (Fin n) (Fin n) E) : Fin n → V := fun j => ∑ i, A i j • g i
end Mat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
end GlobalTheory.HL.PairingClass


