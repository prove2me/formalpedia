-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:00:52.29104+00:00
-- url     : https://prove2.me/theorems/99aa6916-24df-4932-b4a2-605562c187b5
-- title:
--   Exists Norm One Orth Triple
-- statement:
--   Definitions and structural lemmas for Exists Norm One Orth Triple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.OrthCompl
section Ring
variable {o E : Type*} [CommRing o] [IsLocalRing o] [CommRing E]
end Ring
section Space
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
def IsON (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {k : ℕ} (e : Fin k → Fin n → E) :
    Prop :=
  ∀ i j, hf L Hm (e i) (e j) = if i = j then 1 else 0
def orthTo (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    Submodule L.O (Fin n → E) where
  carrier := {x | hf L Hm x v = 0}
  zero_mem' := by simp [hf]
  add_mem' := by
    intro a b ha hb
    show hf L Hm (a + b) v = 0
    rw [hf_add_l, ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    show hf L Hm ((c : E) • a) v = 0
    rw [hf_smul_l, ha, mul_zero]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
variable [IsNonarchimedeanLocalField F] [CharZero F]
end Space
end GlobalTheory.HL.OrthCompl


