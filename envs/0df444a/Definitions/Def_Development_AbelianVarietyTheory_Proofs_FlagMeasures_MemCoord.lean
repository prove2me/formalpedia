-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:33:41.272521+00:00
-- url     : https://prove2.me/theorems/e1ec17db-a6e7-4bfd-8350-402bd0210dec
-- title:
--   Mem Coord
-- statement:
--   Definitions and structural lemmas for Mem Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemCoord.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
namespace GlobalTheory.HL.SAN
def hq {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E := ∑ i, ∑ j, x i * Hm i j * sig (y j)
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.hq_add_l {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.SAN.hq sig Hm (a + b) y = _root_.GlobalTheory.HL.SAN.hq sig Hm a y + _root_.GlobalTheory.HL.SAN.hq sig Hm b y := by
  simp only [_root_.GlobalTheory.HL.SAN.hq, Pi.add_apply, add_mul, Finset.sum_add_distrib]
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.hq_smul_l {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.SAN.hq sig Hm (c • a) y = c * _root_.GlobalTheory.HL.SAN.hq sig Hm a y := by
  simp only [_root_.GlobalTheory.HL.SAN.hq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
def eQ {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (s : E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun v := v + hq sig Hm v u • x - hq sig Hm v x • (u + s • x)
  map_add' a b := by
    simp only [hq_add_l]; module
  map_smul' c a := by
    simp only [hq_smul_l, RingHom.id_apply]; module
end GlobalTheory.HL.SAN


