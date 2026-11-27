-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusLiftEmbeddingsUnit
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusLiftEmbeddingsUnit
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:57.673945+00:00
-- url     : https://prove2.me/theorems/046ca8e6-64e9-4656-aba3-b0e2c8e00f77
-- title:
--   Frobenius Lift Embeddings Unit
-- statement:
--   Definitions and structural lemmas for Frobenius Lift Embeddings Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FrobeniusLiftEmbeddingsUnit.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqOfMapEqOfPowEqOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.TeichSeq
variable {C : Type} [Field C] (V : VF C)
def intRing : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha
def maxId : Ideal (intRing V) where
  carrier := {x | V.MM (x : C)}
  add_mem' := fun {a b} ha hb => V.v.map_lt_add ha hb
  zero_mem' := by simp [VF.MM]
  smul_mem' := fun c x hx => by
    have hc : (0 : WithTop ℝ) ≤ V.v c := c.2
    show 0 < V.v ((c : C) * x)
    rw [V.v.map_mul]
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left hc)
instance : (maxId V).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one]
    show ¬ 0 < V.v 1
    simp
  mem_or_mem' := fun {a b} hab => by
    have h : 0 < V.v ((a : C) * b) := hab
    rw [V.v.map_mul] at h
    by_contra hn
    rw [not_or] at hn
    have h1 : V.v a ≤ 0 := not_lt.1 hn.1
    have h2 : V.v b ≤ 0 := not_lt.1 hn.2
    exact absurd h (not_lt.2 (add_nonpos h1 h2))
end GlobalTheory.TeichSeq
namespace GlobalTheory
end GlobalTheory


