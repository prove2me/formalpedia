-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfGe
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfGe
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:22.73511+00:00
-- url     : https://prove2.me/theorems/c6fb4313-0c43-4b4d-8ed1-e842ab31e636
-- title:
--   Eq Zero Of Ge
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOfGe.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
namespace GlobalTheory.TeichPair
variable {C : Type} [Field C]
def intRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha
def maxId (V : VF C) : Ideal (intRing V) where
  carrier := {x | 0 < V.v (x : C)}
  add_mem' := fun ha hb => V.v.map_lt_add ha hb
  zero_mem' := by
    show 0 < V.v ((0 : intRing V) : C)
    simp
  smul_mem' := fun c x hx => by
    show 0 < V.v ((c : C) * x)
    rw [V.v.map_mul]
    have hc : (0 : WithTop ℝ) ≤ V.v c := c.2
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left hc)
instance maxId_prime (V : VF C) : (maxId V).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    show ¬ 0 < V.v ((1 : intRing V) : C)
    simp
  mem_or_mem' := fun {x y} h => by
    by_contra hc
    push Not at hc
    have hx : V.v (x : C) = 0 := le_antisymm (not_lt.1 hc.1) x.2
    have hy : V.v (y : C) = 0 := le_antisymm (not_lt.1 hc.2) y.2
    have h' : 0 < V.v ((x : C) * y) := h
    rw [V.v.map_mul, hx, hy] at h'
    simp at h'
end GlobalTheory.TeichPair


