-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqChar
-- name    : ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:07.184799+00:00
-- url     : https://prove2.me/theorems/3cb2630a-c946-437f-8d7b-98fa379d35a1
-- title:
--   Sq Char
-- statement:
--   Definitions and structural lemmas for Sq Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqChar.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Statement
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
open ReciprocityTheory.ChartRestriction.DS.S7
def sq_ssEquiv (k : ℕ) (ν : Fin k → ℕ) :
    ↥(Formalism.GradedWeylDivisibility.ssIdx k k ν) ≃ sq_SSZ k (fun t => (ν t : ℤ)) :=
  Equiv.subtypeEquiv (Finsupp.equivFunOnFinite.trans (Equiv.curry (Fin k) (Fin k) ℕ)) (by
    intro m
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun l j hlj a => ?_, fun t => ?_⟩
      · have := h1 l j hlj a
        rw [zero_add] at this
        exact this
      · exact congrArg Nat.cast (h2 t)
    · rintro ⟨h1, h2⟩
      refine ⟨fun l j hlj a => ?_, fun t => ?_⟩
      · rw [zero_add]
        exact h1 l j hlj a
      · exact Nat.cast_injective (R := ℤ) (h2 t))
def sq_shiftEmb {n : ℕ} (c : ℤ) : (Fin n → ℤ) ↪ (Fin n → ℤ) :=
  ⟨fun mu i => mu i + c, fun x y h => funext fun i => by simpa using congrFun h i⟩
end ReciprocityTheory.ChartRestriction.TR.Weyl


