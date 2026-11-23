-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:11.263102+00:00
-- url     : https://prove2.me/theorems/e8cea8eb-c04f-45ab-92ef-c0b8f78f42e2
-- title:
--   Alternating Difference Term Window
-- statement:
--   Definitions and structural lemmas for Alternating Difference Term Window, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlternatingDifferenceTermWindow.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
namespace GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
def dualSub (M : Submodule K.O B.A) : AddSubgroup B.A where
  carrier := {s | InDual B s M}
  zero_mem' := by intro z _; simp
  add_mem' := by
    intro s t hs ht z hz
    rw [add_mul, map_add]
    exact add_mem (hs z hz) (ht z hz)
  neg_mem' := by
    intro s hs z hz
    rw [neg_mul, map_neg]
    exact neg_mem (hs z hz)
def ind (Q : AddSubgroup B.A) (y : B.A) : ℚ := if y ∈ Q then 1 else 0
end GlobalTheory.UnitLemma.Desc.Window


