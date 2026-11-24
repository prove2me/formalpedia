-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrame
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGenericLevelOfFrame
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T22:00:37.06046+00:00
-- url     : https://prove2.me/theorems/ec64879c-ac43-43b8-aefa-e60615b668ad
-- title:
--   Exists Generic Level Of Frame
-- statement:
--   Definitions and structural lemmas for Exists Generic Level Of Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGenericLevelOfFrame.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul_apply_succ
import Theorems.Thm_GlobalTheory_StepData_IntM_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
namespace GlobalTheory.GenericLevel
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end
section
variable {F a : Type} [Field F] [Fintype a] [DecidableEq a]
def upperUnip (F : Type) {a : Type} [Field F] [Fintype a] [DecidableEq a] (pos : a → ℕ) :
    Subgroup (GL a F) where
  carrier := {g | IsUpperUnip pos (g : Matrix a a F)}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {g h} hg hh => Radical.Uni.mul (b := pos) hg hh
  inv_mem' := fun {g} hg => Radical.Uni.inv (b := pos) hg
theorem superSum_mul {pos : a → ℕ} {M M' : Matrix a a F} (h : IsUpperUnip pos M)
    (h' : IsUpperUnip pos M') : superSum pos (M * M') = superSum pos M + superSum pos M' := by
  unfold superSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · exact Radical.Uni.mul_apply_succ (b := pos) h h' hs
  · simp
noncomputable def genChar (φ : AddChar F Circle) (pos : a → ℕ) : upperUnip F pos →* ℂˣ :=
  Circle.toUnits.comp (MonoidHom.mk' (fun g => φ (superSum pos ((g : GL a F) : Matrix a a F)))
    (fun g h => by
      rw [← AddChar.map_add_eq_mul, ← superSum_mul g.2 h.2]
      rfl))
end
end GlobalTheory.GenericLevel


