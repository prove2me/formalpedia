-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:05.453534+00:00
-- url     : https://prove2.me/theorems/1737c919-03e1-41a8-8cc0-ba46e7dc94e1
-- title:
--   Exists Is Symmetric Position Level
-- statement:
--   Definitions and structural lemmas for Exists Is Symmetric Position Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsSymmetricPositionLevel.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_mem
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
noncomputable section
namespace GlobalTheory.SymLevelExists
section Plain
variable {F : Type} [Field F] {κ l : ℕ}
def symGroup (F : Type) [Field F] (κ l p : ℕ) : Subgroup (GL (Fin κ ⊕ Fin l) F) where
  carrier := {x | ∃ u ∈ N F (Fin κ) l p, ∃ γ : GL (Fin κ) F, IsUpperUnip Fin.val γ.val ∧ x = u * embX l γ}
  one_mem' := ⟨1, one_mem _, 1, fun _ _ _ => rfl, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, γ, hγ, rfl⟩ ⟨u', hu', γ', hγ', rfl⟩
    refine ⟨_, mul_mem hu (Radical.conj_mem γ hu'), γ * γ',
      Radical.Uni.mul (b := Fin.val) hγ hγ', ?_⟩
    rw [map_mul]; group
  inv_mem' := by
    rintro _ ⟨u, hu, γ, hγ, rfl⟩
    refine ⟨_, Radical.conj_mem γ⁻¹ (inv_mem hu), γ⁻¹, Radical.Uni.inv (b := Fin.val) hγ, ?_⟩
    rw [map_inv]; group
def symSum (x : GL (Fin κ ⊕ Fin l) F) : F := simpleSum x + superSum Fin.val x.val.toBlocks₁₁
end Plain
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def symSumInt {κ l : ℕ} (g : GL (Fin κ ⊕ Fin l) 𝒪[k]) : 𝒪[k] :=
  (∑ i : Fin l, ∑ j : Fin l, if j.val = i.val + 1 then g.val (Sum.inr i) (Sum.inr j) else 0) +
    ∑ i : Fin κ, ∑ j : Fin κ, if j.val = i.val + 1 then g.val (Sum.inl i) (Sum.inl j) else 0
end Local
end GlobalTheory.SymLevelExists


