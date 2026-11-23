-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:46.607878+00:00
-- url     : https://prove2.me/theorems/ee017ced-715a-4108-89be-3cc75ad56dc5
-- title:
--   Central Exponent Bound Over
-- statement:
--   Definitions and structural lemmas for Central Exponent Bound Over, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CentralExponentBoundOver.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IrreducibleTensorCharacter
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_mem_KOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData ValuativeRel Matrix Topology Filter
open scoped TensorProduct
namespace GlobalTheory.CentralExponent
section Abstract
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
end Abstract
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mul_small {γ : (ValueGroupWithZero k)ˣ} {A B : Matrix n n k} (hA : IntM A)
    (hB : ∀ i j, valuation k (B i j) < γ) (i j : n) : valuation k ((A * B) i j) < γ := by
  refine Valuation.map_sum_lt _ γ.ne_zero fun s _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left' (hA i s)).trans_lt (hB s j)
variable (n) in

def cong (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) : Subgroup (GL n k) where
  carrier := {g | ∀ i j, valuation k ((g.val - 1) i j) < γ}
  one_mem' := fun i j => by simp
  mul_mem' := by
    intro g h hg hh i j
    have h1 : g ∈ KOne k n := mem_KOne.2 fun i j => (hg i j).trans_le hγ
    have : (g * h).val - 1 = g.val * (h.val - 1) + (g.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [this]
    exact Valuation.map_add_lt _ (mul_small (intM_of_mem_KO (KOne_le_KO h1)) hh i j) (hg i j)
  inv_mem' := by
    intro g hg i j
    have h1 : g ∈ KOne k n := mem_KOne.2 fun i j => (hg i j).trans_le hγ
    have : (g⁻¹).val - 1 = (-(g⁻¹).val) * (g.val - 1) := by
      rw [neg_mul, mul_sub, Units.inv_mul]; simp
    rw [this]
    exact mul_small (intM_of_mem_KO (KOne_le_KO (inv_mem h1))).neg hg i j
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
end Local
section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  {V X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
end Main
end GlobalTheory.CentralExponent


