-- Prove2me | Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Groups
-- name    : Formalism_TameInertiaTowers_CentralOrderTwo_Groups
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:10.162803+00:00
-- url     : https://prove2.me/theorems/0594024e-110f-4485-82eb-b956f80871c6
-- title:
--   Groups
-- statement:
--   Definitions and structural lemmas for Groups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Groups.lean

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open scoped commutatorElement
namespace Formalism.TwoAdicCyclotomicDecomposition
section CommGen
variable {H : Type} [Group H]
theorem comm_mul_left_of_central (hcen : commutator H ≤ Subgroup.center H) (a b y : H) :
    ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆ := by
  have hc : ∀ z : H, z * ⁅b, y⁆ = ⁅b, y⁆ * z := fun z =>
    Subgroup.mem_center_iff.mp (hcen (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top b) (Subgroup.mem_top y))) z
  calc ⁅a * b, y⁆ = a * (⁅b, y⁆ * (y * a⁻¹ * y⁻¹)) := by
        simp only [commutatorElement_def]; group
    _ = a * ((y * a⁻¹ * y⁻¹) * ⁅b, y⁆) := by rw [hc]
    _ = ⁅a, y⁆ * ⁅b, y⁆ := by simp only [commutatorElement_def]; group
def commLeftSub (hcen : commutator H ≤ Subgroup.center H) (C : Subgroup H) (y : H) :
    Subgroup H where
  carrier := {x | ⁅x, y⁆ ∈ C}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [comm_mul_left_of_central hcen]
    exact C.mul_mem ha hb
  one_mem' := by
    simp only [Set.mem_ofPred_eq, commutatorElement_one_left]
    exact C.one_mem
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ⁅a⁻¹, y⁆ * ⁅a, y⁆ = 1 := by
      rw [← comm_mul_left_of_central hcen, inv_mul_cancel, commutatorElement_one_left]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact C.inv_mem ha
end CommGen
end Formalism.TwoAdicCyclotomicDecomposition


