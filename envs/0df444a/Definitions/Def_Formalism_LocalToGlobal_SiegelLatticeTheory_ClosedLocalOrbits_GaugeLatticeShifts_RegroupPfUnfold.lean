-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RegroupPfUnfold
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RegroupPfUnfold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:26.296392+00:00
-- url     : https://prove2.me/theorems/610d1b93-7ca0-4963-a2fd-31418d86cc7f
-- title:
--   Regroup Pf Unfold
-- statement:
--   Definitions and structural lemmas for Regroup Pf Unfold, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RegroupPfUnfold.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Formalism.L2.SG.Pf.RegroupPf
section OrbitUnfold
variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
def stabSub (N : Subgroup H) {C : Type*} (act : N → C → C) (h1 : ∀ c, act 1 c = c)
    (hmul : ∀ n m c, act (n * m) c = act n (act m c)) (r : C) : Subgroup H where
  carrier := {h | ∃ n : N, (n : H) = h ∧ act n r = r}
  one_mem' := ⟨1, rfl, h1 r⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
    exact ⟨a * b, rfl, by rw [hmul, hb, ha]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl, ha⟩
    refine ⟨a⁻¹, rfl, ?_⟩
    calc act a⁻¹ r = act a⁻¹ (act a r) := by rw [ha]
      _ = r := by rw [← hmul, inv_mul_cancel, h1]
end OrbitUnfold
end Formalism.L2.SG.Pf.RegroupPf


