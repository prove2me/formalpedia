-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_InstIsZLatticeDualLat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_InstIsZLatticeDualLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:01.87223+00:00
-- url     : https://prove2.me/theorems/e549d6db-fb4b-4405-9196-52e4e8b79ee2
-- title:
--   Inst Is ZLattice Dual Lat
-- statement:
--   Definitions and structural lemmas for Inst Is ZLattice Dual Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/InstIsZLatticeDualLat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_H_dualIsLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open Module
noncomputable section
namespace PI.Tr
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem dualLat_eq (Λ : Submodule ℤ E) :
    dualLat Λ = LinearMap.BilinForm.dualSubmodule (innerₗ E) Λ := by
  ext y
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  show (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) ↔ _
  refine forall₂_congr fun x _ => ?_
  rw [innerₗ_apply_apply, real_inner_comm, Submodule.mem_one]
  simp only [algebraMap_int_eq, eq_intCast]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩
section lattice
variable [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
instance instDiscreteDualLat : DiscreteTopology (dualLat Λ) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  rw [dualLat_eq]
  exact (Formalism.H.dualIsLattice E Λ).1
instance instIsZLatticeDualLat : IsZLattice ℝ (dualLat Λ) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have h := Formalism.H.dualIsLattice E Λ
  haveI := h.1
  have h2 : IsZLattice ℝ (Formalism.H.dual Λ) := h.2
  constructor
  rw [dualLat_eq]
  exact h2.span_top
end lattice
end PI.Tr


