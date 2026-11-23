-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
-- name    : ReciprocityTheory_DualLattices_IsUnitOfNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:39.359804+00:00
-- url     : https://prove2.me/theorems/e916def5-6249-47b2-957f-e97b42c2b000
-- title:
--   Is Unit Of Not Mem
-- statement:
--   Definitions and structural lemmas for Is Unit Of Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsUnitOfNotMem.lean

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
open Finset Matrix
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
def mI (hv : v.Integers R) : Ideal R where
  carrier := {r | v (algebraMap R C r) < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
    calc v (algebraMap R C c) * v (algebraMap R C x) ≤ 1 * v (algebraMap R C x) :=
          mul_le_mul_of_nonneg_right (hv.map_le_one c) zero_le
      _ < 1 := by rwa [one_mul]
theorem mem_mI (hv : v.Integers R) (r : R) : r ∈ mI hv ↔ v (algebraMap R C r) < 1 := Iff.rfl
theorem v_eq_one_iff (hv : v.Integers R) (r : R) : v (algebraMap R C r) = 1 ↔ r ∉ mI hv := by
  rw [mem_mI, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (hv.map_le_one r) h⟩
theorem isUnit_of_not_mem (hv : v.Integers R) {r : R} (h : r ∉ mI hv) : IsUnit r :=
  hv.isUnit_of_one' ((v_eq_one_iff hv r).2 h)
theorem mI_isMaximal (hv : v.Integers R) : (mI hv).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨by simp [mem_mI], fun J x hle hx hxJ => ?_⟩
  obtain ⟨u, rfl⟩ := isUnit_of_not_mem hv hx
  have : (↑u⁻¹ : R) * u ∈ J := J.mul_mem_left _ hxJ
  simpa using this
abbrev res (hv : v.Integers R) : R →+* R ⧸ mI hv := Ideal.Quotient.mk (mI hv)
instance instField (hv : v.Integers R) : Field (R ⧸ mI hv) :=
  haveI := mI_isMaximal hv
  Ideal.Quotient.field _
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField


