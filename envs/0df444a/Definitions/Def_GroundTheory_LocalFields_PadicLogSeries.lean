-- Prove2me | Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
-- name    : GroundTheory_LocalFields_PadicLogSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:37.980142+00:00
-- url     : https://prove2.me/theorems/1d84ff27-def0-4740-b4f6-3e87cf2f77c5
-- title:
--   Padic Log Series
-- statement:
--   Definitions and structural lemmas for Padic Log Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Theorems.Thm_GroundTheory_LocalField_isOpen_setOf_valuation_lt
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Summation
variable (K) in

def valBall (n : ℤ) : AddSubgroup K where
  carrier := {x | normalizedValuation K x ≤ WithZero.exp (-n)}
  zero_mem' := by simp
  add_mem' hx hy := (normalizedValuation K).map_add_le hx hy
  neg_mem' hx := by simpa using hx
instance t2Space_local_field_instance : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
instance nonarchimedeanRing : NonarchimedeanRing K where
  is_nonarchimedean U hU := by
    obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp hU
    exact ⟨⟨(valuation K).ltAddSubgroup γ, isOpen_setOf_valuation_lt⟩, hγ⟩
end Summation
section Arithmetic
end Arithmetic
section CharZero
variable (K) in

noncomputable def absRamificationIndex : ℕ := (ord ((ringChar 𝓀[K] : ℕ) : K)).toNat
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
end CharZero
section Series
noncomputable def logSeries (x : K) : K := ∑' k : ℕ, (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K)
noncomputable def expSeries (x : K) : K := ∑' k : ℕ, x ^ k / (k.factorial : K)
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
end Series
section Exp
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
end Exp
end GroundTheory.LocalField


