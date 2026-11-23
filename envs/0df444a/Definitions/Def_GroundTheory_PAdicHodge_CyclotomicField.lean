-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
-- name    : GroundTheory_PAdicHodge_CyclotomicField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:28:24.108681+00:00
-- url     : https://prove2.me/theorems/a3c53146-3de4-4918-9c53-bb4290d11eeb
-- title:
--   Cyclotomic Field
-- statement:
--   Definitions and structural lemmas for Cyclotomic Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicField.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open IntermediateField Polynomial
noncomputable section
variable (p : ℕ) [Fact p.Prime]
def cycl (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  adjoin ℚ_[p] {x : PadicAlgCl p | x ^ (p ^ n) = 1}
variable {p}
theorem finite_setOf_pow_eq_one (n : ℕ) : {x : PadicAlgCl p | x ^ (p ^ n) = 1}.Finite := by
  classical
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  refine (nthRoots (p ^ n) (1 : PadicAlgCl p)).toFinset.finite_toSet.subset fun x hx => ?_
  simpa [Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots hpos] using hx
instance finiteDimensional_cycl (n : ℕ) : FiniteDimensional ℚ_[p] (cycl p n) := by
  haveI : Finite {x : PadicAlgCl p | x ^ (p ^ n) = 1} := (finite_setOf_pow_eq_one n).to_subtype
  exact finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
end
end GroundTheory.PAdicHodge


