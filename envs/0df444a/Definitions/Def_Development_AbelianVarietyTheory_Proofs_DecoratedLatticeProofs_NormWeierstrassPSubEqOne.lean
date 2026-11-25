-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormWeierstrassPSubEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormWeierstrassPSubEqOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:51.609059+00:00
-- url     : https://prove2.me/theorems/c527bb81-648a-417c-9cbc-d0585acf4227
-- title:
--   Norm Weierstrass PSub Eq One
-- statement:
--   Definitions and structural lemmas for Norm Weierstrass PSub Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormWeierstrassPSubEqOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk


set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
namespace GlobalTheory.Klein.DiffUnit
variable {p : ℕ} [Fact p.Prime]
def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha
end GlobalTheory.Klein.DiffUnit
namespace GlobalTheory.Klein
open DiffUnit
end GlobalTheory.Klein


