-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:31:43.858618+00:00
-- url     : https://prove2.me/theorems/e1521fb1-2fad-417d-ab11-9105a8f14b84
-- title:
--   Norm Iterated Deriv Weierstrass PLe One
-- statement:
--   Definitions and structural lemmas for Norm Iterated Deriv Weierstrass PLe One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
noncomputable section
namespace GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]
def intAt (ι : ℂ ≃+* ℂ_[p]) : Subring ℂ where
  carrier := {c | ‖ι c‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha
def intFun (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) : Subring (ℂ → ℂ) :=
  Subring.closure ({fun z => L.weierstrassP z - r, L.derivWeierstrassP} ∪ {f | ∃ c ∈ intAt ι, f = fun _ => c})
end GlobalTheory.Klein


