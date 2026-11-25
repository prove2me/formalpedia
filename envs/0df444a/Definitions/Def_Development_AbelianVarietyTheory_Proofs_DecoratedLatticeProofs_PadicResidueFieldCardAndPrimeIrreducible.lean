-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PadicResidueFieldCardAndPrimeIrreducible
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PadicResidueFieldCardAndPrimeIrreducible
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T11:15:57.53968+00:00
-- url     : https://prove2.me/theorems/b1a1486e-42b6-4f19-bcc7-774cbbb4b8fc
-- title:
--   Padic Residue Field Card And Prime Irreducible
-- statement:
--   Definitions and structural lemmas for Padic Residue Field Card And Prime Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PadicResidueFieldCardAndPrimeIrreducible.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsLocalRing
noncomputable section
namespace GlobalTheory.TAdicInt
def intEquiv (T : ℕ) [Fact T.Prime] : 𝒪[ℚ_[T]] ≃+* ℤ_[T] where
  toFun x := ⟨x.1, by
    have h := (Valuation.mem_integer_iff _ _).1 x.2
    have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff T 1 x.1).not.1 (by rw [map_one]; exact not_lt.2 h)
    rwa [norm_one, not_lt] at this⟩
  invFun x := ⟨x.1, (Valuation.mem_integer_iff _ _).2 (by
    have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff T 1 x.1).not.2 (by rw [norm_one]; exact not_lt.2 x.2)
    rwa [map_one, not_lt] at this)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
end GlobalTheory.TAdicInt


