-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZero
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZero
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:26:58.1485+00:00
-- url     : https://prove2.me/theorems/b94f613d-b52f-4336-adab-25318dabb0ae
-- title:
--   Partial Reduction Eq Zero Of Flat Map Column Zero
-- statement:
--   Definitions and structural lemmas for Partial Reduction Eq Zero Of Flat Map Column Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEqZeroOfFlatMapColumnZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
namespace GlobalTheory.FlatRed
open GlobalTheory.FlatFactor GlobalTheory.LocFlat
def readPart {k : Type} {n n' : Type} {c : ℕ} (ρ : ℕ) (h : ρ < c + 1)
    (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix n (n' ⊕ Unit) k :=
  Matrix.of fun r q => Sum.elim (fun s => t (.inl r) (.inl s)) (fun _ => t (.inl r) (.inr ⟨ρ, h⟩)) q
section
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
theorem mem_itFree (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) : e ∈ itFree n n' c ρ ↔ Free (ρ + 1) e := by
  simp [itFree]
variable {k : Type} [Field k]
end
end GlobalTheory.FlatRed


