-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:55.127849+00:00
-- url     : https://prove2.me/theorems/55a64eb6-6300-4a4b-bfc2-3951e049a1de
-- title:
--   Flat Tensor Pure Tensor Eq Prod Contr
-- statement:
--   Definitions and structural lemmas for Flat Tensor Pure Tensor Eq Prod Contr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
section Local
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}
def colIx (hc : Even c) (r : n) : KeptVar n c n' := ⟨(.inl r, .inr ⟨c / 2, by omega⟩), hc, rfl⟩
def rowIx (hc : Odd c) (s : n') : KeptVar n c n' := ⟨(.inr ⟨c / 2, by have := hc.pos; omega⟩, .inl s), hc, rfl⟩
def colEquiv (hc : Even c) : n ≃ KeptVar n c n' where
  toFun := colIx hc
  invFun
    | ⟨(.inl r, _), _⟩ => r
    | ⟨(.inr _, .inl _), h⟩ => absurd hc (Nat.not_even_iff_odd.2 h.1)
    | ⟨(.inr _, .inr _), h⟩ => h.elim
  left_inv r := rfl
  right_inv := by
    rintro ⟨⟨r | l, s | i⟩, h⟩
    · exact h.elim
    · obtain ⟨_, hi⟩ := h
      obtain ⟨i, _⟩ := i
      obtain rfl : i = c / 2 := hi
      rfl
    · exact absurd hc (Nat.not_even_iff_odd.2 h.1)
    · exact h.elim
def rowEquiv (hc : Odd c) : n' ≃ KeptVar n c n' where
  toFun := rowIx hc
  invFun
    | ⟨(.inr _, .inl s), _⟩ => s
    | ⟨(.inl _, .inr _), h⟩ => absurd h.1 (Nat.not_even_iff_odd.2 hc)
    | ⟨(.inl _, .inl _), h⟩ => h.elim
    | ⟨(.inr _, .inr _), h⟩ => h.elim
  left_inv s := rfl
  right_inv := by
    rintro ⟨⟨r | l, s | i⟩, h⟩
    · exact h.elim
    · exact absurd h.1 (Nat.not_even_iff_odd.2 hc)
    · obtain ⟨_, hl⟩ := h
      obtain ⟨l, _⟩ := l
      obtain rfl : l = c / 2 := hl
      rfl
    · exact h.elim
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar k Circle) (ν : Measure k)
end Local
section Abstract
def consEquiv {n : ℕ} (E : Fin (n + 1) → Type) [∀ j, MeasurableSpace (E j)] :
    (E 0 × ∀ j : Fin n, E j.succ) ≃ᵐ ∀ j, E j := (MeasurableEquiv.piFinSuccAbove E 0).symm
end Abstract
section Pair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
  {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure]
end Pair
end GlobalTheory.FunObj


