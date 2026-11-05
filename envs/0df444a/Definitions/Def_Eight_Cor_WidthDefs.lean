-- Prove2me | Definitions.Def_Eight_Cor_WidthDefs
-- name    : Eight_Cor_WidthDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:24:00.693013+00:00
-- url     : https://prove2.me/theorems/3f5a96c1-550f-4592-965a-a44d05f22733
-- title:
--   Width Defs
-- statement:
--   Definitions and structural lemmas for Width Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatStatement
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
set_option autoImplicit false
section
section
namespace Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
def neg (l : V × Bool) : V × Bool := (l.1, !l.2)
def forced (y : V) (l₁ l₂ : V × Bool) : List (List (V × Bool)) :=
  [[(y, false), l₁, l₂], [(y, true), neg l₁], [(y, true), neg l₂]]
def splitClause : List V → List (V × Bool) → List (List (V × Bool))
  | y :: ys, l₁ :: l₂ :: l₃ :: l₄ :: r => forced y l₁ l₂ ++ splitClause ys ((y, true) :: l₃ :: l₄ :: r)
  | _, C => [C]
def splitAll : List V → List (List (V × Bool)) → List (List (V × Bool))
  | _, [] => []
  | ys, C :: φ => splitClause (ys.take (C.length - 3)) C ++ splitAll (ys.drop (C.length - 3)) φ
def numFresh (φ : List (List (V × Bool))) : ℕ := (φ.map fun C => C.length - 3).sum
def Holds (a : V → Bool) (φ : List (List (V × Bool))) : Prop := ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2
def widthReduce {n : ℕ} (φ : CNF n) : CNF (n + numFresh φ) :=
  (splitAll ((List.finRange (numFresh φ)).map (Fin.natAdd n))
    (φ.map fun C => C.map fun l => (Fin.castAdd (numFresh φ) l.1, l.2))).dedup
def StForced : Prop := ∀ (V : Type) (a : V → Bool) (y : V) (l₁ l₂ : V × Bool),
  (Holds a (forced y l₁ l₂) ↔ (a y = true ↔ a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2)) ∧ ∀ C ∈ forced y l₁ l₂, C.length ≤ 3
def StRestrict : Prop := ∀ (n : ℕ) (φ : CNF n) (b : Fin (n + numFresh φ) → Bool),
  Holds b (widthReduce φ) → Holds (fun i => b (Fin.castAdd (numFresh φ) i)) φ
def StExtend : Prop := ∀ (n : ℕ) (φ : CNF n) (a : Fin n → Bool), Holds a φ →
  ∃! b : Fin (n + numFresh φ) → Bool, Holds b (widthReduce φ) ∧ ∀ i, b (Fin.castAdd (numFresh φ) i) = a i
def StWidth : Prop := ∀ (n : ℕ) (φ : CNF n),
  SatK.IsKCNF 3 (widthReduce φ) ∧ SatK.numSat (widthReduce φ) = SatK.numSat φ ∧
    ∀ k : ℕ, (∀ C ∈ φ, C.length ≤ k) →
      numFresh φ ≤ (k - 3) * φ.length ∧ (widthReduce φ).length ≤ φ.length + 3 * ((k - 3) * φ.length)
end Eight.Width


