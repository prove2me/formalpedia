-- Prove2me | Definitions.Def_ParityChecksStatement
-- name    : ParityChecksStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:13.295039+00:00
-- url     : https://prove2.me/theorems/c3ddc721-c60b-4513-ab84-713129001dee
-- title:
--   Parity Checks Statement
-- statement:
--   Definitions and structural lemmas for Parity Checks Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/ParityChecksStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
set_option autoImplicit false
section
section
namespace ParityChecks
open Finset
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
def ev (q : ℕ) : ℤ := if Even q then 1 else 0
def sig (i : ℕ) : ℤ := if i = 0 then 1 else (-1) ^ i * 2 ^ (i - 1)
def eta (V : X → Finset E) (nb : ℕ) (ξ : X) : ℤ := ∑ S ∈ (V ξ).powerset with #S ≤ nb, (-1) ^ #S
def Good (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E) : Prop := ∀ ξ, nb < #(V ξ) → ∃ j < r, Odd #(Λ j ∩ V ξ)
def tuples (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J : Finset (Fin r)) (M : ℕ) (ξ : X) : Finset (Fin r → Finset E) :=
  (Fintype.piFinset fun j : Fin r => if j ∈ J then (Λ j ∩ V ξ).powerset else {∅}).filter fun S => ∑ j, #(S j) ≤ M
section Potential
variable (V : X → Finset E) (nb r : ℕ)
def omega (ξ : X) : ℕ := (#(V ξ)).choose (nb + 1)
def pr : ℚ := 1 / nb
def undRow (j : ℕ) (D : Finset E) (j' : ℕ) : ℕ := if j' < j then 0 else if j' = j then #D else Fintype.card E
def undCol (j : ℕ) (D : Finset E) (e : E) : ℕ := (r - 1 - j) + if e ∈ D then 1 else 0
def Upar (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ :=
  (5 / 8) ^ (r - 1 - j) * ∑ ξ, (omega V nb ξ : ℚ) * (∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) *
    (1 / 2 * (1 + (-1) ^ #(Λ j ∩ V ξ) * (1 - 2 * pr nb) ^ #(D ∩ V ξ)))
def Uinc (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ :=
  ((∑ j' ∈ range r, #(Λ j') : ℕ) + pr nb * (∑ j' ∈ range r, undRow j D j' : ℕ)) / (8 * pr nb * Fintype.card E * r)
def Urow (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ :=
  1 / (8 * r) * ∑ j' ∈ range r, (2 : ℚ) ^ #(Λ j') / (1 + pr nb) ^ (Fintype.card E - undRow j D j')
def Ucol (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ :=
  1 / (8 * Fintype.card E) * ∑ e : E, (2 : ℚ) ^ #{j' ∈ range r | e ∈ Λ j'} / (1 + pr nb) ^ (r - undCol r j D e)
def Ups (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ := Upar V nb r j Λ D + Uinc nb r j Λ D + Urow nb r j Λ D + Ucol nb r j Λ D
def tUpar (i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℚ :=
  (5 / 8) ^ (r - 1 - j) * ∑ ξ, (omega V nb ξ : ℚ) * (∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) *
    (1 / 2 * (1 + (-1) ^ #(Λ j ∩ V ξ) * ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * ((#(D ∩ V ξ)).choose i : ℚ)))
def Aint (j : ℕ) (Λ : ℕ → Finset E) : ℤ := ∑ ξ, (omega V nb ξ : ℤ) * ∏ j' ∈ range j, ev #(Λ j' ∩ V ξ)
def Bint (i j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : ℤ :=
  ∑ ξ, (omega V nb ξ : ℤ) * ((#(D ∩ V ξ)).choose i : ℤ) * (-1) ^ #(Λ j ∩ V ξ) * ∏ j' ∈ range j, ev #(Λ j' ∩ V ξ)
structure IsState (j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) : Prop where
  j_lt : j < r
  later : ∀ j', j < j' → Λ j' = ∅
  disj : Disjoint (Λ j) D
def putIn (j : ℕ) (Λ : ℕ → Finset E) (e : E) : ℕ → Finset E := Function.update Λ j (insert e (Λ j))
end Potential
structure ChoiceByPotential : Prop where
  /-- all four terms are nonnegative -/
  nonneg : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E), 2 ≤ nb →
    0 ≤ Upar V nb r j Λ D ∧ 0 ≤ Uinc nb r j Λ D ∧ 0 ≤ Urow nb r j Λ D ∧ 0 ≤ Ucol nb r j Λ D
  /-- ½(1 + (1 − 2p)^v) < 5/8 for v > nb -/
  five_eighths : ∀ nb v : ℕ, 2 ≤ nb → nb < v → 1 / 2 * (1 + (1 - 2 * pr nb) ^ v) < 5 / 8
  /-- at the start the potential is at most 1/2 -/
  start : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r : ℕ), 2 ≤ nb → 1 ≤ r → 1 ≤ Fintype.card E →
    (5 / 8 : ℚ) ^ r * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) ≤ 1 / 8 → Ups V nb r 0 (fun _ => ∅) univ ≤ 1 / 2
  /-- one decision: p·Υ^in + (1 − p)·Υ^out = Υ -/
  martingale : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) (e : E),
    2 ≤ nb → IsState r j Λ D → e ∈ D →
    pr nb * Ups V nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Ups V nb r j Λ (D.erase e) = Ups V nb r j Λ D
  /-- from one check to the next the potential does not grow -/
  boundary : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E),
    2 ≤ nb → IsState r j Λ ∅ → j + 1 < r → Ups V nb r (j + 1) Λ univ ≤ Ups V nb r j Λ ∅
  /-- what Υ < 1 gives -/
  structure_ : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E),
    2 ≤ nb → 1 ≤ Fintype.card E → IsState r j Λ D → Ups V nb r j Λ D < 1 →
    ((∑ j' ∈ range r, #(Λ j') : ℕ) : ℚ) < 8 * pr nb * Fintype.card E * r ∧
    (∀ j' < r, (2 : ℚ) ^ #(Λ j') < 8 * r * (1 + pr nb) ^ Fintype.card E) ∧
    ∀ e : E, (2 : ℚ) ^ #{j' ∈ range r | e ∈ Λ j'} < 8 * Fintype.card E * (1 + pr nb) ^ r
  /-- in the final state Υ < 1 makes the checks good -/
  final : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E),
    2 ≤ nb → IsState r (r - 1) Λ ∅ → Ups V nb r (r - 1) Λ ∅ < 1 → Good V nb r Λ
  /-- the error of the truncated series carries over to the potential -/
  approx : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) (ε : ℚ),
    (∀ u ≤ Fintype.card E, |(1 - 2 * pr nb) ^ u - ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * (u.choose i : ℚ)| ≤ ε) →
    |tUpar V nb r i₀ j Λ D - Upar V nb r j Λ D| ≤ 1 / 2 * ε * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ)
  /-- the truncated potential through the integers A and B_i -/
  compute : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E),
    tUpar V nb r i₀ j Λ D = (5 / 8) ^ (r - 1 - j) * (1 / 2) * ((Aint V nb j Λ : ℚ) + ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * (Bint V nb i j Λ D : ℚ))
  /-- A and B_i are small -/
  abs_le : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb i j : ℕ) (Λ : ℕ → Finset E) (D : Finset E),
    |Aint V nb j Λ| ≤ (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) ∧
    |Bint V nb i j Λ D| ≤ (Fintype.card X * (Fintype.card E).choose (nb + 1) * (Fintype.card E).choose i : ℕ)
end ParityChecks


