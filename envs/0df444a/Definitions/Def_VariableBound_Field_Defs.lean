-- Prove2me | Definitions.Def_VariableBound_Field_Defs
-- name    : VariableBound_Field_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:45:36.141434+00:00
-- url     : https://prove2.me/theorems/d0831f2c-370e-4ebc-8e23-7fe84fab4c22
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_StepMachines_Prog_Chunks
set_option autoImplicit false
section
section
namespace VariableBound.Fld
open Groundwork
def xorW (x y : List Bool) : List Bool := (x.zip y).map fun p => xor p.1 p.2
def zeroW (g : List Bool) : List Bool := g.map fun _ => false
def oneW (g : List Bool) : List Bool := true :: g.tail.map fun _ => false
def mulX (g w : List Bool) : List Bool :=
  if w.getLast?.getD false then xorW ((false :: w).take w.length) g else (false :: w).take w.length
def mulW (g x y : List Bool) : List Bool :=
  y.foldr (fun b c => if b then xorW x (mulX g c) else mulX g c) (zeroW g)
def powW (g u : List Bool) (e : ℕ) : List Bool := (List.range e).foldl (fun c _ => mulW g c u) (oneW g)
def ipW (x y : List Bool) : Bool := decide (((x.zip y).countP fun p => p.1 && p.2) % 2 = 1)
def wordsL (s : ℕ) : List (List Bool) := (List.range (2 ^ s)).map (toWord s)
def irrW (g : List Bool) : Bool :=
  (wordsL g.length).all fun x => decide (x = zeroW g) || (wordsL g.length).any fun y => decide (mulW g x y = oneW g)
def modW (s : ℕ) : List Bool := ((wordsL s).find? irrW).getD []
def gamW (m a : ℕ) (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : List ℕ :=
  (List.range m).filter fun E =>
    (((xorW (mulW g u.1 (toWord g.length E)) u.2.1).take (a - 1)).all fun b => !b) && ipW (powW g u.2.2.1 E) u.2.2.2
def sD (m : ℕ) : ℕ := Nat.clog 2 (16 * m)
def famD (m a : ℕ) : List (List ℕ) :=
  ((wordsL (sD m) ×ˢ wordsL (sD m) ×ˢ wordsL (sD m) ×ˢ wordsL (sD m)).map (gamW m a (modW (sD m)))).filter fun l =>
    decide (2 ^ a * l.length ≤ 16 * m)
def setD (m : ℕ) (l : List ℕ) : Finset (Fin m) := Finset.univ.filter fun E => E.val ∈ l
def StFamD : Prop := ∀ m a : ℕ, 1 ≤ a → 2 ^ a ≤ m →
  famD m a ≠ [] ∧ (famD m a).length < (32 * m) ^ 4 ∧
  (∀ l ∈ famD m a, l.Pairwise (· < ·) ∧ l.Nodup ∧ ∀ E ∈ l, E < m) ∧
  AppVariables.IsFamily (2 ^ a) (Finset.univ : Finset (Fin (famD m a).length)) fun i => setD m ((famD m a).get i)
def StCertFamD : Prop := ∀ (α : Type) [Enc α] (m a : α → ℕ), Unary m → Unary a → PolyT fun x => famD (m x) (a x)
end VariableBound.Fld


