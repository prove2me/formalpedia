-- Prove2me | Definitions.Def_Autoconvolutions_BlockKeys
-- name    : Autoconvolutions_BlockKeys
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:47:45.076444+00:00
-- url     : https://prove2.me/theorems/d419fd5b-bb5a-4150-a54f-4d35739a0e81
-- title:
--   Block Keys
-- statement:
--   Definitions and structural lemmas for Block Keys, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/BlockKeys.lean

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Autoconvolutions.Blocks
open Finset
def code {m : ℕ} (D : ℕ) (a : Fin m → ℕ) : ℕ :=
  ∑ i, a i * D ^ i.val
def key {m : ℕ} (D : ℕ) (a b : Fin m → ℕ) (h : ℕ) : ℕ :=
  h + D * (code D a + code D b)
abbrev Row (m : ℕ) := ((Fin m → ℕ) × (Fin m → ℕ)) × ℕ
noncomputable def rows {m : ℕ} (I J : Finset (Fin m)) (u v D : ℕ) : Finset (Row m) := by
  classical
  exact ((I.piAntidiag u) ×ˢ (J.piAntidiag v)) ×ˢ range D
def rowKey {m : ℕ} (D : ℕ) (t : Row m) : ℕ := key D t.1.1 t.1.2 t.2
end Autoconvolutions.Blocks


