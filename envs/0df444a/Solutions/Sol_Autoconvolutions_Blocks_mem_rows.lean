-- Prove2me | solution 1 for Autoconvolutions.Blocks.mem_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:48:19.21582+00:00
-- url     : https://prove2.me/submissions/78098ef2-0c2a-453d-8d36-b06d75fab67c

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockKeys

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Blocks
open Finset
namespace Autoconvolutions.Blocks
theorem _root_.solution {m u v D : ℕ} {I J : Finset (Fin m)} {t : Row m} :
    t ∈ rows I J u v D ↔ t.1.1 ∈ I.piAntidiag u ∧
      t.1.2 ∈ J.piAntidiag v ∧ t.2 < D := by
  classical
  simp [rows, and_assoc]
end Autoconvolutions.Blocks
