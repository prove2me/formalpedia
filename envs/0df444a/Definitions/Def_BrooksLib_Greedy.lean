-- Prove2me | Definitions.Def_BrooksLib_Greedy
-- name    : BrooksLib_Greedy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:25:20.269954+00:00
-- url     : https://prove2.me/theorems/21452474-e282-455c-8b21-a7d2c9e412bb
-- title:
--   Greedy
-- statement:
--   Definitions and structural lemmas for Greedy, from Juan Pablo Traverso Gianini (jtraverso/brooks; see pinned Apache-2.0 LICENSE and source headers)'s pinned Erdos-Rubin-Taylor degree-choosability, block-cut trees, and Brooks' theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Greedy.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace BrooksTheorem
namespace Aux
variable {V : Type*}
def Proper {k : ℕ} (H : SimpleGraph V) (f : V → Fin k) : Prop :=
  ∀ u v, H.Adj u v → f u ≠ f v
variable [Fintype V]
open Classical in
/-- The finset of neighbours of `v` (classical decidability). -/
noncomputable def nb (H : SimpleGraph V) (v : V) : Finset V := univ.filter (H.Adj v)
def near (H : SimpleGraph V) (P : Finset V) (T : V → Prop) : ℕ → V → Prop
  | 0, w => T w
  | n + 1, w => ∃ u, H.Adj w u ∧ u ∉ P ∧ near H P T n u
end Aux
end BrooksTheorem


