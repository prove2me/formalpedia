-- Prove2me | Definitions.Def_Pr6453_Locality
-- name    : Pr6453_Locality
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T21:39:37.391264+00:00
-- url     : https://prove2.me/theorems/695969d7-ec3d-4f63-942e-280d964525ea
-- title:
--   PR #6453: the columns a frame event writes
-- statement:
--   Which columns a frame event writes: the move, initialisation and clear events write the frame of the column they name; the scaling and addition events write no frame at all. This is the index the per-column locality of the replay is stated with — a program that never writes a column leaves that column's frame where it was.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the guarded replay of research/p104-clean-piggyback/construct.py.

/-
PR #6453: which columns a frame event writes.
-/
import Definitions.Def_Pr6453_Frames

set_option autoImplicit false

namespace Pr6453

def Writes {n : ℕ} (e : Event n) (c : Fin n) : Prop :=
  match e with
  | .MOVE c' _ _ => c' = c
  | .INIT c' _ => c' = c
  | .CLEAR c' _ => c' = c
  | _ => False

instance {n : ℕ} (e : Event n) (c : Fin n) : Decidable (Writes e c) := by
  cases e <;> simp only [Writes] <;> infer_instance

end Pr6453


