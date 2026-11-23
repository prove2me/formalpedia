-- Prove2me | Definitions.Def_SatSolver
-- name    : SatSolver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:40:42.008736+00:00
-- url     : https://prove2.me/theorems/48841342-54d5-472d-b2c9-368f7aae7af3
-- title:
--   Sat Solver
-- statement:
--   Definitions and structural lemmas for Sat Solver, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/SatSolver.lean

import Definitions.Def_Bdd_Sat
import Std.Sat.CNF.Basic
set_option autoImplicit true
def parseDimacs (n : Nat) [NeZero n] (lines : Array String) : Std.Sat.CNF (Fin n) :=
  Std.Sat.CNF.mk <| lines.filter (fun l => ¬l.startsWith "p" ∧ ¬l.startsWith "c")
    |>.map (fun l =>
      String.splitOn l.trimAscii.copy " "
      |>.filterMap (fun s =>
        match s.toInt? with
        | some 0 => none
        | some i =>
          let i' := ⟨i.natAbs % n, by exact Nat.mod_lt i.natAbs (Nat.pos_of_neZero n)⟩
          some ⟨i', decide (i > 0)⟩
        | none   => none)
      )
def main (args : List String) : IO Unit := do
  match args with
  | [ns, fs] =>
    try
      let handle ← (IO.FS.Handle.mk fs .read)
      let lines ← handle.lines
      let cnf := parseDimacs (ns.toNat! + 1) lines
      if Std.Sat.CNF.Unsat cnf
      then IO.println "UNSAT"
      else IO.println "SAT"
    catch e =>
      IO.println ("Error reading file " ++ fs ++ ": " ++ toString e)
  | _ => IO.println "Usage: ./SatSolver <number-of-variables> <input-file>"


