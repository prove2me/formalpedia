-- Prove2me | Definitions.Def_K230_enum
-- name    : K230_enum
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T21:13:35.749934+00:00
-- url     : https://prove2.me/theorems/9b6eb383-c2af-44d7-84cb-61b6c5ccd500
-- title:
--   K230: abstract proof enumerator
-- statement:
--   The six-register abstract proof enumerator: a state records the proof list, next proof, top formula, formula stack, and two parameters; `enumStep` executes one command (MP, DROP, NIP, or a gated axiom bundle), `run` iterates it, and `enum230Halts`/`haltsFrom` express reaching a halting NIP. `seed230` is the actual nonzero initial search state. Ports `Enum230.v`, `Seed230.v`, and `halts_from` from `L1_Comp230.v`.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/logic/Enum230.v

import Definitions.Def_K230_codes
namespace K230
structure State where
  pl : Nat
  np : Nat
  tw : Nat
  ws : Nat
  d : Nat
  h : Nat
def s0 : State := ⟨0, 0, 0, 0, 0, 0⟩
def axStack (a h b c u t w : Nat) : Nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a c) (P (rho7 a b c) (P (rho8 a b c u) (P (wal a h) (P t w)))))))))
def gate (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle230 a b c
def enumStep (s : State) : Option State :=
  let (pl1, np1) := if s.pl = 0 then (s.np, s.np + 1) else (s.pl - 1, s.np)
  let (ac, pl2) := unP pl1
  let (x, pl3) := unP pl2
  let d1 := s.d + x
  if ac = 0 then
    some (if wim s.tw d1 = s.h then ⟨pl3, np1, d1, P 0 s.ws, d1, 0⟩ else ⟨pl3, np1, 0, s.ws, d1, 0⟩)
  else if ac = 1 then some ⟨pl3, np1, s.h, P s.tw s.ws, d1, s.h⟩
  else if ac = 2 then
    if s.h = 1 then none else let (h1, w1) := unP s.ws; some ⟨pl3, np1, s.tw, w1, d1, h1⟩
  else
    let c := ac - 3
    let (y, pl4) := unP pl3
    let (u, pl5) := unP pl4
    let b := s.h + y
    some ⟨pl5, np1, gate d1 b c, axStack d1 s.h b c u s.tw s.ws, 0, 0⟩
def run : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => match enumStep s with | some s' => run n s' | none => none
def enum230Halts : Prop := ∃ n s, run n s0 = some s ∧ enumStep s = none
def seed230 : State := ⟨0, 3, 0, 0, 3, 0⟩
def haltsFrom (s : State) : Prop := ∃ n s', run n s = some s' ∧ enumStep s' = none
end K230


