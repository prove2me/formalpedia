-- Prove2me | Definitions.Def_ULHC_Timed_Strips
-- name    : ULHC_Timed_Strips
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:09:46.895295+00:00
-- url     : https://prove2.me/theorems/d8b3de0e-1379-4ed6-a7fc-add45b747794
-- title:
--   Strips
-- statement:
--   Definitions and structural lemmas for Strips, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
set_option autoImplicit true
namespace ULHC.T
open Finset
def latOKT (F : Finset Edge) (c : Pt) (s : Side) (j : ℕ) : TimeM Bool := do
  let a ← memT (lat1 (cellJ c s j) s) F
  let b ← memT (lat2 (cellJ c s j) s) F
  tick 3
  pure ((a == (j % 2 == 1)) && (b == (j % 2 == 1)))
def stripScanT (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) : ℕ → ℕ → TimeM (Option ℕ)
  | 0, _ => do
    tick 1
    pure none
  | k + 1, j => do
    let a ← isCellT V (cellJ c s j)
    let b ← latOKT F c s j
    let f ← memT (front (cellJ c s j) s) F
    tick 3
    if a && b then
      if f == (j % 2 == 0) then pure (some (j + 1)) else stripScanT V F c s k (j + 1)
    else pure none
def stripLenT (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) : TimeM (Option ℕ) := do
  let b ← memT (back c s) F
  let n ← cardT V
  tick 1
  if b then stripScanT V F c s n 0 else pure none
def allStripsT (V : Finset Pt) (F : Finset Edge) : TimeM (Finset StripSpec) := do
  let Cs ← filterT (isCellT V) V
  biUnionT (fun c => biUnionT (fun s => do
    let o ← stripLenT V F c s
    pure (optStrips c s o)) sidesF) Cs
def flipT (G : Finset Edge) (u : Pt) : TimeM (Finset Edge) := symmDiffT G (cellE u)
def validBT (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) : TimeM Bool := do
  let A ← allStripsT V F
  let a ← memT σ A
  let b ← connBT V F (back1 σ.c σ.s) (front1 σ.c σ.s)
  tick 2
  pure (a && !b)
def sideOffBT (b c : StripSpec) : TimeM Bool := do
  let R ← rangeT c.n
  let R' ← rangeT (b.n - 1)
  lallT (fun j => lallT (fun i => allT (fun e => do
    let m ← memT e (cellE (cellJ b.c b.s i))
    pure (!m)) (cellE (cellJ c.c c.s j))) R') R
def midBT (b : StripSpec) (z : Pt) : TimeM Bool := do
  let R ← rangeT (b.n - 2)
  lanyT (fun j => do
    tick 4
    pure (eqN (j % 2) 1 && (eqP z (front1 (cellJ b.c b.s j) b.s) ||
      eqP z (front2 (cellJ b.c b.s j) b.s)))) R
def endOffBT (b c : StripSpec) : TimeM Bool := do
  let r ← allT (fun e => do
    let m ← memT e (cellE (endCell b))
    pure (!m)) (cellE (endCell c))
  tick 3
  pure (!(c.n % 2 == 0) || r)
def notEndBT (b c : StripSpec) : TimeM Bool := do
  let R ← rangeT c.n
  lallT (fun j => do
    tick 3
    pure (!eqP (cellJ c.c c.s j) (endCell b))) R
def cr2BT (V : Finset Pt) (G : Finset Edge) (b c : StripSpec) : TimeM Bool := do
  let Gu ← flipT G (endCell b)
  let A ← allStripsT V Gu
  let a ← memT c A
  let s1 ← sideOffBT b c
  let s2 ← notEndBT b c
  let s3 ← endOffBT b c
  let m1 ← midBT b (back1 c.c c.s)
  let m2 ← midBT b (front1 c.c c.s)
  let k1 ← connBT V G (back1 c.c c.s) (front1 c.c c.s)
  let Gu' ← flipT G (endCell b)
  let k2 ← connBT V Gu' (back1 c.c c.s) (front1 c.c c.s)
  tick 12
  pure (((2 ≤ b.n : Bool) && eqN (b.n % 2) 0) && a && s1 && s2 && s3 && !m1 && !m2 && k1 && !k2)
def chainOKBT (b c : StripSpec) : TimeM Bool := do
  let R ← rangeT c.n
  lallT (fun j => allT (fun x => do
    let m ← memT x (cellE (endCell b))
    tick 4
    pure (!m || (eqN j 0 && (eqE x (lat1 (endCell b) b.s) || eqE x (lat2 (endCell b) b.s)))))
    (cellE (cellJ c.c c.s j))) R
def gsrcT (V : Finset Pt) (G : Finset Edge) (x : Node) : TimeM Bool := do
  let v ← validBT V G x.σ
  tick 2
  pure ((x.pos == 1) && v)
def gedgeT (V : Finset Pt) (G : Finset Edge) (x y : Node) : TimeM Bool := do
  let a ← cr2BT V G x.σ y.σ
  let b ← chainOKBT x.σ y.σ
  tick 3
  pure ((y.pos == min (x.pos + 1) 3) && a && b)
def candT (V : Finset Pt) (G : Finset Edge) : TimeM (Finset StripSpec) := do
  let A ← allStripsT V G
  let Cs ← filterT (isCellT V) V
  let Bs ← biUnionT (fun u => do
    let Gu ← flipT G u
    allStripsT V Gu) Cs
  unionT A Bs
def candNT (V : Finset Pt) (G : Finset Edge) : TimeM (Finset Node) := do
  let C ← candT V G
  biUnionT (fun σ => imageT (fun p => pure (Node.mk σ p)) ({1, 2, 3} : Finset ℕ)) C
end ULHC.T


