-- Prove2me | Definitions.Def_JinLib_Heavy
-- name    : JinLib_Heavy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:45:58.130722+00:00
-- url     : https://prove2.me/theorems/a7d9ea03-d23f-5374-9b3e-f9aeb9db3458
-- title:
--   Heavy
-- statement:
--   Definitions and structural lemmas for Heavy, from Juan Pablo Traverso Gianini (jtraverso/jin-triangle-free; see pinned Apache-2.0 LICENSE and source headers)'s pinned Jin's theorem on dense triangle-free graphs in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DenseTriangleFree
open SimpleGraph
def enumIndep (E : ℕ → ℕ → Bool) (P : List ℕ → Bool) : List ℕ → List ℕ → Bool
  | [], ch => P ch
  | v :: vs, ch => enumIndep E P vs ch && (ch.any (E v) || enumIndep E P vs (v :: ch))
def edgeFn (edges : List (ℕ × ℕ)) (i j : ℕ) : Bool :=
  edges.any fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)
def wsumL (ws : List ℕ) (l : List ℕ) : ℕ := (l.map fun i => ws.getD i 0).sum
def heavyTest (ws : List ℕ) (Fb Js : List (List ℕ)) (l : List ℕ) : Bool :=
  Nat.ble (29 * wsumL ws l) (10 * ws.sum) || Fb.any (fun F => F.all fun i => l.elem i) ||
    Js.any (fun J => J.all fun i => l.elem i)
def heavyCheck (ws : List ℕ) (edges : List (ℕ × ℕ)) (Fb Js : List (List ℕ)) : Bool :=
  enumIndep (edgeFn edges) (heavyTest ws Fb Js) ((List.range ws.length).filter fun i =>
    0 < ws.getD i 0) []
section Pigeonhole
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
end Pigeonhole
end DenseTriangleFree


