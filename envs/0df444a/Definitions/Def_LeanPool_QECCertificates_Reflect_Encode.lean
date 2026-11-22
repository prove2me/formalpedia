-- Prove2me | Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
-- name    : LeanPool_QECCertificates_Reflect_Encode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:41:32.112217+00:00
-- url     : https://prove2.me/theorems/1f1bcddb-babd-4ac4-9eb2-d9c9e63cdcfd
-- title:
--   Encode
-- statement:
--   Definitions and structural lemmas for Encode, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates.LRAT
def dotS (σ : Assign) : List Nat → Bool
  | [] => false
  | j :: s => σ j ^^ dotS σ s
def cntS (σ : Assign) (l : List Nat) : Nat := (l.filter (fun t => σ t)).length
def xorStepClauses (cur x nxt : Nat) : List Clause :=
  [[(cur, false), (x, false), (nxt, false)],
   [(cur, false), (x, true), (nxt, true)],
   [(cur, true), (x, false), (nxt, true)],
   [(cur, true), (x, true), (nxt, false)]]
def xorChainAux : List Nat → Bool → Nat → Nat → List Clause × Nat
  | [], want, cur, c => ([[(cur, want)]], c)
  | x :: rest, want, cur, c =>
      let (tl, c') := xorChainAux rest want c (c + 1)
      (xorStepClauses cur x c ++ tl, c')
def xorChain (xs : List Nat) (want : Bool) (start : Nat) : List Clause × Nat :=
  match xs with
  | [] => ([], start)
  | x₀ :: rest => xorChainAux rest want x₀ start
def SlotOK (s : Nat → Nat → Option Nat) (k : Nat) : Prop :=
  ∀ i j, s i j = none ↔ ¬(1 ≤ j ∧ j ≤ min i (k + 1))
def slotClauses (s : Nat → Nat → Option Nat) (i j x : Nat) : List Clause :=
  match s (i - 1) j, s (i - 1) (j - 1), s i j with
  | some a, some b, some si =>
      [[(a, false), (si, true)],
       [(b, false), (x, false), (si, true)],
       [(si, false), (a, true), (x, true)],
       [(si, false), (a, true), (b, true)]]
  | some a, none, some si =>
      [[(a, false), (si, true)],
       [(x, false), (si, true)],
       [(si, false), (a, true), (x, true)]]
  | none, some b, some si =>
      [[(b, false), (x, false), (si, true)],
       [(si, false), (x, true)],
       [(si, false), (b, true)]]
  | none, none, some si =>
      [[(x, false), (si, true)],
       [(si, false), (x, true)]]
  | _, _, none => []
def rowClauses (s : Nat → Nat → Option Nat) (k i x : Nat) : List Clause :=
  (List.range (min i (k + 1))).flatMap (fun j' => slotClauses s i (j' + 1) x)
def atMostKAux (s : Nat → Nat → Option Nat) (k : Nat) (pre suf : List Nat) : List Clause :=
  match suf with
  | [] =>
      if k + 1 ≤ pre.length then
        (match s pre.length (k + 1) with
         | some v => [[(v, false)]]
         | none => [])
      else []
  | x :: rest => rowClauses s k (pre.length + 1) x ++ atMostKAux s k (pre ++ [x]) rest
def atMostK (s : Nat → Nat → Option Nat) (k : Nat) (xs : List Nat) : List Clause :=
  atMostKAux s k [] xs
def prodClauses (c n : Nat) : List Clause :=
  (List.range n).flatMap (fun j =>
    [[(c + j, false), (j, true)],
     [(c + j, false), (n + j, true)],
     [(c + j, true), (j, false), (n + j, false)]])
def chainsFrom (f : Nat → Nat) : List (List Nat) → Nat → List Clause × Nat
  | [], c => ([], c)
  | r :: rest, c =>
      let (cl, c') := xorChain (r.map f) false c
      let (cl', c'') := chainsFrom f rest c'
      (cl ++ cl', c'')
def slotBase (k i : Nat) : Nat := ((List.range i).map (fun i' => min i' (k + 1))).sum
def slotVar (c k i j : Nat) : Option Nat :=
  if 1 ≤ j ∧ j ≤ min i (k + 1) then some (c + slotBase k i + (j - 1)) else none
def kerClauses (Rker : List (List Nat)) (n : Nat) : List Clause :=
  (chainsFrom (fun j => j) Rker (2 * n)).1
def c1Of (Rker : List (List Nat)) (n : Nat) : Nat :=
  (chainsFrom (fun j => j) Rker (2 * n)).2
def pairClauses (Rker Rpair : List (List Nat)) (n : Nat) : List Clause :=
  (chainsFrom (fun j => n + j) Rpair (c1Of Rker n)).1
def c2Of (Rker Rpair : List (List Nat)) (n : Nat) : Nat :=
  (chainsFrom (fun j => n + j) Rpair (c1Of Rker n)).2
def prodVars (Rker Rpair : List (List Nat)) (n : Nat) : List Nat :=
  (List.range n).map (fun j => c2Of Rker Rpair n + j)
def xwClauses (Rker Rpair : List (List Nat)) (n : Nat) : List Clause :=
  (xorChain (prodVars Rker Rpair n) true (c2Of Rker Rpair n + n)).1
def c3Of (Rker Rpair : List (List Nat)) (n : Nat) : Nat :=
  (xorChain (prodVars Rker Rpair n) true (c2Of Rker Rpair n + n)).2
def buildPair (Rker Rpair : List (List Nat)) (n k : Nat) : CNF :=
  ((kerClauses Rker n ++ pairClauses Rker Rpair n) ++
    (prodClauses (c2Of Rker Rpair n) n ++ xwClauses Rker Rpair n)) ++
  atMostK (slotVar (c3Of Rker Rpair n) k) k (List.range n)
end QECCertificates.LRAT


