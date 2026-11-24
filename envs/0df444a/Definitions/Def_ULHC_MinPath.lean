-- Prove2me | Definitions.Def_ULHC_MinPath
-- name    : ULHC_MinPath
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:35:41.510925+00:00
-- url     : https://prove2.me/theorems/52c9dbbd-c41e-410b-9570-7c766e4233e6
-- title:
--   Min Path
-- statement:
--   Definitions and structural lemmas for Min Path, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean

import Mathlib
set_option autoImplicit true
namespace ULHC.MP
variable {α : Type}
def IsTail (mid tgt : α → Bool) (edge : α → α → Bool) : α → List α → Prop
  | x, []     => tgt x = true
  | x, y :: L => mid x = true ∧ edge x y = true ∧ IsTail mid tgt edge y L
def IsPath (src mid tgt : α → Bool) (edge : α → α → Bool) : List α → Prop
  | []     => False
  | x :: L => src x = true ∧ IsTail mid tgt edge x L
def pw (w : α → ℕ) (L : List α) : ℕ := (L.map w).sum
section Basic
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}
end Basic
def pick {β : Type} : Option (ℕ × β) → Option (ℕ × β) → Option (ℕ × β)
  | none,   b      => b
  | some a, none   => some a
  | some a, some b => if b.1 < a.1 then some b else some a
def amin {γ β : Type} (f : γ → Option (ℕ × β)) : List γ → Option (ℕ × β)
  | []      => none
  | y :: ys => pick (f y) (amin f ys)
section Argmin
variable {γ β : Type}
end Argmin
variable [DecidableEq α]
def look {β : Type} (x : α) : List (α × Option β) → Option β
  | []          => none
  | (a, v) :: tf => if a = x then v else look x tf
def step (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (T : α → Option (ℕ × List α)) (x : α) : Option (ℕ × List α) :=
  if tgt x then some (w x, [x])
  else if mid x then
    amin (fun y => if edge x y then (T y).map (fun r => (w x + r.1, x :: r.2)) else none)
      NL
  else none
def next (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) : List (α × Option (ℕ × List α)) :=
  NL.map (fun x => (x, step NL mid tgt edge w (fun y => look y tbl) x))
def layer (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ) :
    ℕ → List (α × Option (ℕ × List α))
  | 0     => []
  | k + 1 => next NL mid tgt edge w (layer NL mid tgt edge w k)
def B (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (k : ℕ) (x : α) : Option (ℕ × List α) :=
  look x (layer NL mid tgt edge w k)
def pickSrc (NL : List α) (src : α → Bool) (tbl : List (α × Option (ℕ × List α))) :
    Option (List α) :=
  (amin (fun x => if src x then look x tbl else none) NL).map Prod.snd
def minPathL (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ) :
    Option (List α) :=
  pickSrc NL src (layer NL mid tgt edge w NL.length)
section Correct
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
def srcF (x : α) : Option (ℕ × List α) :=
  if src x then B NL mid tgt edge w NL.length x else none
end Correct
section FinsetFront
variable {β : Type} [LinearOrder β] (N : Finset β) (src mid tgt : β → Bool)
  (edge : β → β → Bool) (w : β → ℕ)
def minPath : Option (List β) :=
  minPathL (N.sort (· ≤ ·)) src mid tgt edge w
end FinsetFront
end ULHC.MP


