-- Prove2me | Definitions.Def_TunnellMap_KernelArith
-- name    : TunnellMap_KernelArith
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:36:01.105138+00:00
-- url     : https://prove2.me/theorems/7469e2fe-df40-4c92-b34a-7694c23a3fb3
-- title:
--   Kernel Arith
-- statement:
--   Definitions and structural lemmas for Kernel Arith, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean

import Mathlib
set_option autoImplicit true
namespace TunnellMap
def sqrtBSAux (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if mid * mid ≤ n then sqrtBSAux n fuel mid hi else sqrtBSAux n fuel lo mid
def natSqrtK (n : ℕ) : ℕ := sqrtBSAux n (n + 1) 0 (n + 1)
def isqrtK (z : ℤ) : ℤ := (natSqrtK z.toNat : ℤ)
variable {α : Type*}
def insertB (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if le a b then a :: b :: l else b :: insertB le a l
def isortB (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => insertB le a (isortB le l)
end TunnellMap


