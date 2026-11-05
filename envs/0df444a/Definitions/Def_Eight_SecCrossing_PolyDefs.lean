-- Prove2me | Definitions.Def_Eight_SecCrossing_PolyDefs
-- name    : Eight_SecCrossing_PolyDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:07:07.081129+00:00
-- url     : https://prove2.me/theorems/e1af8768-0b2e-4eae-8f95-732c4e774369
-- title:
--   Sec Crossing Poly Defs
-- statement:
--   Definitions and structural lemmas for Sec Crossing Poly Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PolyDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Alg_Data
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace Eight
open Groundwork PaddedDescent.F ClauseBound.Alg
def blkAt (w : List Bool) (j : ℕ) : Block := (w.getD j false, w.getD (j + 1) false, w.getD (j + 2) false)
def blkL (w : List Bool) (s : ℕ) : Block := blkAt w (3 * s)
abbrev FourL : Type := List Bool × List Bool × List Bool × List Bool
def rAt (q : FourL) (s : ℕ) : ℤ := Rb (blkL q.1 s) (blkL q.2.1 s) (blkL q.2.2.1 s) (blkL q.2.2.2 s)
def cAt (q : FourL) (s : ℕ) : ℤ := Cb (blkL q.1 s) (blkL q.2.1 s) (blkL q.2.2.1 s) (blkL q.2.2.2 s)
def tL (q : FourL) : ℕ := tOf q.1.length
def mulStep (r c : ℤ) (l : List ℤ) : List ℤ :=
  (List.range (l.length + 1)).map fun j => r * l.getD j 0 + c * (0 :: l).getD j 0
def mulUpTo (q : FourL) (n : ℕ) : List ℤ :=
  (List.range n).foldl (fun l s => mulStep (rAt q s) (cAt q s) l) [1]
def mulOut (q : FourL) : List ℤ := mulUpTo q (tL q)
def aMul (p : ℕ × FourL) : ℤ := (mulOut p.2).getD p.1 0
def longCap (tr : Bool) (t i : ℕ) : ℕ := bif tr then 7 * t - 3 * i else 4 * t + 3 * i
def useLong (tr : Bool) (lam i : ℕ) : Bool := decide (longCap tr (tOf lam) i ≤ 2 * lam)
def wide (tr : Bool) (Q : List Bool) (s : ℕ) : Bool := Q.getD s false != tr
def off (tr : Bool) (Q : List Bool) (s : ℕ) : ℕ := 3 * s + 3 * (List.range s).countP (wide tr Q)
def topAt (tr : Bool) (Q w a b : List Bool) (s : ℕ) : ℤ :=
  if wide tr Q s = true then (if blkL a s = blkAt w (off tr Q s) ∧ blkL b s = blkAt w (off tr Q s + 3) then 1 else 0)
  else psi (blkAt w (off tr Q s)) (blkL a s) (blkL b s)
def botAt (tr : Bool) (Q w a b : List Bool) (s : ℕ) : ℤ :=
  if wide tr Q s = true then Rb (blkAt w (off tr Q s)) (blkL a s) (blkAt w (off tr Q s + 3)) (blkL b s)
  else psi (blkAt w (off tr Q s)) (blkL b s) (blkL a s)
def fTop (q : Bool × ℕ × List Bool × List Bool × List Bool) : ℤ :=
  if useLong q.1 q.2.2.1.length q.2.1 = true then
    (if (q.2.2.2.2.take (tOf q.2.2.1.length)).count true = q.2.1 then
      prodL (tOf q.2.2.1.length) (topAt q.1 (q.2.2.2.2.take (tOf q.2.2.1.length)) (q.2.2.2.2.drop (tOf q.2.2.1.length)) q.2.2.1 q.2.2.2.1)
    else 0)
  else (if q.2.2.1 ++ q.2.2.2.1 = q.2.2.2.2 then 1 else 0)
def fBot (q : Bool × ℕ × List Bool × List Bool × List Bool) : ℤ :=
  if useLong q.1 q.2.2.1.length q.2.1 = true then
    (if (q.2.2.2.2.take (tOf q.2.2.1.length)).count true = q.2.1 then
      prodL (tOf q.2.2.1.length) (botAt q.1 (q.2.2.2.2.take (tOf q.2.2.1.length)) (q.2.2.2.2.drop (tOf q.2.2.1.length)) q.2.2.1 q.2.2.2.1)
    else 0)
  else bif q.1 then aMul (q.2.1, q.2.2.2.2.take q.2.2.1.length, q.2.2.1, q.2.2.2.2.drop q.2.2.1.length, q.2.2.2.1)
    else aMul (q.2.1, q.2.2.2.2.take q.2.2.1.length, q.2.2.2.2.drop q.2.2.1.length, q.2.2.1, q.2.2.2.1)
def eightF : PiecesF where
  cnt _ lam := tOf lam + 1
  d _ lam := 2 ^ tOf lam
  cap tr _ lam i := bif tr then ccol lam i else crow lam i
  top q := fTop (q.1.2, q.2.1.2, q.2.2.1, q.2.2.2.1, q.2.2.2.2)
  bot q := fBot (q.1.2, q.2.1.2, q.2.2.1, q.2.2.2.1, q.2.2.2.2)
  need _ _ := 0
  bits _ lam := tOf lam
  m := 1
def StAMul : Prop := ∀ (lam i : ℕ) (x y u v : Pieces.Bits lam), aMul (i, List.ofFn x, List.ofFn y, List.ofFn u, List.ofFn v) = A lam i x y u v
def StFact : Prop := ∀ lam, 1 ≤ lam → ∀ i ≤ tOf lam,
  (∀ x y u v : Pieces.Bits lam, A lam i x y u v = ∑ θ : Pieces.Bits (crow lam i),
    fTop (false, i, List.ofFn x, List.ofFn y, List.ofFn θ) * fBot (false, i, List.ofFn u, List.ofFn v, List.ofFn θ)) ∧
  (∀ x y u v : Pieces.Bits lam, A lam i x y u v = ∑ θ : Pieces.Bits (ccol lam i),
    fTop (true, i, List.ofFn x, List.ofFn u, List.ofFn θ) * fBot (true, i, List.ofFn y, List.ofFn v, List.ofFn θ)) ∧
  ∀ tr (a b : Pieces.Bits lam) (θ : List Bool),
    |fTop (tr, i, List.ofFn a, List.ofFn b, θ)| ≤ 2 ^ tOf lam ∧ |fBot (tr, i, List.ofFn a, List.ofFn b, θ)| ≤ 2 ^ tOf lam
def StPoly : Prop := PolyT aMul ∧ PolyT fTop ∧ PolyT fBot
def StKeeps : Prop := eightF.Keeps
end Eight


