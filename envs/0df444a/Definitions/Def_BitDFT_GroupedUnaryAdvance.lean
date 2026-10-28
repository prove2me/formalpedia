-- Prove2me | Definitions.Def_BitDFT_GroupedUnaryAdvance
-- name    : BitDFT_GroupedUnaryAdvance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T05:23:06.915981+00:00
-- url     : https://prove2.me/theorems/0357881e-85ec-4bf4-923f-ab6bd7efc6f2
-- title:
--   Advance by grouping unary counter marks
-- statement:
--   A finite-state multitape controller skips the first five consecutive one symbols on a counter tape. It then advances a designated source head once for every next group of three one symbols. At the first non-one symbol after complete groups, it performs one final source move and halts. The controller preserves all tape contents. On a counter of length 3r+5 followed by a non-one symbol, it advances the source head by r+1 cells.
-- source:
--   This machine converts the accepted log scanner's unary output of length 3·lg(n)+5 into a head displacement of lg(n)+1, the offset required to skip the multiplier product's leading zero prefix.

import Definitions.Def_BitDFT_MachineSequence
import Mathlib.Tactic.DeriveFintype

noncomputable section
namespace BitDFT.GroupedUnaryAdvance
open IntMul

inductive State | skip (i : Fin 5) | group (i : Fin 3) | halt
  deriving DecidableEq, Fintype

def emit {N : MultitapeTM} (source counter : Fin N.k) (a : Fin N.k → N.Sym)
    (next : State) (moveSource moveCounter : Bool) :=
  (next, fun i => (a i, if (moveSource && i = source) || (moveCounter && i = counter)
    then Move.right else Move.stay))

def transition (N : MultitapeTM) (source counter : Fin N.k) (q : State)
    (a : Fin N.k → N.Sym) : State × (Fin N.k → N.Sym × Move) := by
  classical
  exact match q with
  | .halt => emit source counter a .halt false false
  | .skip j =>
      if a counter = N.one then
        emit source counter a (if h : j.val = 4 then .group 0 else .skip ⟨j.val+1, by have hj := j.isLt; omega⟩) false true
      else emit source counter a .halt false false
  | .group j =>
      if a counter = N.one then
        if h : j.val = 2 then emit source counter a (.group 0) true true
        else emit source counter a (.group ⟨j.val+1, by have hj := j.isLt; omega⟩) false true
      else if j.val = 0 then emit source counter a .halt true false
      else emit source counter a .halt false false

private theorem transition_symbol (N : MultitapeTM) (source counter : Fin N.k)
    (q : State) (a : Fin N.k → N.Sym) (i : Fin N.k) :
    ((transition N source counter q a).2 i).1 = a i := by
  cases q <;> simp [transition, emit] <;> split_ifs <;> rfl

private theorem transition_not_left (N : MultitapeTM) (source counter : Fin N.k)
    (q : State) (a : Fin N.k → N.Sym) (i : Fin N.k) :
    ((transition N source counter q a).2 i).2 ≠ .left := by
  cases q <;> simp [transition, emit] <;> split_ifs
  all_goals
    by_cases hS : i = source
    · by_cases hC : i = counter
      · have hSC : source = counter := hS.symm.trans hC
        simp [hS, hC, hSC]
      · by_cases hSC : source = counter <;> simp [hS, hC, hSC]
    · by_cases hC : i = counter
      · by_cases hSC : counter = source <;> simp [hS, hC, hSC]
      · simp [hS, hC]

def control (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) : BitDFT.MachineSequence.Controller N where
  K := State
  entry := .skip 0
  exit := .halt
  distinct := by decide
  transition := transition N source counter
  marker := by
    intro q a i hi
    constructor
    · rw [transition_symbol]
      exact hi
    · exact transition_not_left N source counter q a i
  noMarker := by
    intro q a i hi
    rw [transition_symbol]
    exact hi
  frozen := by
    intro a
    rfl
  readonly := by
    intro q a
    exact transition_symbol N source counter q a N.inTape

abbrev machine (N : MultitapeTM) (source counter : Fin N.k) (hsc : source ≠ counter) :=
  (control N source counter hsc).machine

def frame (N : MultitapeTM) (source counter : Fin N.k) (hsc : source ≠ counter)
    (base : N.Cfg) (q : State) (sourceHead counterHead : ℕ) :
    (machine N source counter hsc).Cfg :=
  ⟨q, base.cells,
    Function.update (Function.update base.head source sourceHead) counter counterHead⟩

end BitDFT.GroupedUnaryAdvance


