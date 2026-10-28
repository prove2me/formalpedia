-- Prove2me | Definitions.Def_BitDFT_WorkRelocation
-- name    : BitDFT_WorkRelocation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T17:55:38.064556+00:00
-- url     : https://prove2.me/theorems/704436f5-1607-4073-b218-03f3ffcaec5d
-- title:
--   Relocate a machine onto work tapes while parking the original input
-- statement:
--   For any finite multitape machine M, add a new read-only input tape and shift each original tape index upward by one. The original state and transition are retained on the shifted tapes, while the new input tape remains stationary. An embedding specifies the complete starting configuration; it does not perform free copying or initialization.
-- source:
--   Output-scaling construction for the integer-multiplication to finite-precision DFT transfer.

import Definitions.Def_IntMul_MultitapeModel

namespace BitDFT.WorkRelocation
open IntMul

def oldTape (M : MultitapeTM) (i : Fin M.k) : Fin (M.k+1) := ⟨i.val+1,by omega⟩
def innerTape (M : MultitapeTM) (i : Fin (M.k+1)) (h : i.val ≠ 0) : Fin M.k := ⟨i.val-1,by omega⟩

theorem old_inner (M : MultitapeTM) (i : Fin (M.k+1)) (h : i.val ≠ 0) :
    oldTape M (innerTape M i h) = i := by
  apply Fin.ext
  simp only [oldTape,innerTape]
  omega

theorem inner_old (M : MultitapeTM) (i : Fin M.k) :
    innerTape M (oldTape M i) (by simp [oldTape]) = i := by
  apply Fin.ext
  simp [oldTape,innerTape]

def transition (M : MultitapeTM) (q : M.K) (a : Fin (M.k+1) → M.Sym) :
    M.K × (Fin (M.k+1) → M.Sym × Move) :=
  let result := M.δ q (fun j => a (oldTape M j))
  (result.1,fun i => if h : i.val = 0 then (a i,.stay) else result.2 (innerTape M i h))

abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := M.Sym
  blank := M.blank
  startSym := M.startSym
  zero := M.zero
  one := M.one
  sep := M.sep
  syms_distinct := M.syms_distinct
  K := M.K
  qStart := M.qStart
  qHalt := M.qHalt
  start_ne_halt := M.start_ne_halt
  k := M.k+1
  two_le_k := by have := M.two_le_k; omega
  δ := transition M
  start_preserved := by
    intro q a i hi
    dsimp only [transition]
    split
    · simp [hi]
    · rename_i h
      exact M.start_preserved q (fun j => a (oldTape M j)) (innerTape M i h) (by simpa only [old_inner] using hi)
  start_only_at_start := by
    intro q a i hi
    dsimp only [transition]
    split
    · exact hi
    · rename_i h
      exact M.start_only_at_start q (fun j => a (oldTape M j)) (innerTape M i h) (by simpa only [old_inner] using hi)
  halt_fixed := by
    intro a
    simp only [transition,M.halt_fixed]
    congr 1
    funext i
    split
    · rfl
    · simp only [old_inner]
  input_readonly := by intro q a; rfl

def embed (M : MultitapeTM) (rootCells : ℕ → M.Sym) (rootHead : ℕ) (c : M.Cfg) : (machine M).Cfg where
  state := c.state
  cells := fun i => if h : i.val = 0 then rootCells else c.cells (innerTape M i h)
  head := fun i => if h : i.val = 0 then rootHead else c.head (innerTape M i h)

end BitDFT.WorkRelocation


