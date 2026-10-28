-- Prove2me | Definitions.Def_BitDFT_TapeExtension
-- name    : BitDFT_TapeExtension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:34:04.867391+00:00
-- url     : https://prove2.me/theorems/c3b77f10-6153-4b14-b0cc-fcc712637f0e
-- title:
--   Add parked work tapes without slowing a multitape machine
-- statement:
--   Extend any fixed multitape machine with a fixed number of additional tapes. The finite transition table applies the original transition to its original tapes and leaves all extra heads and cells unchanged. The state set and alphabet are unchanged. The extra tapes may store arbitrary caller data during a simulated run.
-- source:
--   Direct finite-table construction in the existing IntMul.MultitapeTM model. Intended for preserving wrapper workspace while executing existing machine components.

import Definitions.Def_IntMul_MultitapeModel

namespace BitDFT.TapeExtension
open IntMul

def oldTape (M : MultitapeTM) (r : ℕ) (i : Fin M.k) : Fin (M.k+r) :=
  ⟨i.val, by omega⟩

def transition (M : MultitapeTM) (r : ℕ) (q : M.K) (a : Fin (M.k+r) → M.Sym) :
    M.K × (Fin (M.k+r) → M.Sym × Move) :=
  let result := M.δ q (fun i => a (oldTape M r i))
  (result.1, fun i => if h : i.val < M.k then result.2 ⟨i.val,h⟩ else (a i,.stay))

abbrev machine (M : MultitapeTM) (r : ℕ) : MultitapeTM where
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
  k := M.k+r
  two_le_k := by have := M.two_le_k; omega
  δ := transition M r
  start_preserved := by
    intro q a i hi
    dsimp only [transition]
    split
    · rename_i h
      exact M.start_preserved q (fun j => a (oldTape M r j)) ⟨i.val,h⟩ hi
    · simp [hi]
  start_only_at_start := by
    intro q a i hi
    dsimp only [transition]
    split
    · rename_i h
      exact M.start_only_at_start q (fun j => a (oldTape M r j)) ⟨i.val,h⟩ hi
    · exact hi
  halt_fixed := by
    intro a
    simp only [transition, M.halt_fixed]
    congr 1
    funext i
    split <;> rfl
  input_readonly := by
    intro q a
    have hk : 0 < M.k := by have := M.two_le_k; omega
    simp only [transition, hk, dite_true]
    exact M.input_readonly q (fun j => a (oldTape M r j))

/-- Extra tapes may contain arbitrary caller data and parked heads. -/
def embed (M : MultitapeTM) (r : ℕ)
    (extraCells : Fin (M.k+r) → ℕ → M.Sym) (extraHeads : Fin (M.k+r) → ℕ)
    (c : M.Cfg) : (machine M r).Cfg where
  state := c.state
  cells := fun i => if h : i.val < M.k then c.cells ⟨i.val,h⟩ else extraCells i
  head := fun i => if h : i.val < M.k then c.head ⟨i.val,h⟩ else extraHeads i

end BitDFT.TapeExtension


