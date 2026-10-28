-- Prove2me | Definitions.Def_BitDFT_TapePermutation
-- name    : BitDFT_TapePermutation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T15:13:14.952639+00:00
-- url     : https://prove2.me/theorems/fdfbec29-d8aa-40aa-b308-6e4c8cb047f5
-- title:
--   Relabel a finite tape layout while preserving the read-only input tape
-- statement:
--   Given a finite permutation of the tape indices that fixes the input tape, construct a machine that executes the original finite transition table on the relabeled tapes. Logical tape j is stored on physical tape e(j), with its head relabeled in the same way. The alphabet, states and clock are unchanged. The actual input tape remains read-only. This is a finite layout adapter, not a data-copying procedure.
-- source:
--   Direct finite-tape relabeling for composing the BitDFT parser, logarithmic scanner, and binary counter on one larger fixed tape layout.

import Definitions.Def_IntMul_MultitapeModel

namespace BitDFT.TapePermutation
open IntMul

def transition (M : MultitapeTM) (e : Fin M.k ≃ Fin M.k) (q : M.K)
    (a : Fin M.k → M.Sym) : M.K × (Fin M.k → M.Sym × Move) :=
  let result := M.δ q (fun j => a (e j))
  (result.1,fun i => result.2 (e.symm i))

abbrev machine (M : MultitapeTM) (e : Fin M.k ≃ Fin M.k)
    (he : e M.inTape = M.inTape) : MultitapeTM where
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
  k := M.k
  two_le_k := M.two_le_k
  δ := transition M e
  start_preserved := by
    intro q a i hi
    simpa [transition] using M.start_preserved q (fun j => a (e j)) (e.symm i) (by simpa using hi)
  start_only_at_start := by
    intro q a i hi
    simpa [transition] using M.start_only_at_start q (fun j => a (e j)) (e.symm i) (by simpa using hi)
  halt_fixed := by
    intro a
    simp [transition,M.halt_fixed]
  input_readonly := by
    intro q a
    have hi : e.symm M.inTape = M.inTape := by apply e.injective; simpa using he.symm
    change ((M.δ q (fun j => a (e j))).2 (e.symm M.inTape)).1 = a M.inTape
    rw [hi]
    have hr := M.input_readonly q (fun j => a (e j))
    simpa only [MultitapeTM.inTape] using hr.trans (congrArg a he)

/-- Physical tape e(j) carries logical tape j, including its head position. -/
def embed (M : MultitapeTM) (e : Fin M.k ≃ Fin M.k) (he : e M.inTape = M.inTape)
    (c : M.Cfg) : (machine M e he).Cfg where
  state := c.state
  cells := fun i => c.cells (e.symm i)
  head := fun i => c.head (e.symm i)

end BitDFT.TapePermutation


