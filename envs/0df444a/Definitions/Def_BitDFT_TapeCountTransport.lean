-- Prove2me | Definitions.Def_BitDFT_TapeCountTransport
-- name    : BitDFT_TapeCountTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T18:24:40.270361+00:00
-- url     : https://prove2.me/theorems/588609b2-e1ae-4257-a801-304b193915c6
-- title:
--   Transport a machine across an equality of tape counts
-- statement:
--   Given a machine with k tapes and a proof k=n, view the same machine as having n tapes by transporting the finite tape indices along that equality. States, alphabet, tape contents, head positions, and numerical tape indices are unchanged. This construction adds no computation.
-- source:
--   Type-correct composition of child-wrapper and scaler tape layouts.

import Definitions.Def_IntMul_MultitapeModel

namespace BitDFT.TapeCountTransport
open IntMul

def transition (M : MultitapeTM) (n : ℕ) (h : M.k = n) (q : M.K)
    (a : Fin n → M.Sym) : M.K × (Fin n → M.Sym × Move) :=
  let result := M.δ q (fun j => a (Fin.cast h j))
  (result.1,fun i => result.2 (Fin.cast h.symm i))

abbrev machine (M : MultitapeTM) (n : ℕ) (h : M.k = n) : MultitapeTM where
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
  k := n
  two_le_k := h ▸ M.two_le_k
  δ := transition M n h
  start_preserved := by
    subst n
    intro q a i hi
    simpa [transition] using M.start_preserved q a i hi
  start_only_at_start := by
    subst n
    intro q a i hi
    simpa [transition] using M.start_only_at_start q a i hi
  halt_fixed := by
    subst n
    intro a
    simp [transition,M.halt_fixed]
  input_readonly := by
    subst n
    intro q a
    simpa [transition] using M.input_readonly q a

/-- Equality transport changes only the type of tape indices, never their numerical values. -/
def embed (M : MultitapeTM) (n : ℕ) (h : M.k = n) (c : M.Cfg) : (machine M n h).Cfg where
  state := c.state
  cells := fun i => c.cells (Fin.cast h.symm i)
  head := fun i => c.head (Fin.cast h.symm i)

end BitDFT.TapeCountTransport


