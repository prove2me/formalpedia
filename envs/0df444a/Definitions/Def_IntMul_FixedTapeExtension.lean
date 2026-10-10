-- Prove2me | Definitions.Def_IntMul_FixedTapeExtension
-- name    : IntMul_FixedTapeExtension
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T23:54:05.661378+00:00
-- url     : https://prove2.me/theorems/a8dcc496-ff6c-4cdd-b5d2-ae29e7cd9263
-- title:
--   Exact-time finite machine extension retaining one additional fixed tape
-- statement:
--   A finite k-tape machine is extended to k+1 tapes with exactly the same finite alphabet and finite control. Each old transition reads the unchanged old tape indices and applies its original writes and moves there; the added tape retains its scanned cell and stays. The old input/output origins and global-marker constraints are unchanged. The proof-side embedding combines an arbitrary old configuration with arbitrary saved cells and head position on the additional tape. No position or tape content is supplied as an external oracle to the transition table.
-- source:
--   Original exact-clock tape extension for saved continuation records in integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.FixedTapeExtension

/-- Old tape indices are unchanged; exactly one fixed tape is appended. -/
def oldTape (M : MultitapeTM) (j : Fin M.k) : Fin (M.k + 1) := ⟨j.val,by have := j.isLt; omega⟩
def extraTape (M : MultitapeTM) : Fin (M.k + 1) := ⟨M.k,by omega⟩
def innerTape (M : MultitapeTM) (i : Fin (M.k + 1)) (hi : i.val < M.k) : Fin M.k := ⟨i.val,hi⟩

private theorem old_inner (M : MultitapeTM) (i : Fin (M.k + 1)) (hi : i.val < M.k) :
    oldTape M (innerTape M i hi) = i := by apply Fin.ext; rfl

noncomputable def transition (M : MultitapeTM) (q : M.K) (a : Fin (M.k + 1) → M.Sym) :
    M.K × (Fin (M.k + 1) → M.Sym × Move) :=
  let r := M.δ q (fun j => a (oldTape M j))
  (r.1,fun i => if h : i.val < M.k then r.2 (innerTape M i h) else (a i,.stay))

/-- One additional fixed tape, retained verbatim during every original
transition. The alphabet, finite states and physical step count are unchanged. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
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
  k := M.k + 1
  two_le_k := by have := M.two_le_k; omega
  δ := transition M
  start_preserved := by
    intro q a i ha
    by_cases hi : i.val < M.k
    · simp only [transition,dif_pos hi]
      apply M.start_preserved
      simpa only [old_inner] using ha
    · simp only [transition,dif_neg hi,ha]
      exact ⟨trivial,by decide⟩
  start_only_at_start := by
    intro q a i ha
    by_cases hi : i.val < M.k
    · simp only [transition,dif_pos hi]
      apply M.start_only_at_start
      simpa only [old_inner] using ha
    · simpa only [transition,dif_neg hi] using ha
  halt_fixed := by
    intro a
    simp only [transition,M.halt_fixed]
    apply Prod.ext
    · rfl
    · funext i
      by_cases hi : i.val < M.k
      · simp only [dif_pos hi,old_inner]
      · simp only [dif_neg hi]
  input_readonly := by
    intro q a
    have hi : (0 : ℕ) < M.k := by have := M.two_le_k; omega
    simp only [transition,dif_pos hi,innerTape]
    change ((M.δ q (fun j => a (oldTape M j))).2 ⟨0,hi⟩).1 = a ⟨0,by omega⟩
    exact M.input_readonly q (fun j => a (oldTape M j))

/-- Exact old configuration plus arbitrary saved extra-tape cells and head.
These proof parameters are never supplied to delta. -/
noncomputable def embed (M : MultitapeTM) (base : (machine M).Cfg) (c : M.Cfg) : (machine M).Cfg where
  state := c.state
  cells := fun i => if h : i.val < M.k then c.cells (innerTape M i h) else base.cells i
  head := fun i => if h : i.val < M.k then c.head (innerTape M i h) else base.head i

end IntMul.FixedTapeExtension


