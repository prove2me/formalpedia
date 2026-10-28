-- Prove2me | Definitions.Def_BitDFT_AlphabetEmbedding
-- name    : BitDFT_AlphabetEmbedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:47:01.252428+00:00
-- url     : https://prove2.me/theorems/4e158067-db6c-48d7-9e1b-e0ce80d5937e
-- title:
--   Exact-clock embedding of a machine into a larger finite alphabet
-- statement:
--   An injective alphabet map preserves blank, permanent marker, zero, one, and separator. The lifted machine uses the target alphabet while retaining the original finite states and tape count. Decoding maps encoded symbols back to their originals; symbols outside the image decode to blank. The transition table preserves native input literally and freezes all symbols in its halt state, so its machine invariants hold even on symbols outside the image.
-- source:
--   Alphabet compatibility adapter for composing the request preprocessor with an arbitrary finite Fourier-machine caller.

import Definitions.Def_IntMul_MultitapeModel

noncomputable section
namespace BitDFT.AlphabetEmbedding
open IntMul

structure Map (M N : MultitapeTM) where
  encode : M.Sym ↪ N.Sym
  blank : encode M.blank = N.blank
  marker : encode M.startSym = N.startSym
  zero : encode M.zero = N.zero
  one : encode M.one = N.one
  sep : encode M.sep = N.sep

def decode {M N : MultitapeTM} (e : Map M N) (a : N.Sym) : M.Sym := by
  classical
  exact if h : ∃ b, e.encode b = a then Classical.choose h else M.blank

theorem decode_encode {M N : MultitapeTM} (e : Map M N) (a : M.Sym) : decode e (e.encode a) = a := by
  classical
  unfold decode
  split
  · apply e.encode.injective
    exact Classical.choose_spec (by assumption)
  · rename_i h
    exact False.elim (h ⟨a,rfl⟩)

private theorem blank_ne_marker (M : MultitapeTM) : M.blank ≠ M.startSym := by
  have h := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or] at h
  aesop

theorem decode_marker_iff {M N : MultitapeTM} (e : Map M N) (a : N.Sym) :
    decode e a = M.startSym ↔ a = N.startSym := by
  classical
  constructor
  · intro h
    unfold decode at h
    split at h
    · rename_i he
      have hh := Classical.choose_spec he
      rw [h,e.marker] at hh
      exact hh.symm
    · exact False.elim (blank_ne_marker M h)
  · intro h
    rw [h,← e.marker,decode_encode]

def transition {M N : MultitapeTM} (e : Map M N) (q : M.K) (a : Fin M.k → N.Sym) :
    M.K × (Fin M.k → N.Sym × Move) := by
  classical
  exact if q = M.qHalt then (q,fun i => (a i,.stay)) else
    let r := M.δ q (fun i => decode e (a i))
    (r.1,fun i => (if i = M.inTape then a i else e.encode (r.2 i).1,(r.2 i).2))

abbrev machine {M N : MultitapeTM} (e : Map M N) : MultitapeTM where
  Sym := N.Sym
  blank := N.blank
  startSym := N.startSym
  zero := N.zero
  one := N.one
  sep := N.sep
  syms_distinct := N.syms_distinct
  K := M.K
  qStart := M.qStart
  qHalt := M.qHalt
  start_ne_halt := M.start_ne_halt
  k := M.k
  two_le_k := M.two_le_k
  δ := transition e
  start_preserved := by
    intro q a i hi
    classical
    simp only [transition]
    split
    · simp [hi]
    · have hm : decode e (a i) = M.startSym := (decode_marker_iff e _).mpr hi
      have h := M.start_preserved q (fun j => decode e (a j)) i hm
      constructor
      · simp [h.1,e.marker,hi]
      · exact h.2
  start_only_at_start := by
    intro q a i hi
    classical
    simp only [transition]
    split
    · exact hi
    · have hm : decode e (a i) ≠ M.startSym := fun h => hi ((decode_marker_iff e _).mp h)
      have h := M.start_only_at_start q (fun j => decode e (a j)) i hm
      by_cases hi0 : i = M.inTape
      · simpa only [hi0,if_true] using hi
      · simp only [hi0,if_false]
        intro he
        apply h
        apply e.encode.injective
        exact he.trans e.marker.symm
  halt_fixed := by intro a; simp [transition]
  input_readonly := by
    intro q a
    classical
    simp only [transition]
    split
    · rfl
    · rfl

def embed {M N : MultitapeTM} (e : Map M N) (c : M.Cfg) : (machine e).Cfg where
  state := c.state
  cells := fun i p => e.encode (c.cells i p)
  head := c.head

end BitDFT.AlphabetEmbedding


