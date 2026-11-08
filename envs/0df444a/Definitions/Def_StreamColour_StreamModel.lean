-- Prove2me | Definitions.Def_StreamColour_StreamModel
-- name    : StreamColour_StreamModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:51.63237+00:00
-- url     : https://prove2.me/theorems/9b1ba2ac-08cd-4dbc-94e2-5ee4a749d025
-- title:
--   §3 — edge streams, space in bits, and a colouring output
-- statement:
--   The input model of §3. The vertex set is labelled, each edge of $G$ appears exactly once in the stream, in either orientation, and $n,\Delta,k$ are known before the stream.
--
--   A run begins with all memory cells zero and nothing written. The **space** of a configuration, in bits, is the word size times the number of memory cells ever written; this includes all workspace used after the stream. The run **outputs a proper $q$-colouring** of $G$ if it reaches a halt instruction, after some number of steps, with an output list of length $n$ whose entries lie in $\{1,\dots,q\}$ and differ across every edge of $G$.
--
--   **Formalization Note** The paper names no machine. Programs are those of the published `DynBrooks_Machine`. A word is written only by executing an instruction, so a post-stream computation cannot use memory free of charge. In the stream, labels are $1,\dots,n$ and the word $0$ ends the stream.
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), §3, p.20 (PDF 22)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_StreamColour_Params

namespace StreamColour

/-! # The streaming input, space, and a colouring output

Chakraborty, Chatterjee, Kundu, Mishra (STOC 2027 submission, sha256 31a813b3…), §3, p.20 (PDF 22):
"The graph has labelled vertex set [n] and maximum degree at most the supplied bound ∆ ≤ n − 1. The
parameters n, ∆, and k are known before the stream. Each edge appears once in an insertion-only stream"
and "Space is measured in bits and includes postprocessing workspace. Computation time is unrestricted."

**Formalization Note.** The paper names no machine. A program is a `DynBrooks.Program` (finite list of
instructions, fixed before the word size) of word size `w`. Its `read` consumes the input once, its
`write` appends to an unreadable output, and all computation goes through memory cells, so "space
including postprocessing workspace" is `w * written.card`: `w` bits for each cell ever assigned. Vertices
are `Fin n` inside statements and labels `1..n` in the stream, so the word `0` is free and ends the stream.
Each edge occurs exactly once, in either orientation; the number of edges is not given. Colours are `1..q`
in the output. Output words are write-only and not charged. A run that reports failure, halts with a bad
list, or never halts does not output a colouring. -/

/-- `es` lists each edge of `G` exactly once, in either orientation. -/
def IsEdgeStream {n : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) : Prop :=
  (es.map fun p => s(p.1, p.2)).Nodup ∧
    ∀ e, e ∈ es.map (fun p => s(p.1, p.2)) ↔ e ∈ G.edgeSet

/-- The words of an edge list: labels `1..n`. -/
def edgeWords {n : ℕ} (es : List (Fin n × Fin n)) : List ℕ :=
  es.flatMap fun p => [p.1.val + 1, p.2.val + 1]

/-- The input of a colouring program: the parameters, the edges, the sentinel `0`. -/
def streamInput {n : ℕ} (Δ k : ℕ) (es : List (Fin n × Fin n)) : List ℕ :=
  [n, Δ, k] ++ edgeWords es ++ [0]

/-- The start of a run: program counter `0`, all cells zero, nothing written, nothing output. -/
def initConfig (w : ℕ) (input : List ℕ) : DynBrooks.Config w where
  pc := 0
  mem := fun _ => 0
  input := input
  coinPos := 0
  output := []
  written := ∅

/-- Space in bits: the word size times the number of cells ever written. -/
def spaceBits (w : ℕ) (c : DynBrooks.Config w) : ℕ := w * c.written.card

/-- `out` is a proper `q`-colouring of `G`: its `v`-th entry is the colour of `v`, with colours in
`1..q`, and adjacent vertices have different entries. -/
def IsProperOutput {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (out : List ℕ) : Prop :=
  out.length = n ∧ (∀ x ∈ out, 1 ≤ x ∧ x ≤ q) ∧ ∀ u v, G.Adj u v → out[u.val]? ≠ out[v.val]?

/-- The run from `c` on tape `ω` halts, after some number of steps, with a proper `q`-colouring. -/
def OutputsColouring {n w : ℕ} (P : DynBrooks.Program) (ω : ℕ → BitVec w) (c : DynBrooks.Config w)
    (q : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ t, P[(DynBrooks.run P ω c t).pc]? = some DynBrooks.Instr.halt ∧
    IsProperOutput G q (DynBrooks.run P ω c t).output

end StreamColour


