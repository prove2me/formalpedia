-- Prove2me | Definitions.Def_SemiStreamMWM_StreamModel
-- name    : SemiStreamMWM_StreamModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:14:52.574204+00:00
-- url     : https://prove2.me/theorems/81a568ff-63c1-461e-b891-15dc1093072c
-- title:
--   §1, §1.3 — multi-pass semi-streaming on the word RAM: passes, space, output
-- statement:
--   The semi-streaming model of the paper: an algorithm makes passes over an arbitrary-order stream of the edges and is charged for the bits of memory it uses, on the standard word RAM.
--
--   A program is a finite list of word-RAM instructions, fixed before the word size $w$. The input of one pass is a header (the number of vertices $n$, and, as needed, the weight bound $W$ and $K=\lceil1/\varepsilon\rceil$), then every edge once in an arbitrary orientation as two vertex labels in $1,\dots,n$ (followed by its weight in a weighted stream), then the end marker $0$. The run starts with the first pass pending and counts passes: whenever the machine has read every word and waits for more, the same stream, in the same order, is delivered again. Its **space** at any moment is $w$ times the number of memory cells written so far. It is **deterministic** if it uses no random words. It **outputs a matching** if it halts with output $u_1,v_1,\dots,u_k,v_k$ whose pairs are edges of $G$ with no repeated vertex.
--
--   All machine-level statements of the mission (Lemmas 1.6, 4.4, 4.5 and Theorem 1.1) are stated in this model.
--
--   **Formalization Note** The machine is the published `DynBrooks_Machine`; its `read` blocks when no word is pending, which is what ends a pass. Output words are write-only and are not charged. $\ell(m)=\max\{1,\lceil\log_2(m+1)\rceil\}$ is the number of bits of $m$.
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), §1 p.3 (semi-streaming model); §1.3 p.8 (computational model)

import Mathlib
import Definitions.Def_DynBrooks_Machine

open Classical

namespace SemiStreamMWM

/-! # The multi-pass semi-streaming model on the word RAM

J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), §1 p.3 ("In the semi-streaming
model, an algorithm makes passes over an arbitrary-order stream of edges using O(n log^{O(1)} n) bits
of space"), §1.3 p.8 ("We use the standard word RAM with Θ(log n)-bit words"), footnote 1 p.3.

**Formalization Note.** The paper names the word RAM and no instruction set. A program is a
`DynBrooks.Program` (the published `DynBrooks_Machine`): a finite instruction list, fixed before the
word size, with memory `ℕ → BitVec w`; `read` stores the next pending input word and blocks when
none is pending; `write` appends to a write-only output; every assignment records its cell in
`written`. **Space** in bits is `w · |written|`, so every cell the run ever uses is charged.
**Passes:** a run starts with the first pass's words pending and pass count `1`; whenever the
machine is blocked at a `read` with nothing pending (`DynBrooks.IsCompleted`), the same words are
delivered again and the count increases. A pass therefore ends only after every word of it has
been read, and the stream order is the same in every pass. The words of a pass are a header,
the edges with vertex labels `1..n` (and, for weighted inputs, the weight), and the sentinel `0`.
**Deterministic** means the program has no `coin` instruction; the coin tape is then irrelevant
and is fixed to `0`. A run **halts** when it reaches a `halt` instruction. The output
`[u₁, v₁, …, u_k, v_k]` decodes to the list of label pairs; it is not charged. -/

/-- `ℓ(m) = max{1, ⌈log₂(m + 1)⌉}`: the bits needed to hold the number `m`. -/
def ell (m : ℕ) : ℕ := max 1 (Nat.clog 2 (m + 1))

/-- `es` lists every edge of `G` exactly once, in either orientation, in an arbitrary order. -/
def IsEdgeStream {n : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) : Prop :=
  (es.map fun p => s(p.1, p.2)).Nodup ∧
    ∀ e, e ∈ es.map (fun p => s(p.1, p.2)) ↔ e ∈ G.edgeSet

/-- The words of one pass of an unweighted stream: `n`, `K = ⌈1/ε⌉`, the edges (labels `1..n`), `0`. -/
def mcmWords {n : ℕ} (K : ℕ) (es : List (Fin n × Fin n)) : List ℕ :=
  [n, K] ++ es.flatMap (fun p => [p.1.val + 1, p.2.val + 1]) ++ [0]

/-- The words of one pass of a weighted stream: `n`, `W`, `K`, the edges with their weights, `0`. -/
def mwmWords {n : ℕ} (W K : ℕ) (wt : Sym2 (Fin n) → ℕ) (es : List (Fin n × Fin n)) : List ℕ :=
  [n, W, K] ++ es.flatMap (fun p => [p.1.val + 1, p.2.val + 1, wt s(p.1, p.2)]) ++ [0]

/-- The words of one pass of a weighted stream without an accuracy parameter: `n`, `W`, the edges
with their weights, `0`. -/
def gwWords {n : ℕ} (W : ℕ) (wt : Sym2 (Fin n) → ℕ) (es : List (Fin n × Fin n)) : List ℕ :=
  [n, W] ++ es.flatMap (fun p => [p.1.val + 1, p.2.val + 1, wt s(p.1, p.2)]) ++ [0]

/-- The start of a run: program counter `0`, all cells zero, nothing written, nothing output. -/
def initConfig (w : ℕ) (inp : List ℕ) : DynBrooks.Config w where
  pc := 0
  mem := fun _ => 0
  input := inp
  coinPos := 0
  output := []
  written := ∅

/-- The program uses no randomness: it contains no `coin` instruction. -/
def IsDeterministic (P : DynBrooks.Program) : Prop :=
  ∀ i, DynBrooks.Instr.coin i ∉ P

/-- One step of a multi-pass run, on states (configuration, passes started so far): a completed
state receives the words of the next pass; otherwise the machine makes one step. -/
noncomputable def passStep {w : ℕ} (P : DynBrooks.Program) (inp : List ℕ)
    (s : DynBrooks.Config w × ℕ) : DynBrooks.Config w × ℕ :=
  if DynBrooks.IsCompleted P s.1 then (DynBrooks.feed s.1 inp, s.2 + 1)
  else (DynBrooks.step P (fun _ => 0) s.1, s.2)

/-- The state after `t` steps of the multi-pass run of `P` with word size `w` on the pass `inp`. -/
noncomputable def passRun (P : DynBrooks.Program) (w : ℕ) (inp : List ℕ) (t : ℕ) :
    DynBrooks.Config w × ℕ :=
  (passStep P inp)^[t] (initConfig w inp, 1)

/-- The machine is at a `halt` instruction. -/
def IsHalted {w : ℕ} (P : DynBrooks.Program) (c : DynBrooks.Config w) : Prop :=
  P[c.pc]? = some DynBrooks.Instr.halt

/-- Space in bits: the word size times the number of cells ever written. -/
def spaceBits (w : ℕ) (c : DynBrooks.Config w) : ℕ := w * c.written.card

/-- Decode an output `[u₁, v₁, …, u_k, v_k]` with labels in `1..n` into the pairs
`(u₁ − 1, v₁ − 1), …`; `none` for an odd length or a label outside `1..n`. -/
def decodePairs (n : ℕ) : List ℕ → Option (List (Fin n × Fin n))
  | [] => some []
  | [_] => none
  | a :: b :: rest =>
      if h : 1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n then
        (decodePairs n rest).map fun M => (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩) :: M
      else none

/-- The list of pairs is a matching of `G`: every pair is an edge, and no vertex occurs twice. -/
def IsMatchingList {n : ℕ} (G : SimpleGraph (Fin n)) (M : List (Fin n × Fin n)) : Prop :=
  (∀ p ∈ M, G.Adj p.1 p.2) ∧ (M.flatMap fun p => [p.1, p.2]).Nodup

/-- The weight of a list of pairs. -/
def listWeight {n : ℕ} (wt : Sym2 (Fin n) → ℕ) (M : List (Fin n × Fin n)) : ℕ :=
  (M.map fun p => wt s(p.1, p.2)).sum

end SemiStreamMWM


