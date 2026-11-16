-- Prove2me | Definitions.Def_SemiStreamMWM_Supplement_Incremental
-- name    : SemiStreamMWM_Supplement_Incremental
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:35:19.05851+00:00
-- url     : https://prove2.me/theorems/e4d43433-7f09-49b2-a4cd-19be6dc1f445
-- title:
--   The incremental update protocol: insertions, total time and explicit matchings on the word RAM
-- statement:
--   This definition fixes the **incremental update model** in which Theorem 1.2 of the paper is stated: a word-RAM program receives an $n$-vertex graph, initially empty, followed by edge insertions one at a time, and after each insertion it must report a matching.
--
--   1. **Insertion sequences.** An insertion sequence on the vertex set $\{0,\dots,n-1\}$ is a list of pairs $(u_1,v_1),\dots,(u_m,v_m)$ with weights $w:\binom{V}{2}\to\mathbb N$. It is *valid* with weight bound $W$ when $u_i\neq v_i$, no unordered pair $\{u_i,v_i\}$ occurs twice, and $1\le w_{u_iv_i}\le W$ for every $i$. The graph $G_i$ has the first $i$ pairs as edges; $G_0$ is empty.
--   2. **Protocol.** The program runs on the published word RAM (`DynBrooks`), started with the header words $n, W, K$ pending, until its first *completed state* (blocked at a read with nothing pending). For the $i$-th insertion the three words $u_i+1,\ v_i+1,\ w_{u_iv_i}$ are delivered, and the machine runs to its next completed state. The program never sees insertions in advance and is never told $m$.
--   3. **Time.** The time of a stage is the number of executed instructions from its starting configuration to the next completed state ($\infty$ if none is reached, and $\infty$ for every later stage). The **total time** through $m$ insertions is the sum of the times of the initialization and of the $m$ insertions.
--   4. **Explicit matching.** The output is append-only. It is read as pairs of vertex labels $(a,b)$, $a,b\in\{1,\dots,n\}$; each pair toggles the edge $\{a-1,b-1\}$ in or out of the reported set, starting from the empty set. A set $D$ is a $(1-\varepsilon)$-MWM of $G$ under $w$ when it is a matching of $G$ (edges of $G$, pairwise vertex-disjoint) of weight at least $(1-\varepsilon)\mu_w(G)$.
--
--   These objects let Theorem 1.2 count every write to the output as a step, so the cost of changing the reported matching is part of the total time, as in the paper.
--
--   **Formalization Note** The machine, the initial configuration, the decoding of output pairs and the maximum weight $\mu_w$ are the published `DynBrooks_Machine`, `SemiStreamMWM.StreamModel` and `SemiStreamMWM.Graph`. A deterministic program runs on the all-zero coin tape.
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), §1 pp.3–4 (dynamic matching, Theorem 1.2); §1.3 p.8 (computational model); §5 p.21

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_StreamModel

set_option autoImplicit false

open Classical

namespace SemiStreamMWM.Supplement

/-! # The incremental update protocol on the word RAM

J. Chen, *Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs:
A Unified Framework* (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), §1 p.3 ("an
algorithm must maintain an explicit (1 − ε)-MWM after each update"), p.4 (Theorem 1.2: "starting
from the empty n-vertex graph … through m edge insertions in total time …"), §1.3 p.8 ("the standard
word RAM with Θ(log n)-bit words"), §5 p.21 ("we start with an empty graph on n vertices and
maintain an explicit (1 − ε)-MWM after edge insertions").

**Formalization Note.**
* The machine is the published `DynBrooks` word RAM, used exactly as in `SemiStreamMWM.StreamModel`.
  A deterministic program (no `coin` instruction) is run on the all-zero coin tape.
* **Protocol.** The run starts from `initConfig w hdr` with the header words `hdr` pending and runs to
  its first completed state (blocked at a `read` with nothing pending, `DynBrooks.complete`). For the
  `i`-th insertion the words `ops i` are delivered with `DynBrooks.feed` and the machine runs to the
  next completed state. The machine cannot look ahead and is never told the number of insertions.
* **Time.** The time of a stage is `DynBrooks.time` from its starting configuration (the number of
  executed instructions, `⊤` if no completed state is ever reached); the total time is the sum over
  the initialization and every insertion. A stage after one that never completes has time `⊤`.
* **Explicit matching.** The output tape is append-only. It is read as a list of pairs of vertex
  labels `a, b ∈ 1..n`; each pair toggles the edge `{a − 1, b − 1}` in or out of the reported set.
  An odd number of words or a label outside `1..n` decodes to nothing. Every written word is an
  executed (charged) instruction, so every change of the reported matching is paid for in time. -/

/-- The graph on `Fin n` whose edges are the pairs of `es` (diagonal pairs are dropped). -/
def insGraph {n : ℕ} (es : List (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ p ∈ es, s(p.1, p.2) = e}

/-- `es` with weights `wt` is a valid insertion sequence with weights in `[1, W]`: no pair is a
loop, no unordered pair is inserted twice, and every inserted edge has weight in `[1, W]`. -/
def IsInsertionSeq {n : ℕ} (W : ℕ) (wt : Sym2 (Fin n) → ℕ) (es : List (Fin n × Fin n)) : Prop :=
  (∀ p ∈ es, p.1 ≠ p.2 ∧ 1 ≤ wt s(p.1, p.2) ∧ wt s(p.1, p.2) ≤ W) ∧
    (es.map fun p => s(p.1, p.2)).Nodup

/-- The words of one insertion `{u, v}` of weight `wt {u, v}`: `u + 1, v + 1, wt {u, v}`
(vertex labels `1..n`). -/
def insWords {n : ℕ} (wt : Sym2 (Fin n) → ℕ) (p : Fin n × Fin n) : List ℕ :=
  [p.1.val + 1, p.2.val + 1, wt s(p.1, p.2)]

/-- The completed configuration after the initialization (`i = 0`) and after the first `i`
updates (`i ≥ 1`), where update `j` (0-based) delivers the words `ops j`; `none` once some stage
never reaches a completed state. The coin tape is all zero. -/
noncomputable def incConfig (P : DynBrooks.Program) (w : ℕ) (hdr : List ℕ) (ops : ℕ → List ℕ) :
    ℕ → Option (DynBrooks.Config w)
  | 0 => DynBrooks.complete P (fun _ => 0) (initConfig w hdr)
  | i + 1 => (incConfig P w hdr ops i).bind fun c =>
      DynBrooks.complete P (fun _ => 0) (DynBrooks.feed c (ops i))

/-- The configuration at which stage `i` starts: `initConfig w hdr` for the initialization
(`i = 0`), and the completed configuration after `i − 1` updates with the words `ops (i − 1)`
delivered for `i ≥ 1`. -/
noncomputable def incStart (P : DynBrooks.Program) (w : ℕ) (hdr : List ℕ) (ops : ℕ → List ℕ) :
    ℕ → Option (DynBrooks.Config w)
  | 0 => some (initConfig w hdr)
  | i + 1 => (incConfig P w hdr ops i).map fun c => DynBrooks.feed c (ops i)

/-- The number of steps of stage `i` (the initialization for `i = 0`, update `i` for `i ≥ 1`):
`DynBrooks.time` from its starting configuration, and `⊤` if an earlier stage never completed. -/
noncomputable def stageTime (P : DynBrooks.Program) (w : ℕ) (hdr : List ℕ) (ops : ℕ → List ℕ)
    (i : ℕ) : ℕ∞ :=
  match incStart P w hdr ops i with
  | none => ⊤
  | some c => DynBrooks.time P (fun _ => 0) c

/-- The total time of the initialization and the first `m` updates. -/
noncomputable def totalTime (P : DynBrooks.Program) (w : ℕ) (hdr : List ℕ) (ops : ℕ → List ℕ)
    (m : ℕ) : ℕ∞ :=
  ∑ i ∈ Finset.range (m + 1), stageTime P w hdr ops i

/-- Decode an append-only output `[a₁, b₁, …, a_k, b_k]` (labels in `1..n`) into the set of edges
obtained by toggling `{a₁ − 1, b₁ − 1}`, then `{a₂ − 1, b₂ − 1}`, …, starting from the empty set;
`none` for an odd length or a label outside `1..n`. -/
def toggleDecode (n : ℕ) (out : List ℕ) : Option (Finset (Sym2 (Fin n))) :=
  (decodePairs n out).map fun M =>
    M.foldl (fun S p => symmDiff S {s(p.1, p.2)}) ∅

/-- The decoded set `D` is a matching of `G` of weight at least `(1 − ε) µ_w(G)`: it consists of
edges of `G`, no two sharing a vertex (`SemiStreamMWM.IsMatching`), and its weight under `wt` is at
least `(1 − ε)` times the maximum weight `µ_w(G)` (`SemiStreamMWM.mwm`). -/
def IsApproxMWMSet {n : ℕ} (G : SimpleGraph (Fin n)) (wt : Sym2 (Fin n) → ℕ) (ε : ℝ)
    (D : Finset (Sym2 (Fin n))) : Prop :=
  ∃ M : Finset G.edgeSet, IsMatching G M ∧ M.map (Function.Embedding.subtype _) = D ∧
    (1 - ε) * (mwm G wt : ℝ) ≤ ∑ e ∈ M, (wt e.1 : ℝ)

end SemiStreamMWM.Supplement


