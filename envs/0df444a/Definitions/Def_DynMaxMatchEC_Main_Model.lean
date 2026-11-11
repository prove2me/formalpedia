-- Prove2me | Definitions.Def_DynMaxMatchEC_Main_Model
-- name    : DynMaxMatchEC_Main_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:01:48.577631+00:00
-- url     : https://prove2.me/theorems/e97ba20d-1f8e-453d-a8e8-f058d684b647
-- title:
--   Edge updates, change logs, FAIL, maximal matchings, and the adaptive interaction of a word-RAM program with a configuration-seeing adversary
-- statement:
--   **Machine.** Programs are those of the published word RAM `DynBrooks_Machine`: instructions act on words of $w$ bits, `coin` stores the next word of a uniformly random coin tape $\omega:\mathbb N\to\{0,1\}^w$, `read` stores the next pending input word and *blocks* when none is pending, `write` appends a word to the output, `halt` stops; every executed instruction costs one step. A configuration blocked at `read` with no pending input is **completed**. The update words are those of `DynBrooks_Protocol`: insertion of $uv$ is `0 u v`, deletion is `1 u v`.
--
--   **Updates.** Vertices are $\{0,\dots,n-1\}$. From the current simple graph $G$, a legal update for Theorem 1.1 inserts a non-edge $uv$ with $u\ne v$ or deletes an edge (no degree bound).
--
--   **Interaction.** A problem instance (`Setup`) consists of a program $P$, the preprocessing words, the initial graph $G_0$, a legality condition and a **strategy** $A$, a map from the list $c_0,\dots,c_t$ of completed configurations seen so far to the next update or to "stop". On coin tape $\omega$ the run is: start with all memory $0$ and the preprocessing words pending, run to the first completed state $c_0$; then repeatedly let $A$ propose an update $x_{t+1}$ from $(c_0,\dots,c_t)$; if it stops or $x_{t+1}$ is illegal for $G_t$, the interaction ends; otherwise the words of $x_{t+1}$ are delivered to $c_t$, $G_{t+1}=x_{t+1}(G_t)$, and the machine runs to the next completed state $c_{t+1}$. If it executes `halt` first, update $t+1$ **ends in FAIL** and the interaction ends. The strategy sees memory, output and coin cursor of every completed configuration (all prior decisions and internal state), never the unread coins.
--
--   **Change logs.** The output is read in consecutive triples. The reported matching $M^*$ after preprocessing or after a completed update is $\emptyset$ with every triple $u,v,b$ written so far applied in order ($b=1$ adds $uv$, $b=0$ deletes it; anything else is ignored). The number of records written while processing an update is the number of words it writes divided by $3$, rounded up.
--
--   **Maximal matching.** $M$ is a matching if no two distinct edges share a vertex. A vertex $v$ is **settled** (Definition 2.2) if an edge of $M$ contains $v$ or every neighbour of $v$ is contained in an edge of $M$. $M$ is a **maximal matching** of $G$ if $M\subseteq E(G)$, $M$ is a matching and every vertex is settled.
--
--   The definition also provides the bound predicates used by every theorem: preprocessing reaches a completed state within $T$ steps; every delivered update ends (completed or FAIL), or completes, within $T$ steps; at most $R$ records are written during any delivered update; a property holds after preprocessing and after every completed update.
--
--   **Formalization Note.** `wordSize a N = a·⌈log₂(N+1)⌉`, `logInv p = ⌈log₂(1/p)⌉`. `TimeLE T b` says the step count $T\in\mathbb N\cup\{\infty\}$ is finite and at most the real $b$. `CoinFree P` says $P$ contains no `coin` instruction. `vdeg` is the vertex degree and `mdeg M v` the number of edges of $M$ containing $v$.
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 1, §1.1; p. 2, Theorem 1.1 and the definition of per-update failure probability; p. 12, Definition 2.2

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol

namespace DynMaxMatchEC.Main

open DynBrooks

/-!
# Edge updates, change logs, FAIL, and the adaptive interaction

Chuzhoy, *New Algorithms for Dynamic Maximal Matching and Edge Coloring* (manuscript, Nov. 1,
2026; PDF sha256 2c277528…4ca5), §1.1 p. 1, Theorem 1.1 p. 2, §2 p. 11, Definition 2.2 p. 12.

* The machine is the published word RAM `DynBrooks.Program` (unit-cost uniform random words read by
  `coin`, a `read` that blocks until input is delivered, `write` to an output list, `halt`; every
  executed instruction is one step). The update plumbing `DynBrooks.Update`, `Update.apply` and
  `Update.words` (`0 u v` inserts, `1 u v` deletes) is reused from `DynBrooks_Protocol`; its Brooks
  legality and its query-model coloring are not used.
* Vertices are `Fin n`. A run starts from `initConfig w inp` (all memory zero, coin cursor `0`, the
  preprocessing words `inp` pending).
* **FAIL** is the machine executing `halt` while processing an update; a halted configuration never
  reaches a completed state again, so the interaction stops there.
* **The adversary** is a deterministic strategy: it maps the list of completed configurations seen so
  far (after preprocessing, then after every completed update; memory, program counter, output and
  coin cursor included, so all prior decisions and internal state) to the next update, or to `none`
  (stop). It never sees the unread part of the coin tape. An update that is not legal for the current
  graph also ends the interaction.
* **Change logs.** The output is read as consecutive triples of words (a trailing incomplete triple
  is ignored). The number of records written while processing an update is the number of words
  written divided by three, rounded up.
* A **matching** is a finite set of edges (unordered pairs of vertices) no two of which share a
  vertex; the reported matching `M∗` is the empty set with every record `u, v, b` applied in order
  (`b = 1`: add the edge `uv`; `b = 0`: delete it; a record whose vertex words are not two distinct
  vertices `< n`, or whose flag is neither `0` nor `1`, is ignored).
-/

/-- A legal update for Theorem 1.1 from the current graph `G`: it inserts a non-edge `uv` with
`u ≠ v`, or deletes an edge. There is no degree or edge-count condition. -/
def IsEdgeUpdate {n : ℕ} (G : SimpleGraph (Fin n)) : Update n → Prop
  | .insert u v => u ≠ v ∧ ¬ G.Adj u v
  | .delete u v => G.Adj u v

/-- The starting configuration: program counter `0`, all memory zero, the words `inp` pending, coin
cursor `0`, nothing written. -/
def initConfig (w : ℕ) (inp : List ℕ) : Config w :=
  ⟨0, fun _ => 0, inp, 0, [], ∅⟩

/-- The machine is at a `halt` instruction (this is how a program returns FAIL). -/
def IsHalted {w : ℕ} (P : Program) (c : Config w) : Prop :=
  P[c.pc]? = some Instr.halt

/-- The number of steps from `c` until processing ends, either in a completed state or at `halt`
(FAIL); `⊤` if it never ends. -/
noncomputable def endTime {w : ℕ} (P : Program) (ω : ℕ → BitVec w) (c : Config w) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : IsCompleted P (run P ω c t) ∨ IsHalted P (run P ω c t)), (t : ℕ∞)

/-- `TimeLE T b`: the step count `T` is finite and at most the real number `b`. -/
def TimeLE (T : ℕ∞) (b : ℝ) : Prop :=
  ∃ m : ℕ, T = (m : ℕ∞) ∧ (m : ℝ) ≤ b

/-- A deterministic program: it contains no `coin` instruction. -/
def CoinFree (P : Program) : Prop :=
  ∀ i : ℕ, Instr.coin i ∉ P

/-- `⌈log₂ (1/p)⌉`, the input word that stands for the failure parameter `p`. -/
noncomputable def logInv (p : ℝ) : ℕ :=
  ⌈Real.logb 2 (1 / p)⌉₊

/-- The word size `a · ⌈log₂ (N + 1)⌉`, where `N` bounds every input number. -/
def wordSize (a N : ℕ) : ℕ :=
  a * Nat.clog 2 (N + 1)

/-- A deterministic adaptive strategy: from the completed configurations seen so far, in
chronological order, the next update or `none` (stop). -/
abbrev Strategy (w n : ℕ) := List (Config w) → Option (Update n)

/-- The history after preprocessing and some completed updates: the completed configurations
`c₀, …, c_t` in order, the last one `c_t`, and the current graph `G_t`. -/
structure Hist (w n : ℕ) where
  confs : List (Config w)
  last : Config w
  graph : SimpleGraph (Fin n)

/-- One dynamic problem instance on the machine: the program, its preprocessing words, the initial
graph, the legality condition on updates, and the adversary's strategy. -/
structure Setup (w n : ℕ) where
  prog : Program
  inp : List ℕ
  G₀ : SimpleGraph (Fin n)
  legal : SimpleGraph (Fin n) → Update n → Prop
  adv : Strategy w n

namespace Setup

variable {w n : ℕ}

open Classical in
/-- The update the strategy proposes after history `h`, if it proposes one and it is legal. -/
noncomputable def proposal (g : Setup w n) (h : Hist w n) : Option (Update n) :=
  match g.adv h.confs with
  | some x => if g.legal h.graph x then some x else none
  | none => none

/-- The history after preprocessing and `t` completed updates on coin tape `ω` (`none` once the
interaction has stopped: preprocessing never completed, the strategy stopped or proposed an
illegal update, or an update was not completed because of FAIL or non-termination). -/
noncomputable def hist (g : Setup w n) (ω : ℕ → BitVec w) : ℕ → Option (Hist w n)
  | 0 => (complete g.prog ω (initConfig w g.inp)).map fun c => ⟨[c], c, g.G₀⟩
  | t + 1 =>
      match hist g ω t with
      | none => none
      | some h =>
          match g.proposal h with
          | none => none
          | some x =>
              (complete g.prog ω (feed h.last x.words)).map fun c =>
                ⟨h.confs ++ [c], c, x.apply h.graph⟩

/-- Update number `t` (`t ≥ 1`) is delivered on tape `ω`: the history before it and the update.
`none` for `t = 0` and when the interaction stopped before update `t`. -/
noncomputable def delivered (g : Setup w n) (ω : ℕ → BitVec w) : ℕ → Option (Hist w n × Update n)
  | 0 => none
  | t + 1 => (g.hist ω t).bind fun h => (g.proposal h).map fun x => (h, x)

end Setup

/-- The configuration in which the processing of a delivered update starts: its words are fed to
the last completed configuration. -/
def startOf {w n : ℕ} (hx : Hist w n × Update n) : Config w :=
  feed hx.1.last hx.2.words

namespace Setup

variable {w n : ℕ}

/-- The event "update `t` is delivered and its processing ends in FAIL" on tape `ω`. -/
def FailsAt (g : Setup w n) (ω : ℕ → BitVec w) (t : ℕ) : Prop :=
  ∃ hx, g.delivered ω t = some hx ∧ ∃ s : ℕ, IsHalted g.prog (run g.prog ω (startOf hx) s)

end Setup

/-- Split a list of words into consecutive triples (a trailing incomplete triple is dropped). -/
def triples : List ℕ → List (ℕ × ℕ × ℕ)
  | a :: b :: c :: rest => (a, b, c) :: triples rest
  | _ => []

/-- The number of records (triples) written between configuration `c` and a later configuration
`c'` of the same run: the number of new output words divided by three, rounded up. -/
def recordsWritten {w : ℕ} (c c' : Config w) : ℕ :=
  (c'.output.length - c.output.length + 2) / 3

/-- The edge `uv` named by the words `u, v`, if they are two distinct vertices `< n`. -/
def toEdge (n u v : ℕ) : Option (Sym2 (Fin n)) :=
  if h : u < n ∧ v < n ∧ u ≠ v then some s(⟨u, h.1⟩, ⟨v, h.2.1⟩) else none

/-- Apply one matching record `u, v, b`: `b = 1` adds the edge `uv`, `b = 0` deletes it; anything
else is ignored. -/
def applyMatchRecord {n : ℕ} (M : Finset (Sym2 (Fin n))) : ℕ × ℕ × ℕ → Finset (Sym2 (Fin n))
  | (u, v, b) =>
      match toEdge n u v with
      | some e => if b = 1 then insert e M else if b = 0 then M.erase e else M
      | none => M

/-- The reported matching `M∗`: the empty set with every record of the output applied in order. -/
def reportedMatching (n : ℕ) (out : List ℕ) : Finset (Sym2 (Fin n)) :=
  (triples out).foldl applyMatchRecord ∅

/-- A matching: no two distinct edges of `M` share a vertex. -/
def IsMatching {n : ℕ} (M : Finset (Sym2 (Fin n))) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : Fin n, v ∈ e → v ∉ f

/-- Vertex `v` is matched in `M`: some edge of `M` contains it. -/
def IsMatchedIn {n : ℕ} (M : Finset (Sym2 (Fin n))) (v : Fin n) : Prop :=
  ∃ e ∈ M, v ∈ e

/-- Definition 2.2: `v` is settled in `G` with respect to `M` if some edge of `M` is incident to
`v`, or every neighbour of `v` is incident to an edge of `M`. -/
def IsSettled {n : ℕ} (G : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) (v : Fin n) : Prop :=
  IsMatchedIn M v ∨ ∀ u : Fin n, G.Adj v u → IsMatchedIn M u

open Classical in
/-- The degree of `v` in `G`. -/
noncomputable def vdeg {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  G.degree v

/-- `m(v)`: the number of edges of the edge set `M` incident to `v`. -/
def mdeg {n : ℕ} (M : Finset (Sym2 (Fin n))) (v : Fin n) : ℕ :=
  (M.filter fun e => v ∈ e).card

/-- A maximal matching of `G`: a matching made of edges of `G` in which every vertex is settled
(equivalently, no edge of `G` can be added). -/
def IsMaximalMatching {n : ℕ} (G : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ IsMatching M ∧ ∀ v : Fin n, IsSettled G M v

namespace Setup

variable {w n : ℕ}

/-- Preprocessing reaches a completed state within `T` steps on tape `ω`. -/
def PreprocWithin (g : Setup w n) (ω : ℕ → BitVec w) (T : ℝ) : Prop :=
  TimeLE (time g.prog ω (initConfig w g.inp)) T

/-- Every delivered update's processing ends (completed state or FAIL) within `T` steps. -/
def UpdatesEndWithin (g : Setup w n) (ω : ℕ → BitVec w) (T : ℝ) : Prop :=
  ∀ (t : ℕ) (hx : Hist w n × Update n), g.delivered ω t = some hx →
    TimeLE (endTime g.prog ω (startOf hx)) T

/-- Every delivered update's processing reaches a completed state (never FAIL) within `T` steps. -/
def UpdatesCompleteWithin (g : Setup w n) (ω : ℕ → BitVec w) (T : ℝ) : Prop :=
  ∀ (t : ℕ) (hx : Hist w n × Update n), g.delivered ω t = some hx →
    TimeLE (time g.prog ω (startOf hx)) T

/-- While processing any delivered update, at most `R` records are ever written. -/
def RecordsWithin (g : Setup w n) (ω : ℕ → BitVec w) (R : ℝ) : Prop :=
  ∀ (t : ℕ) (hx : Hist w n × Update n), g.delivered ω t = some hx →
    ∀ s : ℕ, (recordsWritten hx.1.last (run g.prog ω (startOf hx) s) : ℝ) ≤ R

/-- After preprocessing and after every completed update, the current graph and the whole output so
far satisfy `Q`. -/
def AlwaysHolds (g : Setup w n) (ω : ℕ → BitVec w) (Q : SimpleGraph (Fin n) → List ℕ → Prop) :
    Prop :=
  ∀ (t : ℕ) (h : Hist w n), g.hist ω t = some h → Q h.graph h.last.output

end Setup

end DynMaxMatchEC.Main


