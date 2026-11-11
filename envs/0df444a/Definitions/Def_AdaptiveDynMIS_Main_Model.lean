-- Prove2me | Definitions.Def_AdaptiveDynMIS_Main_Model
-- name    : AdaptiveDynMIS_Main_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:55:02.918666+00:00
-- url     : https://prove2.me/theorems/1100e8d7-aa3c-4171-83a2-4fa9000268a4
-- title:
--   Legal updates with at most m edges, the reported MIS, and the adaptive interaction of a word-RAM program with an update strategy
-- statement:
--   Fix $n$ vertices $V=\{0,\dots,n-1\}$ (`Fin n`) and an edge bound $m$. A **fully dynamic graph** starts empty; an **update** either inserts an edge $uv$ with $u\ne v$ that is not present, or deletes an edge that is present. An update is **legal** for the current graph $G$ when, in addition, the graph after it has at most $m$ edges:
--   $$\mathrm{Legal}_m(G,x)\iff \bigl(x=\mathrm{ins}(u,v),\ u\ne v,\ uv\notin E(G)\ \text{ or }\ x=\mathrm{del}(u,v),\ uv\in E(G)\bigr)\ \wedge\ |E(x(G))|\le m .$$
--   $G_t$ is the graph after the first $t$ updates of a list $\sigma$, starting from the empty graph.
--
--   **The machine.** An algorithm is a program $P$ of the published word RAM (`DynBrooks_Machine`): words of $w=a\lceil\log_2(n+1)\rceil$ bits, unit-cost uniform random words read from a coin tape $\omega$, a `read` instruction that blocks until input is delivered, and a `write` instruction appending a word to the output. Preprocessing starts with the words $n$ and $\min(m,n^2)$ pending; afterwards each update is delivered as its words (`Update.words` of `DynBrooks_Protocol`) to the completed state reached so far. `stateAt` is the completed state after preprocessing and $t$ updates, `updateTime` the number of steps of update $t$ ($\infty$ if it never completes), and `totalUpdateTime` the sum over the first $t$ updates.
--
--   **The reported MIS.** The machine reports changes in MIS membership by writing pairs $v,b$: $b=1$ puts vertex $v$ in, $b=0$ takes it out. The **reported set** $M_t$ after the completed state following update $t$ is $V$ (the paper's initial $M=V$) with every pair written so far applied in order; a pair whose first word is not a vertex, or whose second word is neither $0$ nor $1$, is ignored.
--
--   **The adaptive adversary.** A deterministic strategy $A$ maps the list $(M_0,\dots,M_t)$ of reported sets so far to the next update, or to "stop". On coin tape $\omega$ the interaction runs: preprocessing; then, while the current state is completed, $A$ sees the reported sets and proposes an update, which is delivered if it is legal for the current graph. The interaction stops when $A$ stops, when its proposal is illegal (it is not delivered), when a run never reaches a completed state, or after $N=\lfloor n^d\rfloor$ updates. The **realized update sequence** $\sigma(\omega)$ is the list of delivered updates; the graphs $G_t$, reported sets $M_t$ and update times are all functions of $\omega$ through it.
--
--   This is the model of Theorem 1.1: the adversary chooses each update from the reported MISs and sees nothing else (not the coins, the memory, the order of the output words or the running times).
--
--   **Formalization Note.** The machine, the update type and its words are reused from `DynBrooks_Machine` and `DynBrooks_Protocol`; the Brooks legality and the query-model coloring of the latter are not used. Edge counts use `Set.ncard` of the edge set. `TimeLE T b` says a step count in $\mathbb N\cup\{\infty\}$ is finite and at most the real $b$.
-- source:
--   Chen, Fan, Zhang, Faster Dynamic Maximal Independent Set against Adaptive Adversaries, arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a), p. 1, §1; p. 2, Theorem 1.1; pp. 4–5, §2; p. 35, §4.2

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_SmoothedMIS_IsMIS

namespace AdaptiveDynMIS.Main

/-! # Fully dynamic MIS against an adaptive adversary: legality, the reported MIS, the interaction

Chen, Fan, Zhang, *Faster Dynamic Maximal Independent Set against Adaptive Adversaries*,
arXiv:2611.05932 (PDF sha256 a65b11d9…ec4a): §1 p. 1 (PDF 3), Theorem 1.1 p. 2 (PDF 4), §2 pp. 4–5
(PDF 6–7), §4.2 p. 35 (PDF 37).

* Vertices are `Fin n`. The graph starts **empty**; an update inserts a non-edge `uv` with `u ≠ v`
  or deletes an edge, and it is **legal** when the graph afterwards has at most `m` edges.
* The machine is the published word RAM `DynBrooks.Program` (unit-cost uniform random words; `read`
  blocks until an operation is delivered, so there is no look-ahead). The update plumbing
  (`DynBrooks.Update`, `Update.apply`, `Update.words`, `graphAfter`, `stateFrom`) is reused from the
  published `DynBrooks_Protocol`; its Brooks legality and its query-model coloring are not used.
* Preprocessing receives the words `n` and `min m (n·n)` (`m` itself may exceed every word). Each
  update is then delivered as `Update.words` to the completed state.
* **The reported MIS** is what the machine itself writes: its output words are read as pairs `v, b`
  ("vertex `v` joins the MIS" for `b = 1`, "leaves it" for `b = 0`; a pair whose first word is not a
  vertex value, or whose second word is neither `0` nor `1`, is ignored). The reported set after a
  completed state is `V` (the paper's initial `M = V`) with every pair written so far applied in
  order.
* **The adversary** is a deterministic strategy that maps the list of reported sets so far (after
  preprocessing, then after each completed update) to the next update, or to `none` to stop. It
  sees nothing else: not the coins, the output order, the memory or the running times. -/

/-- A legal update from `G` for the edge bound `m`: it inserts a non-edge `uv` with `u ≠ v`, or
deletes an edge, and the resulting graph has at most `m` edges. -/
def IsLegalUpdate {n : ℕ} (m : ℕ) (G : SimpleGraph (Fin n)) (x : DynBrooks.Update n) : Prop :=
  (match x with
    | .insert u v => u ≠ v ∧ ¬ G.Adj u v
    | .delete u v => G.Adj u v) ∧
  (x.apply G).edgeSet.ncard ≤ m

/-- `G_t`: the graph after the first `t` updates of `σ`, starting from the empty graph. -/
def graphAt {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : SimpleGraph (Fin n) :=
  DynBrooks.graphAfter ⊥ σ t

/-- The word size `a · ⌈log₂ (n + 1)⌉` used for an `n`-vertex graph (`a` is fixed with the
program). -/
def wordSize (a n : ℕ) : ℕ := a * Nat.clog 2 (n + 1)

/-- The preprocessing input: the words `n` and `min m (n·n)`. -/
def initWords (n m : ℕ) : List ℕ := [n, min m (n * n)]

/-- The starting configuration: program counter `0`, all memory zero, coin cursor `0`, nothing
written, the preprocessing words `inp` pending. -/
def initConfig (w : ℕ) (inp : List ℕ) : DynBrooks.Config w :=
  ⟨0, fun _ => 0, inp, 0, [], ∅⟩

/-- The completed state after preprocessing on `inp` and the first `t` updates of `σ`, on tape `ω`
(`none` if one of these runs never reaches a completed state). -/
noncomputable def stateAt (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : Option (DynBrooks.Config w) :=
  DynBrooks.stateFrom P ω (DynBrooks.complete P ω (initConfig w inp))
    ((σ.take t).map DynBrooks.Update.words)

/-- The time of update `t` (0-based, the `(t+1)`-st entry of `σ`): the number of steps from
delivering its words to the completed state after the first `t` updates to the next completed state;
`⊤` if that run never completes or the earlier runs did not complete. -/
noncomputable def updateTime (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : ℕ∞ :=
  match stateAt P ω inp σ t, σ[t]? with
  | some s, some x => DynBrooks.time P ω (DynBrooks.feed s x.words)
  | _, _ => ⊤

/-- The total time of the first `t` updates of `σ` (`⊤` as soon as one of them does not
complete). -/
noncomputable def totalUpdateTime (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w)
    (inp : List ℕ) {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : ℕ∞ :=
  ∑ s ∈ Finset.range t, updateTime P ω inp σ s

/-- `TimeLE T b`: the (possibly infinite) step count `T` is finite and at most the real `b`. -/
def TimeLE (T : ℕ∞) (b : ℝ) : Prop :=
  ∃ k : ℕ, T = (k : ℕ∞) ∧ (k : ℝ) ≤ b

/-- Every word the machine has written up to the completed state after the first `t` updates
(empty if that state is not reached). -/
noncomputable def outputAt (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : List ℕ :=
  match stateAt P ω inp σ t with
  | some s => s.output
  | none => []

/-- Apply a change log of pairs `v, b` to a vertex set, in order: `b = 1` puts vertex `v` in, `b = 0`
takes it out. A pair whose first word is not a vertex value or whose second word is neither `0` nor
`1` is ignored, as is a single trailing word. -/
def applyMISLog {n : ℕ} : Finset (Fin n) → List ℕ → Finset (Fin n)
  | M, v :: b :: rest =>
      applyMISLog
        (if h : v < n then
          (if b = 1 then insert ⟨v, h⟩ M else if b = 0 then M.erase ⟨v, h⟩ else M)
        else M) rest
  | M, _ => M

/-- The reported MIS `M_t` after the first `t` updates: the whole vertex set `V` with every pair the
machine has written so far applied in order. -/
noncomputable def reportedAt (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : Finset (Fin n) :=
  applyMISLog Finset.univ (outputAt P ω inp σ t)

/-- The list `[M_0, M_1, …, M_{|σ|}]` of the reported sets after preprocessing and after each update
of `σ`: exactly what an adaptive adversary observes. -/
noncomputable def reports (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) : List (Finset (Fin n)) :=
  (List.range (σ.length + 1)).map (reportedAt P ω inp σ)

/-- A deterministic adaptive adversary on `n` vertices: from the reported sets so far it proposes the
next update, or `none` to stop. -/
abbrev Strategy (n : ℕ) := List (Finset (Fin n)) → Option (DynBrooks.Update n)

open Classical in
/-- The updates delivered in the first `r` rounds of the interaction on tape `ω`. In a round, if the
completed state after the updates delivered so far exists, the adversary sees the reported sets and
proposes an update; a legal proposal (for the edge bound `m` and the current graph) is delivered.
The interaction stays put (stops) once the adversary returns `none`, once its proposal is illegal
(such a proposal is never delivered), or once a run does not reach a completed state. -/
noncomputable def deliveredAfter (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w)
    (inp : List ℕ) {n : ℕ} (m : ℕ) (A : Strategy n) : ℕ → List (DynBrooks.Update n)
  | 0 => []
  | r + 1 =>
      let σ := deliveredAfter P ω inp m A r
      match stateAt P ω inp σ σ.length, A (reports P ω inp σ) with
      | some _, some x => if IsLegalUpdate m (graphAt σ σ.length) x then σ ++ [x] else σ
      | _, _ => σ

/-- The length cap `⌊n^d⌋` on the number of updates ("polynomial-length update sequences"). -/
noncomputable def lengthCap (n : ℕ) (d : ℝ) : ℕ := ⌊(n : ℝ) ^ d⌋₊

/-- The realized update sequence `σ(ω)` of program `P` (word size `wordSize a n`, preprocessing input
`initWords n m`) against the adversary `A` on tape `ω`, with at most `lengthCap n d` updates. -/
noncomputable def realized (P : DynBrooks.Program) (a : ℕ) (d : ℝ) (n m : ℕ) (A : Strategy n)
    (ω : ℕ → BitVec (wordSize a n)) : List (DynBrooks.Update n) :=
  deliveredAfter P ω (initWords n m) m A (lengthCap n d)

end AdaptiveDynMIS.Main


