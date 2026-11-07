-- Prove2me | Definitions.Def_DynBrooks_Protocol
-- name    : DynBrooks_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:46.243619+00:00
-- url     : https://prove2.me/theorems/09890a76-2c38-4a1a-a408-37f11953a905
-- title:
--   §3 — Brooks graphs, legal updates, work, reachable states and color queries
-- statement:
--   Vertices are $[n]$, represented as $\{0,\dots,n-1\}$. A graph $G$ on $[n]$ is **Brooks** for $\Delta$ if every vertex has degree at most $\Delta$ and $G$ contains no $K_{\Delta+1}$. An **update** inserts or deletes an edge $uv$; it is **legal** for $G$ if it inserts a non-edge ($u\ne v$) or deletes an edge, and the resulting graph is Brooks. A legal update sequence is one in which every update is legal for the graph it meets.
--
--   A program serves the graph as follows. **Preprocessing** receives the words $n$, $\min(\Delta,n)$, the number of edges, and the edges of the initial graph $G_0$ in an arbitrary listing and orientation. An insertion of $uv$ arrives as the words $0,u,v$, a deletion as $1,u,v$, and a query for vertex $v$ as $2,v$; an operation is delivered only to a completed state.
--
--   - The **work** $W(t)$ through update $t$ is the total number of steps from the start of preprocessing to the completed state after the first $t$ updates, and $\infty$ if some of these runs never completes.
--   - $s$ is **reachable with current graph $G$** if it is the completed state reached, on some coin tape, after preprocessing on $G_0$ and then finitely many legal updates leading to $G$.
--   - $\mathrm{color}_s(v)$ is the word output by the query for $v$ from $s$.
--   - $s$ **serves** $G$ with query constant $C$ if, on every coin tape and for every $v$, the query for $v$ from $s$ reaches a completed state within $C$ steps with the same program counter, memory and coin cursor as $s$, having output exactly $\mathrm{color}_s(v)$; and $\mathrm{color}_s$ is a proper coloring of $G$ with colors in $\{1,\dots,\Delta\}$.
--
--   It also defines the number of vertices recolored between two completed states and $\ell=\max\{1,\lceil\log(n+T+2)\rceil\}$ (§3).
--
--   **Formalization Note** Since $\Delta$ may exceed every word, preprocessing receives $\min(\Delta,n)$; when $\Delta\ge n$ the colors may stay at most $n\le\Delta$. Queries are not part of reachability: serving requires that a query changes no state.
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), §3, p.13 (PDF 15); §1.1, p.2 (PDF 4)

import Mathlib
import Definitions.Def_DynBrooks_Machine

namespace DynBrooks

/-! # Brooks graphs, updates, and how a program serves them

Mishra, Mukherjee, *Fully Dynamic Brooks Coloring* (STOC 2027 submission, sha256 6542a9f1…), §3,
p.13 (PDF 15): "Every graph in the update sequence has maximum degree at most ∆ and contains no
K_{∆+1}." "Color queries are answered from the stored coloring after each completed update."

**Formalization Note.** Vertices are `Fin n`, delivered as their value. Preprocessing receives
`n`, `min Δ n`, the edge count and the edges of the initial graph in an arbitrary listing; an update
or query arrives as words only when the machine is blocked. Colors are the word values `1, …, Δ`.
Since `Δ` may exceed every word, the program receives `min Δ n` (when `Δ ≥ n` the colors may stay
at most `n ≤ Δ`). -/

open Classical in
/-- The Brooks hypotheses: maximum degree at most `Δ` and no `K_{Δ+1}`. -/
def IsBrooks {n : ℕ} (Δ : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  (∀ v, G.degree v ≤ Δ) ∧ G.CliqueFree (Δ + 1)

/-- An edge update on `Fin n`. -/
inductive Update (n : ℕ) where
  | insert (u v : Fin n)
  | delete (u v : Fin n)

/-- The graph after an update. -/
def Update.apply {n : ℕ} (G : SimpleGraph (Fin n)) : Update n → SimpleGraph (Fin n)
  | .insert u v => G ⊔ SimpleGraph.edge u v
  | .delete u v => G.deleteEdges {s(u, v)}

/-- A legal update from `G`: it inserts a non-edge or deletes an edge, and the result is Brooks. -/
def IsLegal {n : ℕ} (Δ : ℕ) (G : SimpleGraph (Fin n)) (x : Update n) : Prop :=
  (match x with
    | .insert u v => u ≠ v ∧ ¬ G.Adj u v
    | .delete u v => G.Adj u v) ∧
  IsBrooks Δ (x.apply G)

/-- A legal update sequence from `G`: every update is legal for the graph it meets. -/
def IsLegalSeq {n : ℕ} (Δ : ℕ) : SimpleGraph (Fin n) → List (Update n) → Prop
  | _, [] => True
  | G, x :: σ => IsLegal Δ G x ∧ IsLegalSeq Δ (x.apply G) σ

/-- The graph `G_t` after the first `t` updates of `σ`. -/
def graphAfter {n : ℕ} (G : SimpleGraph (Fin n)) (σ : List (Update n)) (t : ℕ) :
    SimpleGraph (Fin n) :=
  (σ.take t).foldl Update.apply G

/-- The words of an update: `0 u v` inserts, `1 u v` deletes. -/
def Update.words {n : ℕ} : Update n → List ℕ
  | .insert u v => [0, u.val, v.val]
  | .delete u v => [1, u.val, v.val]

/-- The words of a query: `2 v`. -/
def queryWords {n : ℕ} (v : Fin n) : List ℕ := [2, v.val]

/-- `es` lists each edge of `G` exactly once, in any order and orientation. -/
def IsEdgeListing {n : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) : Prop :=
  (es.map fun e => s(e.1, e.2)).Nodup ∧
    ∀ e : Sym2 (Fin n), e ∈ G.edgeSet ↔ e ∈ es.map fun e => s(e.1, e.2)

/-- The input of preprocessing: `n`, `min Δ n`, the edge count, and the edges. -/
def initWords {n : ℕ} (Δ : ℕ) (es : List (Fin n × Fin n)) : List ℕ :=
  [n, min Δ n, es.length] ++ es.flatMap fun e => [e.1.val, e.2.val]

/-- The starting configuration: all memory zero, coin cursor at `0`, the initial words pending. -/
def startConfig (w : ℕ) {n : ℕ} (Δ : ℕ) (es : List (Fin n × Fin n)) : Config w :=
  ⟨0, fun _ => 0, initWords Δ es, 0, [], ∅⟩

/-- Work from an optional completed state through a list of operations (each given by its words):
the sum of the operation times, and `⊤` once some operation does not complete. -/
noncomputable def workFrom {w : ℕ} (P : Program) (ω : ℕ → BitVec w) :
    Option (Config w) → List (List ℕ) → ℕ∞
  | none, _ => ⊤
  | some _, [] => 0
  | some c, op :: ops => time P ω (feed c op) + workFrom P ω (complete P ω (feed c op)) ops

/-- `W(t)`: every step from the start of preprocessing to the completed state after update `t`. -/
noncomputable def Work {w n : ℕ} (P : Program) (Δ : ℕ) (es : List (Fin n × Fin n))
    (σ : List (Update n)) (ω : ℕ → BitVec w) (t : ℕ) : ℕ∞ :=
  time P ω (startConfig w Δ es) +
    workFrom P ω (complete P ω (startConfig w Δ es)) ((σ.take t).map Update.words)

/-- The state after a list of operations, if every one of them completes. -/
noncomputable def stateFrom {w : ℕ} (P : Program) (ω : ℕ → BitVec w) :
    Option (Config w) → List (List ℕ) → Option (Config w)
  | none, _ => none
  | some c, [] => some c
  | some c, op :: ops => stateFrom P ω (complete P ω (feed c op)) ops

/-- The completed state `s_t` after update `t` on tape `ω`, if it is reached. -/
noncomputable def stateAfter {w n : ℕ} (P : Program) (Δ : ℕ) (es : List (Fin n × Fin n))
    (σ : List (Update n)) (ω : ℕ → BitVec w) (t : ℕ) : Option (Config w) :=
  stateFrom P ω (complete P ω (startConfig w Δ es)) ((σ.take t).map Update.words)

/-- `Reach P Δ es s G`: `s` is a completed state with current graph `G`, reached from the start by
preprocessing on the edges `es` of `G₀` and finitely many legal updates, on some coin tape. Queries
change no state (`QueryOK`), so they need no case here. -/
inductive Reach {w n : ℕ} (P : Program) (Δ : ℕ) (es : List (Fin n × Fin n))
    (G₀ : SimpleGraph (Fin n)) : Config w → SimpleGraph (Fin n) → Prop
  | init (ω : ℕ → BitVec w) (s : Config w) :
      complete P ω (startConfig w Δ es) = some s → Reach P Δ es G₀ s G₀
  | update {s : Config w} {G : SimpleGraph (Fin n)} (x : Update n) (ω : ℕ → BitVec w)
      (s' : Config w) :
      Reach P Δ es G₀ s G → IsLegal Δ G x →
        complete P ω (feed s x.words) = some s' → Reach P Δ es G₀ s' (x.apply G)

open Classical in
/-- `colorOf P s v`: the word the program outputs for `query v` from state `s` (read on the all-zero
tape; `QueryOK` says that the tape does not matter). -/
noncomputable def colorOf {w n : ℕ} (P : Program) (s : Config w) (v : Fin n) : ℕ :=
  match complete P (fun _ => 0) (feed s (queryWords v)) with
  | some c => (c.output.drop s.output.length).headD 0
  | none => 0

/-- Two configurations with the same program counter, memory and coin cursor. The output and the
ghost set `written` are not state the program can branch on. -/
def SameState {w : ℕ} (c c' : Config w) : Prop :=
  c.pc = c'.pc ∧ c.mem = c'.mem ∧ c.coinPos = c'.coinPos

/-- "Answer color queries in O(1) time": on every tape, `query v` from `s` reaches a completed state
within `C` steps, with the same state as `s` (no coin is used and nothing changes), having written
exactly the word `colorOf P s v`. -/
def QueryOK {w n : ℕ} (P : Program) (C : ℕ) (s : Config w) : Prop :=
  ∀ (v : Fin n) (ω : ℕ → BitVec w), ∃ t ≤ C,
    let c := run P ω (feed s (queryWords v)) t
    IsCompleted P c ∧ SameState s c ∧ c.output = s.output ++ [colorOf P s v]

/-- A proper coloring of `G` with colors in `{1, …, Δ}`. -/
def IsProperColoring {n : ℕ} (Δ : ℕ) (G : SimpleGraph (Fin n)) (χ : Fin n → ℕ) : Prop :=
  (∀ v, 1 ≤ χ v ∧ χ v ≤ Δ) ∧ ∀ u v, G.Adj u v → χ u ≠ χ v

/-- What every completed state must offer: pure `O(1)` queries that read off a proper `Δ`-coloring of
the current graph. -/
def Serves {w n : ℕ} (P : Program) (C Δ : ℕ) (s : Config w) (G : SimpleGraph (Fin n)) : Prop :=
  QueryOK (n := n) P C s ∧ IsProperColoring Δ G (colorOf P s)

/-- The number of vertices whose color differs between two completed states. -/
noncomputable def recolored {w : ℕ} (n : ℕ) (P : Program) (s s' : Config w) : ℕ :=
  open Classical in
  (Finset.univ.filter fun v : Fin n => colorOf P s v ≠ colorOf P s' v).card

/-- `ℓ = max{1, ⌈log(n + T + 2)⌉}` (§3, p.13), a natural number. -/
noncomputable def ell (n T : ℕ) : ℕ :=
  max 1 ⌈Real.log ((n : ℝ) + T + 2)⌉₊

end DynBrooks


