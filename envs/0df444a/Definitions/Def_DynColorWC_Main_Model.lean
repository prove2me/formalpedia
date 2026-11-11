-- Prove2me | Definitions.Def_DynColorWC_Main_Model
-- name    : DynColorWC_Main_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:46:14.237973+00:00
-- url     : https://prove2.me/theorems/799201e8-78bb-48fe-8999-a23145a42ded
-- title:
--   The dynamic graph model, the run of a program, and the explicit coloring it writes
-- statement:
--   The vertex set is $[n]$, represented as $\{0,\dots,n-1\}$. The graph starts **empty**. An **update** inserts an edge $uv$ or deletes one; it is **legal** for the current graph $G$ when it inserts a non-edge with $u\ne v$ or deletes an edge, and afterwards every vertex has degree at most $\Delta$. A legal sequence $\sigma$ is one in which every update is legal for the graph it meets; $G_t$ is the graph after the first $t$ updates.
--
--   Programs run on the published word RAM `DynBrooks_Machine` (unit-cost uniform random words, a `read` that blocks until an operation is delivered, every instruction one step), with word size $a\lceil\log_2(n+1)\rceil$. A run starts with the preprocessing words pending; after it reaches a completed state, the updates are delivered one at a time, each as its words ($0,u,v$ for an insertion, $1,u,v$ for a deletion) to the completed state reached after the previous one. The **time** of update $t$ is the number of steps from its delivery to the next completed state ($\infty$ if none is reached).
--
--   **Explicit coloring.** The program's output words are read as pairs $v,q$, each meaning "$\chi(v):=q$". The coloring $\chi_t$ after update $t$ is the all-$1$ coloring with every pair written up to the completed state after update $t$ applied in order. The number of vertices **recolored** by update $t$ is the number of $v$ with $\chi_t(v)\ne\chi_{t-1}(v)$. A coloring is a **proper $(\Delta+1)$-coloring** of $G$ if every color lies in $\{1,\dots,\Delta+1\}$ and adjacent vertices get different colors.
--
--   **Formalization Note.** The update plumbing (`Update`, `Update.apply`, `Update.words`, `graphAfter`, `stateFrom`) is reused from the published `DynBrooks_Protocol`; its Brooks legality (which adds $K_{\Delta+1}$-freeness) and its query-model coloring are not used. A pair whose first word is not a vertex is ignored. "Explicit" is exactly what this change log enforces: a query routine that computes colors on demand would not appear in it.
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, §1.1 p. 1 (PDF 3); Theorem 1 p. 2 (PDF 4); §3 'Dynamic graphs model' and 'Sets & Functions' p. 13 (PDF 15); Theorem 4 p. 49 (PDF 51)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol

namespace DynColorWC.Main

/-! # The dynamic graph model, the run of a program, and the explicit coloring

Flin and Ghaffari (2026), *Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time*,
STOC 2027 submission, supplied PDF sha256 93ebb2ff…3154300e3: §1.1 p. 1 (PDF 3), Theorem 1 p. 2
(PDF 4), §3 "Dynamic graphs model" and "Sets & Functions" p. 13 (PDF 15), Theorem 4 p. 49 (PDF 51).

* Vertices are `Fin n`. The graph starts **empty**; an update inserts a non-edge `uv` (`u ≠ v`) or
  deletes an edge, and is **legal** when afterwards every degree is at most `Δ` (no other condition).
* The machine is the published word RAM `DynBrooks.Program` (unit-cost uniform random words,
  `read` blocks until an operation is delivered, so there is no look-ahead). Update plumbing
  (`DynBrooks.Update`, `Update.apply`, `Update.words`, `graphAfter`, `stateFrom`) is reused from the
  published `DynBrooks_Protocol`; its Brooks legality and its query-model coloring are not used.
* A run starts with the preprocessing words pending (for the coloring: `n` and `min Δ n`, since `Δ`
  may not fit in a word); after it completes, each update is delivered as `Update.words` to the
  completed state. Update `t` (0-based) is the `(t+1)`-st entry of the sequence; `stateAt … t` is the
  completed state after preprocessing and the first `t` updates.
* **Explicit coloring.** The coloring is what the machine itself writes: its output words are read as
  pairs `v, q`, each meaning "`χ(v) := q`" (vertex `v` given by its value `0 … n-1`; a pair whose
  first word is not a vertex is ignored). The coloring after update `t` is obtained by applying, in
  order, every pair written up to the completed state after update `t`, starting from the all-`1`
  coloring. A recolored vertex is one whose color differs between consecutive completed states. -/

open Classical in
/-- A legal update from `G` for the degree bound `Δ`: it inserts a non-edge `uv` with `u ≠ v`, or
deletes an edge, and the resulting graph has every degree at most `Δ`. -/
def IsLegalUpdate {n : ℕ} (Δ : ℕ) (G : SimpleGraph (Fin n)) (x : DynBrooks.Update n) : Prop :=
  (match x with
    | .insert u v => u ≠ v ∧ ¬ G.Adj u v
    | .delete u v => G.Adj u v) ∧
  ∀ v, (x.apply G).degree v ≤ Δ

/-- Every update of the list is legal for the graph it meets, starting from `G`. -/
def IsLegalSeqFrom {n : ℕ} (Δ : ℕ) : SimpleGraph (Fin n) → List (DynBrooks.Update n) → Prop
  | _, [] => True
  | G, x :: σ => IsLegalUpdate Δ G x ∧ IsLegalSeqFrom Δ (x.apply G) σ

/-- A legal update sequence: legal from the **empty** graph on `Fin n`. -/
def IsLegalSeq {n : ℕ} (Δ : ℕ) (σ : List (DynBrooks.Update n)) : Prop :=
  IsLegalSeqFrom Δ ⊥ σ

/-- `G_t`: the graph after the first `t` updates of `σ`, starting from the empty graph. -/
def graphAt {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : SimpleGraph (Fin n) :=
  DynBrooks.graphAfter ⊥ σ t

/-- The two endpoints of an update. -/
def updateEndpoints {n : ℕ} : DynBrooks.Update n → Finset (Fin n)
  | .insert u v => {u, v}
  | .delete u v => {u, v}

/-- Update number `t` (1-based: the `t`-th entry of `σ`) is incident on `v`: `v` is one of its endpoints. -/
def IsIncident {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) (v : Fin n) : Prop :=
  ∃ x, σ[t - 1]? = some x ∧ 1 ≤ t ∧ v ∈ updateEndpoints x

/-- The word size `a · ⌈log₂ (n + 1)⌉` used for an `n`-vertex graph (`a` is fixed with the program). -/
def wordSize (a n : ℕ) : ℕ := a * Nat.clog 2 (n + 1)

/-- The starting configuration: program counter `0`, all memory zero, coin cursor `0`, nothing
written, the preprocessing words `inp` pending. -/
def initConfig (w : ℕ) (inp : List ℕ) : DynBrooks.Config w :=
  ⟨0, fun _ => 0, inp, 0, [], ∅⟩

/-- The completed state after preprocessing on `inp` and the first `t` updates of `σ`, on tape `ω`
(`none` if some of these runs never reaches a completed state). -/
noncomputable def stateAt (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : Option (DynBrooks.Config w) :=
  DynBrooks.stateFrom P ω (DynBrooks.complete P ω (initConfig w inp))
    ((σ.take t).map DynBrooks.Update.words)

/-- The worst-case time of update `t` (0-based): the number of steps from delivering its words to the
completed state after update `t` to the next completed state; `⊤` if the run never completes or the
earlier runs did not complete. -/
noncomputable def updateTime (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : ℕ∞ :=
  match stateAt P ω inp σ t, σ[t]? with
  | some s, some x => DynBrooks.time P ω (DynBrooks.feed s x.words)
  | _, _ => ⊤

/-- `TimeLE T b`: the (possibly infinite) step count `T` is finite and at most the real `b`. -/
def TimeLE (T : ℕ∞) (b : ℝ) : Prop :=
  ∃ m : ℕ, T = (m : ℕ∞) ∧ (m : ℝ) ≤ b

/-- Every word the machine has written up to the completed state after the first `t` updates
(empty if that state is not reached). -/
noncomputable def outputAt (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : List ℕ :=
  match stateAt P ω inp σ t with
  | some s => s.output
  | none => []

/-- Apply a change log of pairs `v, q` ("`χ(v) := q`") to a coloring, in order. A pair whose first
word is not a vertex is ignored, as is a single trailing word. -/
def applyColorLog {n : ℕ} : (Fin n → ℕ) → List ℕ → (Fin n → ℕ)
  | χ, v :: q :: rest =>
      applyColorLog (if h : v < n then Function.update χ ⟨v, h⟩ q else χ) rest
  | χ, _ => χ

/-- The explicit coloring `χ_t` after update `t`: the all-`1` coloring with every pair the machine has
written so far applied in order. -/
noncomputable def colorAt (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    {n : ℕ} (σ : List (DynBrooks.Update n)) (t : ℕ) : Fin n → ℕ :=
  applyColorLog (fun _ => 1) (outputAt P ω inp σ t)

open Classical in
/-- The number of vertices whose color differs between two colorings. -/
noncomputable def recolored {n : ℕ} (χ χ' : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun v : Fin n => χ v ≠ χ' v).card

/-- A proper `(Δ+1)`-coloring of `G`: every color lies in `{1, …, Δ+1}` and adjacent vertices get
different colors. -/
def IsProperDeltaPlusOne {n : ℕ} (Δ : ℕ) (G : SimpleGraph (Fin n)) (χ : Fin n → ℕ) : Prop :=
  (∀ v, 1 ≤ χ v ∧ χ v ≤ Δ + 1) ∧ ∀ u v, G.Adj u v → χ u ≠ χ v

end DynColorWC.Main


