-- Prove2me | Definitions.Def_DecrNbhdCover_DegreeReduction
-- name    : DecrNbhdCover_DegreeReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:34.367954+00:00
-- url     : https://prove2.me/theorems/b5b623fd-396f-4d46-87be-ff4ecf10dd71
-- title:
--   The input, output and queries of the degree reduction (Claim 2.2)
-- statement:
--   The input has $0<\epsilon<1$, $\Lambda$, an $n$-vertex graph $G$ with $m\ge1$ edges initially and integer lengths $K\le\ell_G(e)\le\Lambda$, where $K=2\lceil64\log(2m)/\epsilon\rceil$, undergoing edge deletions. The output is a dynamic graph $\tilde G$ with $V(G)\subseteq V(\tilde G)$, whose only updates after initialization are edge deletions.
--
--   $\tilde G$ must have $|V(\tilde G)|=n+8m$, maximum degree at most $O(\log\Lambda)$, positive even integer lengths, and $\mathrm{dist}_G\le\mathrm{dist}_{\tilde G}\le(1+\epsilon)\mathrm{dist}_G$ on $V(G)$ at all times. Two kinds of query go with it: translate a path of $\tilde G$ between distinct vertices of $G$ into a path of $G$, and map a non-isolated vertex of $\tilde G$ to a nearby non-isolated vertex of $G$.
--
--   **Formalization Note** $\tilde G$ is reported once, in the initialization window, on vertices $0,\dots,n+8m-1$, with $V(G)$ as the initial segment. $\Lambda$ is a natural number, since lengths are integers.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Claim 2.2, p.15 (PDF 19)

import Mathlib
import Definitions.Def_DecrNbhdCover_Streams
import Definitions.Def_DecrNbhdCover_Session

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-! # The degree-reduction problem of Claim 2.2

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Claim 2.2, p.15.

**Formalization Note.** The program reports `G̃`: `0, ñ, (edge list)` once, in the initialization window, and `1, e` for an edge deletion from `G̃`; so after initialization `G̃` undergoes only edge deletions. Its vertices are `0, …, ñ-1`, and `V(G) = {0, …, n-1}` is the
initial segment: this is the inclusion `V(G) ⊆ V(G̃)`. `Λ` is a natural number: lengths are integers, so a real `Λ` can be replaced by its floor. Operations: `0, e` deletes `e` from `G`; `1, u, v, k, ẽ₁, …, ẽ_k` asks to translate a path of `G̃`, answered with `k′, e₁, …, e_{k′}`;
`2, u` asks for the non-isolated vertex, answered with `v` alone. -/

/-- A report: `G̃` is created, or one of its edges is deleted. -/
inductive TildeReport where
  | create (nt : ℕ) (es : List (ℕ × ℕ × ℕ))
  | del (e : ℕ)

/-- The words of a report. -/
def TildeReport.words : TildeReport → List ℕ
  | .create nt es => 0 :: nt :: edgeWords es
  | .del e => [1, e]

/-- The reported `G̃`: `none` before it is created. -/
abbrev TildeState := Option (Graph ℕ ℕ)

/-- The effect of a report: `G̃` may be created only once, and deleting an edge not present is illegal. -/
noncomputable def tildeStep (s : TildeState) : TildeReport → Option TildeState
  | .create nt es =>
    match s with
    | none => some (some (ofEdges nt es))
    | some _ => none
  | .del e =>
    match s with
    | none => none
    | some g =>
      open Classical in
      if e ∈ g.E then some (some ((GUpdate.delE e).apply g)) else none

/-- An operation: an edge deletion from `G`, a path translation, or a vertex query. -/
inductive DegOp where
  | del (e : ℕ)
  | translate (u v : ℕ) (es : List ℕ)
  | vertex (u : ℕ)

namespace DegOp

/-- The words of an operation. -/
def words : DegOp → List ℕ
  | .del e => [0, e]
  | .translate u v es => 1 :: u :: v :: es.length :: es
  | .vertex u => [2, u]

/-- The updates of `G`. -/
def gPart : DegOp → List GUpdate
  | .del e => [.delE e]
  | _ => []

/-- Whether an operation is a query. -/
def isQ : DegOp → Bool
  | .del _ => false
  | _ => true

end DegOp

/-- The protocol of Claim 2.2. -/
noncomputable def degProtocol : Protocol DegOp TildeReport TildeState where
  opWords := DegOp.words
  isQuery := DegOp.isQ
  enc := TildeReport.words
  step := tildeStep
  st₀ := none

/-- The input of Claim 2.2. -/
structure DegInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)
  eps : ℚ
  Lam : ℕ

namespace DegInput

variable (I : DegInput)

/-- The number of edges. -/
def m : ℕ := I.edges.length

/-- `K = 2⌈64 log(2m)/ϵ⌉`. -/
noncomputable def K : ℕ := 2 * ⌈64 * Real.logb 2 (2 * (I.m : ℝ)) / (I.eps : ℝ)⌉₊

/-- The conditions of Claim 2.2. -/
structure Ok : Prop where
  n_pos : 1 ≤ I.n
  m_pos : 1 ≤ I.m
  edges_ok : EdgesOk I.n I.edges
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1
  len_ge : ∀ t ∈ I.edges, I.K ≤ t.2.2
  len_le : ∀ t ∈ I.edges, t.2.2 ≤ I.Lam

/-- The initialization words. -/
def words : List ℕ :=
  I.n :: edgeWords I.edges ++ ratWords I.eps ++ [I.Lam]

/-- `G` after the first `t` operations. -/
def Gt (σ : List DegOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map DegOp.gPart) t

/-- Valid operations: a present edge is deleted; a translation is asked on a (possibly non-simple) path of the current `G̃` connecting distinct vertices of `G`; a vertex query is asked on a non-isolated vertex of the current `G̃`. -/
def Valid (W : ℕ) (P : Program) (σ : List DegOp) : Prop :=
  ∀ (t : ℕ) (o : DegOp), σ[t]? = some o →
    match o with
    | .del e => e ∈ (I.Gt σ t).E
    | .translate u v es => ∃ g, degProtocol.state W P I.words σ t = some (some g) ∧
        u < I.n ∧ v < I.n ∧ u ≠ v ∧ g.WalkFromTo u es v
    | .vertex u => ∃ g, degProtocol.state W P I.words σ t = some (some g) ∧ g.NonIsolated u

/-- What Claim 2.2 requires of `G̃` at one moment, with `G` the current graph. -/
structure TildeAt (C : ℕ) (G g : Graph ℕ ℕ) : Prop where
  wf : g.WF
  V_sub : G.V ⊆ g.V
  V_card : g.V = {v | v < I.n + 8 * I.m}
  deg : ∀ v ∈ g.V, (((g.incident v).ncard : ℕ) : ℝ) ≤ (C : ℝ) * Real.logb 2 (I.Lam : ℝ)
  even : ∀ e ∈ g.E, Even (g.len e)
  dist_ge : ∀ u ∈ G.V, ∀ v ∈ G.V, G.dist u v ≤ g.dist u v
  dist_le : ∀ u ∈ G.V, ∀ v ∈ G.V,
    ((g.dist u v : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (1 + (I.eps : ℝ)) * ((G.dist u v : ℕ∞) : ℝ≥0∞)

end DegInput

/-- The clauses of Claim 2.2, with the hidden constant `C`. -/
structure DegHolds (C W : ℕ) (P : Program) (I : DegInput) (σ : List DegOp) : Prop where
  runs : RunsThrough W P (degProtocol.blocks I.words σ)
  /-- At every time the log parses, `G̃` exists and has the required properties. -/
  log : ∀ t ≤ σ.length, ∃ g, degProtocol.state W P I.words σ t = some (some g) ∧
    DegInput.TildeAt I C (I.Gt σ t) g
  /-- Path translation in time `O(|E(P̃)|)`: a `u`-`v` path in `G` with `ℓG(P) ≤ ℓ_G̃(P̃)` and `|E(P)| ≥ Ω(ϵ·|E(P̃)|/log(2m))`. -/
  translate : ∀ (t u v : ℕ) (es : List ℕ) (g : Graph ℕ ℕ), σ[t]? = some (.translate u v es) →
    degProtocol.state W P I.words σ t = some (some g) →
    ∃ es', degProtocol.answer W P I.words σ t = some es' ∧
      (I.Gt σ t).WalkFromTo u es' v ∧ (I.Gt σ t).walkLen es' ≤ g.walkLen es ∧
      (I.eps : ℝ) * (es.length : ℝ) ≤ (C : ℝ) * Real.logb 2 (2 * (I.m : ℝ)) * (es'.length : ℝ) ∧
      (degProtocol.opTime W P I.words σ t : ℝ) ≤ (C : ℝ) * ((es.length : ℝ) + 1)
  /-- The vertex query in time `O(1)`: a non-isolated vertex `v` of `G` with `dist_G̃(u, v) ≤ ϵΛ`. -/
  vertex : ∀ (t u : ℕ) (g : Graph ℕ ℕ), σ[t]? = some (.vertex u) →
    degProtocol.state W P I.words σ t = some (some g) →
    ∃ v, degProtocol.out W P I.words σ (t + 1) = [v] ∧ v ∈ (I.Gt σ t).V ∧ (I.Gt σ t).NonIsolated v ∧
      ((g.dist u v : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((I.eps : ℝ) * (I.Lam : ℝ)) ∧
      degProtocol.opTime W P I.words σ t ≤ C
  /-- The total update time `Õ(m + n)`. -/
  time : (degProtocol.updateTime W P I.words σ : ℝ) ≤
    polylog C I.n I.m * ((I.m : ℝ) + (I.n : ℝ))

end DecrNbhdCover


