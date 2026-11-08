-- Prove2me | Definitions.Def_DecrNbhdCover_ApproxBall
-- name    : DecrNbhdCover_ApproxBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:00.820688+00:00
-- url     : https://prove2.me/theorems/3352c234-da55-4c76-8f4b-594979ca0779
-- title:
--   The weak ApproxBall problem (Definition 3.14)
-- statement:
--   The input has a decremental graph $G$ with $n$ vertices initially and maximum degree at most $\mu$, a decremental set $S\subseteq V(G)$, $0<\epsilon<1/400$, an integer $0<d<D$ and a partial $(\epsilon,d,D)$-emulator $H$ for $G$ with dynamic degree bound $\mu$.
--
--   The goal is a decremental set $S'\subseteq V(G)$ with $B_G(S,10D/\epsilon^2)\subseteq S'$ and, for $v\in S'$, a value $\tilde d(v)$ that does not decrease, with
--   $$\mathrm{dist}_H(S,v)\le\tilde d(v)\le32D/\epsilon^2,\qquad \tilde d(v)\le(1+\epsilon)\mathrm{dist}_G(S,v)+\epsilon D,$$
--   all changes being reported. A query $v\in S'$ is answered by a simple path in $H$ from $v$ to a vertex of $S$, of length at most $\tilde d(v)$, in time $\tilde O(|E(P)|)$.
--
--   This is the shell-maintenance tool used in §5 and §7.
--
--   **Formalization Note** $\tilde d$ values are reported as rationals. The strong problem of Definition 3.14 is not on the goal's proof path as a separate statement.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Definition 3.14, p.21 (PDF 25)

import Mathlib
import Definitions.Def_DecrNbhdCover_Emulator
import Definitions.Def_DecrNbhdCover_Streams
import Definitions.Def_DecrNbhdCover_Session

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-! # The weak ApproxBall problem (Definition 3.14)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Definition 3.14, p.21.

**Formalization Note.** Input words: `n, μ, d`, the edge list of `G`, the initial `H`, the initial `S`, `ϵ` and `D` (rationals). An update step carries at most one update of `G`, updates of `H`
accompanying it, and deletions from `S`; `S ⊆ V(G)` and the emulator property are promised after every step. The set `S′` and the values `d̃` are reported as rationals: `0, v, p, q` sets
`d̃(v) = p/q` (`v` joins `S′` if it was not in it), `1, v` removes `v` from `S′`. That `S′` is decremental and that `d̃` does not decrease are stated clauses, so every change is
explicitly reported and no other change is allowed. Query: `1, v`, answered with `k, e₁, …, e_k` (edges of `H`). -/

/-- A report: set `d̃(v) = p/q`, or remove `v` from `S′`. -/
inductive BallReport where
  | set (v p q : ℕ)
  | leave (v : ℕ)

/-- The words of a report. -/
def BallReport.words : BallReport → List ℕ
  | .set v p q => [0, v, p, q]
  | .leave v => [1, v]

/-- The current `S′` with its values: `some x` for `v ∈ S′` with `d̃(v) = x`. -/
abbrev BallState := ℕ → Option ℚ

/-- The effect of a report; a zero denominator is illegal. -/
def ballStep (s : BallState) : BallReport → Option BallState
  | .set v p q => if q = 0 then none else some (Function.update s v (some ((p : ℚ) / (q : ℚ))))
  | .leave v => some (Function.update s v none)

/-- An operation: a step of updates, or a query `shortest-path(v)`. -/
inductive BallOp where
  | batch (gs : List GUpdate) (hs : List HUpdate) (ss : List ℕ)
  | query (v : ℕ)

namespace BallOp

/-- The words of an operation. -/
def words : BallOp → List ℕ
  | .batch gs hs ss => 0 :: batchWords gs hs ++ ss.length :: ss
  | .query v => [1, v]

/-- The updates of `G`. -/
def gPart : BallOp → List GUpdate
  | .batch gs _ _ => gs
  | .query _ => []

/-- The updates of `H`. -/
def hPart : BallOp → List HUpdate
  | .batch _ hs _ => hs
  | .query _ => []

/-- The deletions from `S`. -/
def sPart : BallOp → List ℕ
  | .batch _ _ ss => ss
  | .query _ => []

/-- Whether an operation is a query. -/
def isQ : BallOp → Bool
  | .batch _ _ _ => false
  | .query _ => true

end BallOp

/-- The protocol of weak ApproxBall. -/
def ballProtocol : Protocol BallOp BallReport BallState where
  opWords := BallOp.words
  isQuery := BallOp.isQ
  enc := BallReport.words
  step := ballStep
  st₀ := fun _ => none

/-- The input of the weak ApproxBall problem: `G` on `n` vertices, `H`, the initial set `S`, and the parameters. -/
structure BallInput where
  n : ℕ
  mu : ℕ
  edges : List (ℕ × ℕ × ℕ)
  h₀ : List (List (ℕ × ℕ))
  S₀ : List ℕ
  eps : ℚ
  d : ℕ
  D : ℚ

namespace BallInput

variable (I : BallInput)

/-- The conditions of Definition 3.14 for the weak problem that do not concern the update stream. `S` is a set, so its list has
no repeated vertex. -/
structure Ok : Prop where
  n_pos : 1 ≤ I.n
  edges_ok : EdgesOk I.n I.edges
  deg : (ofEdges I.n I.edges).DegLe I.mu
  mu_pos : 1 ≤ I.mu
  h_ok : hInitOk I.n I.h₀
  S_sub : ∀ v ∈ I.S₀, v < I.n
  S_nodup : I.S₀.Nodup
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1 / 400
  d_pos : 0 < I.d
  d_lt : (I.d : ℚ) < I.D

/-- The initialization words. -/
def words : List ℕ :=
  [I.n, I.mu, I.d] ++ edgeWords I.edges ++ hInitWords I.h₀ ++ I.S₀.length :: I.S₀ ++ ratWords I.eps ++ ratWords I.D

/-- `G` after the first `t` operations. -/
def Gt (σ : List BallOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map BallOp.gPart) t

/-- `H` after the first `t` operations. -/
noncomputable def Ht (σ : List BallOp) (t : ℕ) : HState :=
  hAt (hInit I.n I.h₀) (σ.map BallOp.hPart) t

/-- `S` after the first `t` operations. -/
def St (σ : List BallOp) (t : ℕ) : Set ℕ :=
  {v | v ∈ I.S₀ ∧ ∀ o ∈ σ.take t, v ∉ o.sPart}

/-- The promise on the input stream, except for the emulator property: each step is nonempty and has at most one update of `G`, all updates are valid, a step deletes a vertex of `S` at most once, `S` stays inside `V(G)`, and `H` has dynamic degree
bound `μ`. -/
structure Promise (σ : List BallOp) : Prop where
  steps : ∀ (t : ℕ) (gs : List GUpdate) (hs : List HUpdate) (ss : List ℕ), σ[t]? = some (.batch gs hs ss) →
    gs.length ≤ 1 ∧ (gs ≠ [] ∨ hs ≠ [] ∨ ss ≠ []) ∧ gsOk (I.Gt σ t) gs ∧ hsOk (I.Ht σ t) hs ∧
      ss.Nodup ∧ ∀ v ∈ ss, v ∈ I.St σ t
  S_sub : ∀ t ≤ σ.length, I.St σ t ⊆ (I.Gt σ t).V
  deg : (I.Ht σ σ.length).EverDegLe I.mu

/-- A query names a vertex of `S′`, as reported so far. -/
def QueriesOk (W : ℕ) (P : Program) (σ : List BallOp) : Prop :=
  ∀ (t : ℕ) (v : ℕ), σ[t]? = some (.query v) →
    ∃ s x, ballProtocol.state W P I.words σ t = some s ∧ s v = some x

/-- What Definition 3.14 requires at one moment of the weak problem, with `G`, `H`, `S`. -/
structure BallAt (G : Graph ℕ ℕ) (H : WSGraph ℕ ℕ ℕ) (S : Set ℕ) (s : BallState) (eps D : ℝ) : Prop where
  sub : ∀ v x, s v = some x → v ∈ G.V
  ball_sub : ∀ v ∈ G.ballSet S (10 * D / eps ^ 2), (s v).isSome
  values : ∀ v x, s v = some x →
    0 ≤ (x : ℝ) ∧ ((H.distSet S v : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (x : ℝ) ∧ (x : ℝ) ≤ 32 * D / eps ^ 2 ∧
      ENNReal.ofReal (x : ℝ) ≤ ENNReal.ofReal (1 + eps) * ((G.distSet S v : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (eps * D)

end BallInput

/-- The clauses of the weak ApproxBall problem, with the time bound `C·polylog·n·μ·D/(d·ϵ²)` of Theorem 3.15. -/
structure BallHolds (C W : ℕ) (P : Program) (I : BallInput) (σ : List BallOp) : Prop where
  runs : RunsThrough W P (ballProtocol.blocks I.words σ)
  /-- At every time the log parses and the required properties hold. -/
  log : ∀ t ≤ σ.length, ∃ s, ballProtocol.state W P I.words σ t = some s ∧
    BallInput.BallAt (I.Gt σ t) (I.Ht σ t).g (I.St σ t) s (I.eps : ℝ) (I.D : ℝ)
  /-- `S′` is decremental and, as long as `v` lies in `S′`, `d̃(v)` does not decrease. -/
  mono : ∀ t < σ.length, ∀ s s', ballProtocol.state W P I.words σ t = some s →
    ballProtocol.state W P I.words σ (t + 1) = some s' →
    ∀ v x', s' v = some x' → ∃ x, s v = some x ∧ x ≤ x'
  /-- Queries return a simple path in `H` from `v` to a vertex of `S`, of length at most `d̃(v)`. -/
  query : ∀ (t v : ℕ) (s : BallState) (x : ℚ), σ[t]? = some (.query v) →
    ballProtocol.state W P I.words σ t = some s → s v = some x →
    ∃ es, ballProtocol.answer W P I.words σ t = some es ∧
      (I.Ht σ t).g.SimplePathToSet v es (I.St σ t) ∧ ((I.Ht σ t).g.walkLen es : ℝ) ≤ (x : ℝ) ∧
      (ballProtocol.opTime W P I.words σ t : ℝ) ≤ polylog C I.n I.edges.length * ((es.length : ℝ) + 1)
  /-- The total update time. -/
  time : (ballProtocol.updateTime W P I.words σ : ℝ) ≤
    polylog C I.n I.edges.length * ((I.n : ℝ) * (I.mu : ℝ) * ((I.D : ℝ) / ((I.d : ℝ) * (I.eps : ℝ) ^ 2)))

end DecrNbhdCover


