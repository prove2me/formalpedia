-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_Cluster
-- name    : DecrNbhdCover_Supplement_Cluster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:27:08.610668+00:00
-- url     : https://prove2.me/theorems/8a8f3744-8e1e-48ad-aa71-726444b3d2b6
-- title:
--   The interface of MaintainCluster in decremental graphs (Theorem 3.27)
-- statement:
--   The input is a graph $G$ with positive integer lengths that initially has $n$ vertices and $m$ edges, and rationals $0<\epsilon<1$, $D>0$. $G$ undergoes edge deletions and vertex deletions, which arrive in batches. The first batch $B_0=\emptyset$ is the initialization, and every later batch is non-empty.
--
--   With a constant $C$, the clauses are:
--
--   1. After each batch $B$ the algorithm returns a bit $g_B\in\{0,1\}$, and if $g_B=0$ it also returns two vertices $v,v'$ of the current $G$ with $\mathrm{dist}_G(v,v')>D$ (the distance may be $\infty$).
--   2. A short-path query $(v,v')$, on two vertices of the current $G$, may be asked only if the bit returned after the most recent batch was $1$. The answer is a $v$-$v'$ path $P$ in $G$ of length at most $2^{C/\epsilon^C}\cdot D$, in at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps.
--   3. The total update time is at most $C\left(n+m^{1+C\epsilon}\cdot2^{C/\epsilon^C}\right)$.
--
--   The bit $1$ is not required when the diameter is small, exactly as in the theorem.
--
--   **Formalization Note** The window of a batch outputs exactly the bit, in the published format of the weak MaintainCluster problem. Paths are walks given by edge numbers.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.27, p.28 (PDF 32)

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Common
import Definitions.Def_DecrNbhdCover_MaintainCluster

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # MaintainCluster in decremental graphs (Theorem 3.27)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Theorem 3.27, p.28 (PDF 32).

**Formalization Note.** The first batch `B₀ = ∅` is the initialization window. A later batch is `0, k, (update words)…`, a nonempty list
of edge and vertex deletions of `G`. After each batch the window's output is exactly the bit, in the published format `ClusterBit`:
`1`, or `0, v, v′` with `distG(v, v′) > D` in the current graph (`∞` allowed). Query: `1, v, v′`, answered with `k, e₁, …, e_k` (edges of
`G`); it is valid only if the bit after the most recent batch was `1`. Input words: `n`, the edge list, `ϵ` and `D` as rationals. -/

/-- An operation: a batch of updates, or a query. -/
inductive CBOp where
  | batch (gs : List GUpdate)
  | query (v v' : ℕ)

namespace CBOp

/-- The words of an operation. -/
def words : CBOp → List ℕ
  | .batch gs => 0 :: gs.length :: gs.flatMap GUpdate.words
  | .query v v' => [1, v, v']

/-- The updates of `G`. -/
def gPart : CBOp → List GUpdate
  | .batch gs => gs
  | .query _ _ => []

/-- Whether an operation is a query. -/
def isQ : CBOp → Bool
  | .batch _ => false
  | .query _ _ => true

end CBOp

/-- The protocol of Theorem 3.27: the state is the last bit, `true` for `1`. -/
def cbProtocol : Protocol CBOp ClusterBit Bool where
  opWords := CBOp.words
  isQuery := CBOp.isQ
  enc := ClusterBit.words
  step := fun _ r => match r with
    | .one => some true
    | .zero _ _ => some false
  st₀ := false

/-- The input of Theorem 3.27. -/
structure CBInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)
  eps : ℚ
  D : ℚ

namespace CBInput

variable (I : CBInput)

/-- The number of edges. -/
def m : ℕ := I.edges.length

/-- The conditions of Theorem 3.27: `n ≥ 1`, `0 < ϵ < 1` and `D > 0`. -/
structure Ok : Prop where
  n_pos : 1 ≤ I.n
  edges_ok : EdgesOk I.n I.edges
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1
  D_pos : 0 < I.D

/-- The initialization words. -/
def words : List ℕ :=
  I.n :: edgeWords I.edges ++ ratWords I.eps ++ ratWords I.D

/-- `G` after the first `t` operations. -/
def Gt (σ : List CBOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map CBOp.gPart) t

/-- Valid operations: a batch is nonempty and its updates are valid in order; a query is asked only if the bit after the most recent
batch was `1`, on two current vertices of `G`. -/
def Valid (W : ℕ) (P : Program) (σ : List CBOp) : Prop :=
  ∀ (t : ℕ) (o : CBOp), σ[t]? = some o →
    match o with
    | .batch gs => gs ≠ [] ∧ gsOk (I.Gt σ t) gs
    | .query v v' => cbProtocol.state W P I.words σ t = some true ∧ v ∈ (I.Gt σ t).V ∧ v' ∈ (I.Gt σ t).V

end CBInput

/-- The output of a batch is the bit `1`, or the bit `0` with two vertices of `G` at distance more than `D`. -/
def BitOkQ (G : Graph ℕ ℕ) (D : ℝ) (out : List ℕ) : Prop :=
  out = [1] ∨ ∃ v v', out = [0, v, v'] ∧ v ∈ G.V ∧ v' ∈ G.V ∧
    ENNReal.ofReal D < ((G.dist v v' : ℕ∞) : ℝ≥0∞)

/-- The clauses of Theorem 3.27 with the constant `C`. -/
structure CBHolds (C W : ℕ) (P : Program) (I : CBInput) (σ : List CBOp) : Prop where
  runs : RunsThrough W P (cbProtocol.blocks I.words σ)
  /-- The answer to `B₀`. -/
  bit₀ : BitOkQ (I.Gt σ 0) (I.D : ℝ) (cbProtocol.out W P I.words σ 0)
  /-- The answer to each later batch. -/
  bit : ∀ (t : ℕ) (gs : List GUpdate), σ[t]? = some (.batch gs) →
    BitOkQ (I.Gt σ (t + 1)) (I.D : ℝ) (cbProtocol.out W P I.words σ (t + 1))
  /-- Queries return a walk in `G` from `v` to `v′` of length at most `2^{C/ϵ^C}·D`. -/
  query : ∀ (t v v' : ℕ), σ[t]? = some (.query v v') →
    ∃ es, cbProtocol.answer W P I.words σ t = some es ∧
      (I.Gt σ t).WalkFromTo v es v' ∧
      ((I.Gt σ t).walkLen es : ℝ) ≤ expEps C (I.eps : ℝ) * (I.D : ℝ) ∧
      (cbProtocol.opTime W P I.words σ t : ℝ) ≤ polylog C I.n I.m * ((es.length : ℝ) + 1)
  /-- The total update time `C·(n + m^{1+Cϵ}·2^{C/ϵ^C})`. -/
  time : (cbProtocol.updateTime W P I.words σ : ℝ) ≤
    (C : ℝ) * ((I.n : ℝ) + (I.m : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ)) * expEps C (I.eps : ℝ))

end DecrNbhdCover.Supplement


