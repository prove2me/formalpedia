-- Prove2me | Definitions.Def_DecrNbhdCover_MaintainCluster
-- name    : DecrNbhdCover_MaintainCluster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:10.7285+00:00
-- url     : https://prove2.me/theorems/9ae38054-dfbb-48d4-abe9-6e6e32d71803
-- title:
--   The weak MaintainCluster problem (Definition 3.16)
-- statement:
--   The input has $\mu\ge1$, $0<\epsilon<1/400$, integers $0<d<D$, a decremental graph $G$ with maximum degree at most $\mu$, and a partial $(\epsilon,d,D)$-emulator $H$ for $G$ with dynamic degree bound $\mu$. Updates arrive in batches; the first batch $B_0=\emptyset$ arrives at the start and later ones are nonempty.
--
--   After each batch $B$ the algorithm returns a bit $g_B$; if $g_B=0$, it supplies $v,v'\in V$ with $\mathrm{dist}_G(v,v')>D$. A short-path query $(v,v')$, allowed only if the most recent bit is $1$, returns a path in $H$ of length at most $\alpha D$ with no consecutively repeated regular vertices, in time $\tilde O(|E(P)|)$.
--
--   This is what maintains each candidate cluster in the neighborhood cover construction.
--
--   **Formalization Note** Each batch's window outputs exactly the bit, with its pair if the bit is $0$.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Definition 3.16, p.22 (PDF 26)

import Mathlib
import Definitions.Def_DecrNbhdCover_Emulator
import Definitions.Def_DecrNbhdCover_Streams
import Definitions.Def_DecrNbhdCover_Session

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-! # The weak MaintainCluster problem (Definition 3.16)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Definition 3.16, p.22.

**Formalization Note.** The first batch `B₀ = ∅` is the initialization window. After each batch the window's output is exactly the bit: `1`, or `0, v, v′` with `distG(v, v′) > D`. Query: `1, v, v′`, answered
with `k, e₁, …, e_k` (edges of `H`). A query is valid only if the bit of the most recent batch was `1`. -/

/-- The answer to a batch. -/
inductive ClusterBit where
  | one
  | zero (v v' : ℕ)

/-- The words of the answer. -/
def ClusterBit.words : ClusterBit → List ℕ
  | .one => [1]
  | .zero v v' => [0, v, v']

/-- An operation: a nonempty batch of updates to `G` and `H`, or a query. -/
inductive ClusterOp where
  | batch (gs : List GUpdate) (hs : List HUpdate)
  | query (v v' : ℕ)

namespace ClusterOp

/-- The words of an operation. -/
def words : ClusterOp → List ℕ
  | .batch gs hs => 0 :: batchWords gs hs
  | .query v v' => [1, v, v']

/-- The updates of `G`. -/
def gPart : ClusterOp → List GUpdate
  | .batch gs _ => gs
  | .query _ _ => []

/-- The updates of `H`. -/
def hPart : ClusterOp → List HUpdate
  | .batch _ hs => hs
  | .query _ _ => []

/-- Whether an operation is a query. -/
def isQ : ClusterOp → Bool
  | .batch _ _ => false
  | .query _ _ => true

end ClusterOp

/-- The protocol of weak MaintainCluster: the state is the last bit, `true` for `1`. -/
def clusterProtocol : Protocol ClusterOp ClusterBit Bool where
  opWords := ClusterOp.words
  isQuery := ClusterOp.isQ
  enc := ClusterBit.words
  step := fun _ r => match r with
    | .one => some true
    | .zero _ _ => some false
  st₀ := false

/-- The input of the weak MaintainCluster problem. -/
structure ClusterInput where
  n : ℕ
  mu : ℕ
  edges : List (ℕ × ℕ × ℕ)
  h₀ : List (List (ℕ × ℕ))
  eps : ℚ
  d : ℕ
  D : ℕ

namespace ClusterInput

variable (I : ClusterInput)

/-- The conditions of Definition 3.16 that do not concern the update stream. -/
structure Ok : Prop where
  n_pos : 1 ≤ I.n
  mu_pos : 1 ≤ I.mu
  edges_ok : EdgesOk I.n I.edges
  deg : (ofEdges I.n I.edges).DegLe I.mu
  h_ok : hInitOk I.n I.h₀
  eps_pos : 0 < I.eps
  eps_lt : I.eps < 1 / 400
  d_pos : 0 < I.d
  d_lt : I.d < I.D

/-- The initialization words. -/
def words : List ℕ :=
  [I.n, I.mu, I.d, I.D] ++ edgeWords I.edges ++ hInitWords I.h₀ ++ ratWords I.eps

/-- `G` after the first `t` operations. -/
def Gt (σ : List ClusterOp) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map ClusterOp.gPart) t

/-- `H` after the first `t` operations. -/
noncomputable def Ht (σ : List ClusterOp) (t : ℕ) : HState :=
  hAt (hInit I.n I.h₀) (σ.map ClusterOp.hPart) t

/-- The promise on the input stream: batches are nonempty and valid, and `H` is a partial `(ϵ, d, D)`-emulator for `G` after each batch, with dynamic degree bound `μ`. -/
structure Promise (σ : List ClusterOp) : Prop where
  steps : ∀ (t : ℕ) (gs : List GUpdate) (hs : List HUpdate), σ[t]? = some (.batch gs hs) →
    (gs ≠ [] ∨ hs ≠ []) ∧ gsOk (I.Gt σ t) gs ∧ hsOk (I.Ht σ t) hs
  partial' : ∀ t ≤ σ.length, IsPartial (I.Gt σ t) (I.Ht σ t).g (I.eps : ℝ) I.d (I.D : ℝ)
  deg : (I.Ht σ σ.length).EverDegLe I.mu

/-- A query is asked only if the bit of the most recent batch was `1`, on two current vertices of `G`. -/
def QueriesOk (W : ℕ) (P : Program) (σ : List ClusterOp) : Prop :=
  ∀ (t v v' : ℕ), σ[t]? = some (.query v v') →
    clusterProtocol.state W P I.words σ t = some true ∧ v ∈ (I.Gt σ t).V ∧ v' ∈ (I.Gt σ t).V

end ClusterInput

/-- The output of a batch at time `t` is the bit `1`, or the bit `0` with a pair at distance more than `D`. -/
def BitOk (G : Graph ℕ ℕ) (D : ℕ) (out : List ℕ) : Prop :=
  out = [1] ∨ ∃ v v', out = [0, v, v'] ∧ v ∈ G.V ∧ v' ∈ G.V ∧
    ((D : ℕ∞) : ℝ≥0∞) < ((G.dist v v' : ℕ∞) : ℝ≥0∞)

/-- The clauses of the weak MaintainCluster problem, with approximation factor `2^{C/ϵ^C}` and the time bound of Theorem 3.17. -/
structure ClusterHolds (C W : ℕ) (P : Program) (I : ClusterInput) (σ : List ClusterOp) : Prop where
  runs : RunsThrough W P (clusterProtocol.blocks I.words σ)
  /-- The answer to `B₀`. -/
  bit₀ : BitOk (I.Gt σ 0) I.D (clusterProtocol.out W P I.words σ 0)
  /-- The answer to each later batch. -/
  bit : ∀ (t : ℕ) (gs : List GUpdate) (hs : List HUpdate), σ[t]? = some (.batch gs hs) →
    BitOk (I.Gt σ (t + 1)) I.D (clusterProtocol.out W P I.words σ (t + 1))
  /-- Queries return a path in `H` with no consecutively repeated regular vertices, of length at most `2^{C/ϵ^C}·D`. -/
  query : ∀ (t v v' : ℕ), σ[t]? = some (.query v v') →
    ∃ es, clusterProtocol.answer W P I.words σ t = some es ∧
      (I.Ht σ t).g.NoRepeatPath v es v' ∧
      ((I.Ht σ t).g.walkLen es : ℝ) ≤ expEps C (I.eps : ℝ) * (I.D : ℝ) ∧
      (clusterProtocol.opTime W P I.words σ t : ℝ) ≤ polylog C I.n I.edges.length * ((es.length : ℝ) + 1)
  /-- The total update time. -/
  time : (clusterProtocol.updateTime W P I.words σ : ℝ) ≤
    (C : ℝ) * (I.n : ℝ) ^ (1 + (C : ℝ) * (I.eps : ℝ)) * ((I.D : ℝ) * (I.mu : ℝ) / (I.d : ℝ)) ^ C *
      expEps C (I.eps : ℝ)

end DecrNbhdCover


