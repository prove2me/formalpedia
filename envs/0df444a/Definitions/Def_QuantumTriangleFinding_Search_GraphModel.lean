-- Prove2me | Definitions.Def_QuantumTriangleFinding_Search_GraphModel
-- name    : QuantumTriangleFinding_Search_GraphModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:58.710412+00:00
-- url     : https://prove2.me/theorems/bd6c27e8-63e9-4e4c-b729-b16ebc2596b7
-- title:
--   Triangle search, full adjacency queries and conditioned input laws
-- statement:
--   Let $G$ be any finite simple undirected host on $\{0,\ldots,N-1\}$, with edge set $I$, $m$ edges, maximum degree $\Delta$ and $M$ triangles. A bit string $x:I\to\{0,1\}$ specifies an unknown subgraph. An edge is stored once with its endpoints sorted. Every ordered adjacency query is allowed: both orientations read the same edge; loops and host nonedges return zero. An output is an unordered vertex set or failure, and is valid exactly when it contains three distinct pairwise adjacent vertices.
--
--   The published query circuit has an arbitrary unit start, arbitrary input-independent unitaries, the controlled phase oracle, arbitrary finite ancillary space, and a fixed final basis decoder. Its actual search success is
--   $$s_A(x)=\sum_{o\text{ a valid triangle of }x}\Pr[A^x=o].$$
--   This is a search relation, with no condition on outputs at triangle-free inputs.
--
--   Let $\nu_p$ be the independent-edge law and let $\mu_-$ be its normalized restriction to triangle-free inputs. For each host triangle $T$, pin its edges to one, draw all other edges independently with probability $p$, and condition on $T$ being the unique triangle, obtaining $\mu_T$. The labeled positive law and average search probability are
--   $$\mu_+(T,y)=\frac{\mu_T(y)}M,\qquad \sigma_A=\sum_{T,y}\mu_+(T,y)s_A(y).$$
--   The label $T$ appears only in analysis; the circuit receives only adjacency queries to $y$. For $0<p<1$, the zero negative input and the input containing only $T$ ensure the required conditioning probabilities are positive. Using the complete host represents every simple graph on $N$ vertices.
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), §3.2, pp. 13–15; §5, pp. 25–26; (5.3), p. 26

import Definitions.Def_QuantumTriangleFinding_Search_ConditionalOperators
import Definitions.Def_QAlgorithms_Defs_Query

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Section 5, p.25: each undirected host edge occurs once, with sorted endpoints. -/
abbrev Edge {N : ℕ} (G : SimpleGraph (Fin N)) :=
  {uv : Fin N × Fin N // uv.1 < uv.2 ∧ G.Adj uv.1 uv.2}
noncomputable instance edgeFintype {N : ℕ} (G : SimpleGraph (Fin N)) : Fintype (Edge G) :=
  Fintype.ofFinite _
noncomputable instance edgeDecidableEq {N : ℕ} (G : SimpleGraph (Fin N)) : DecidableEq (Edge G) :=
  Classical.decEq _

/-- Triangles are unordered three-vertex cliques; their three-edge sets are computed below. -/
abbrev Triangle {N : ℕ} (G : SimpleGraph (Fin N)) :=
  {S : Finset (Fin N) // S.card = 3 ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v}
noncomputable instance triangleFintype {N : ℕ} (G : SimpleGraph (Fin N)) : Fintype (Triangle G) :=
  Fintype.ofFinite _
noncomputable instance triangleDecidableEq {N : ℕ} (G : SimpleGraph (Fin N)) : DecidableEq (Triangle G) :=
  Classical.decEq _

def triangleEdges {N : ℕ} {G : SimpleGraph (Fin N)} (T : Triangle G) : Finset (Edge G) := by
  classical
  exact Finset.univ.filter fun e => e.val.1 ∈ T.val ∧ e.val.2 ∈ T.val

def trianglePatterns {N : ℕ} (G : SimpleGraph (Fin N)) : Finset (Finset (Edge G)) := by
  classical
  exact Finset.univ.image triangleEdges

def starEdges {N : ℕ} (G : SimpleGraph (Fin N)) (w : Fin N) : Finset (Edge G) := by
  classical
  exact Finset.univ.filter fun e => e.val.1 = w ∨ e.val.2 = w

def maxDegree {N : ℕ} (G : SimpleGraph (Fin N)) : ℕ :=
  Finset.univ.sup fun w => (starEdges G w).card

def edgeCount {N : ℕ} (G : SimpleGraph (Fin N)) : ℕ := Fintype.card (Edge G)
def triangleCount {N : ℕ} (G : SimpleGraph (Fin N)) : ℕ := Fintype.card (Triangle G)

/-- Full adjacency-matrix queries, including reverse edges, host nonedges and loops.
All known zero answers are explicit. -/
def adjacencyBits {N : ℕ} (G : SimpleGraph (Fin N)) (x : Edge G → Bool) :
    (Fin N × Fin N) → Bool := by
  classical
  exact fun uv => if h : uv.1 < uv.2 ∧ G.Adj uv.1 uv.2 then x ⟨uv, h⟩
    else if h : uv.2 < uv.1 ∧ G.Adj uv.2 uv.1 then x ⟨(uv.2, uv.1), h⟩ else false

abbrev TriangleOutput (N : ℕ) := Option (Finset (Fin N))

def ValidTriangle {N : ℕ} (G : SimpleGraph (Fin N)) (x : Edge G → Bool)
    (o : TriangleOutput N) : Prop :=
  ∃ S, o = some S ∧ S.card = 3 ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → adjacencyBits G x (u, v) = true

/-- The search relation is summed over all valid outputs, with `none` as failure. -/
def triangleSuccess {N t : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph (Fin N)) (x : Edge G → Bool)
    (A : QAlgorithms.QueryAlg (Fin N × Fin N) Bool W t)
    (out : ((Fin N × Fin N) × Bool) × W → TriangleOutput N) : ℝ := by
  classical
  exact ∑ o, if ValidTriangle G x o then
    A.outputProb (QAlgorithms.controlledPhaseOracle (adjacencyBits G x)) out o else 0

/-- Section 5.1, p.26: negative inputs use the actual triangle-free conditioned law. -/
def negativeLaw {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ) : (Edge G → Bool) → ℝ :=
  conditionedBernoulli p (trianglePatterns G)

/-- Independent outside edges, and the triangle edges pinned to one. -/
def plantedProduct {N : ℕ} {G : SimpleGraph (Fin N)} (T : Triangle G) (p : ℝ)
    (x : Edge G → Bool) : ℝ := by
  classical
  exact if ∀ e ∈ triangleEdges T, x e = true then
    ∏ e ∈ Finset.univ \ triangleEdges T, if x e then p else 1 - p else 0

def uniqueTriangleEvent {N : ℕ} {G : SimpleGraph (Fin N)} (T : Triangle G) :
    Set (Edge G → Bool) :=
  {x | ∀ S : Triangle G, (∀ e ∈ triangleEdges S, x e = true) ↔ S = T}

def triangleLaw {N : ℕ} {G : SimpleGraph (Fin N)} (T : Triangle G) (p : ℝ) :
    (Edge G → Bool) → ℝ := condition (plantedProduct T p) (uniqueTriangleEvent T)

/-- Equations (5.3): uniform mixture of individually normalized laws, keeping an inaccessible label. -/
def positiveLaw {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ) :
    (Triangle G × (Edge G → Bool)) → ℝ :=
  fun z => triangleLaw z.1 p z.2 / (triangleCount G : ℝ)

def averageTriangleSuccess {N t : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph (Fin N)) (p : ℝ)
    (A : QAlgorithms.QueryAlg (Fin N × Fin N) Bool W t)
    (out : ((Fin N × Fin N) × Bool) × W → TriangleOutput N) : ℝ :=
  ∑ z, positiveLaw G p z * triangleSuccess G z.2 A out

end QuantumTriangleFinding.Search


