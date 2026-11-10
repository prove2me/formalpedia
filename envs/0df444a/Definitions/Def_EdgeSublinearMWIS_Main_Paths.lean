-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_Paths
-- name    : EdgeSublinearMWIS_Main_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:41:02.611213+00:00
-- url     : https://prove2.me/theorems/c8ee9978-28b4-4bd7-a52b-579a82828738
-- title:
--   Endpoint-inclusive flows, path laws and almost-embeddings
-- statement:
--   An ordered simple path is a nonempty vertex sequence with no repetitions and adjacent consecutive vertices. A diagonal path is the singleton sequence. A unit all-pairs flow has one unit of demand for every ordered pair, including equal endpoints, and loads count both endpoints. A separation has nonempty overlapping sides covering all vertices, with no edge between their differences.
--
--   A path law on an induced vertex set $W$ satisfies
--   $$\Pr[(\operatorname{first}Q,\operatorname{last}Q)=(u,v)]=|W|^{-2},\qquad \Pr[v\in Q]\le\ell x_v/x(V).$$
--   The full alternative also requires $|W|>2n/3$. Sparse real lists represent every such law because the set of simple paths in a finite graph is finite; rational lists encode algorithm outputs. An almost-embedding maps vertices and represents each edge by a path, requiring disjointness only for nonincident edges. The vertex map need not be injective. The induced version also forbids adjacencies between those paths.
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), §3.1, Eqs. (4)–(6); §3.2, p.7 (PDF p.7), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

/-- Ordered, nonempty simple paths; the diagonal path is necessarily a singleton. -/
def SimplePath {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (p : List (Fin n)) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ (∀ v ∈ p, v ∈ W) ∧ p.IsChain G.Adj

def HasEndpoints {n : ℕ} (p : List (Fin n)) (u v : Fin n) : Prop :=
  p.head? = some u ∧ p.getLast? = some v

def SparseValid {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) : Prop :=
  ∀ e ∈ f, 0 ≤ e.2 ∧ SimplePath G W e.1

noncomputable def endpointMass {n : ℕ} (f : List (List (Fin n) × ℝ))
    (u v : Fin n) : ℝ := by
  classical
  exact ((f.filter (fun e => HasEndpoints e.1 u v)).map Prod.snd).sum

noncomputable def vertexMass {n : ℕ} (f : List (List (Fin n) × ℝ)) (v : Fin n) : ℝ := by
  classical
  exact ((f.filter (fun e => v ∈ e.1)).map Prod.snd).sum

def realPaths {n : ℕ} (f : List (List (Fin n) × ℚ)) : List (List (Fin n) × ℝ) :=
  f.map (fun e => (e.1, (e.2 : ℝ)))

def UnitFlow {n : ℕ} (G : SimpleGraph (Fin n)) (f : List (List (Fin n) × ℚ)) : Prop :=
  SparseValid G Finset.univ (realPaths f) ∧
    ∀ u v, endpointMass (realPaths f) u v = 1

def Separation {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ A ∪ B = Finset.univ ∧
    TreewidthApprox.Pushed.NoEdge G (A \ B) (B \ A)

/-- The complete event in item 2 of Lemma 8, for arbitrary real costs and laws. -/
def PathOutcome {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (ell : ℝ)
    (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ)) : Prop :=
  2 * n < 3 * W.card ∧ SparseValid G W f ∧ (f.map Prod.snd).sum = 1 ∧
    (∀ u ∈ W, ∀ v ∈ W, endpointMass f u v = 1 / (W.card : ℝ) ^ 2) ∧
    ∀ v ∈ W, vertexMass f v ≤ ell * x v / vertexSum x Finset.univ

abbrev EdgeIndex {h : ℕ} (H : SimpleGraph (Fin h)) :=
  {e : Fin h × Fin h // e.1 < e.2 ∧ H.Adj e.1 e.2}

structure AlmostEmbedding {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n)) where
  vertex : Fin h → Fin n
  path : EdgeIndex H → List (Fin n)
  valid : ∀ e, SimplePath G Finset.univ (path e) ∧
    HasEndpoints (path e) (vertex e.val.1) (vertex e.val.2)
  disjoint : ∀ e f, e.val.1 ≠ f.val.1 → e.val.1 ≠ f.val.2 →
    e.val.2 ≠ f.val.1 → e.val.2 ≠ f.val.2 →
    ∀ v ∈ path e, v ∉ path f

def AlmostEmbedding.Induced {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) : Prop :=
  ∀ e f, e.val.1 ≠ f.val.1 → e.val.1 ≠ f.val.2 →
    e.val.2 ≠ f.val.1 → e.val.2 ≠ f.val.2 →
    ∀ u ∈ E.path e, ∀ v ∈ E.path f, ¬ G.Adj u v

noncomputable def flowInput {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode)
    (γ : RationalCode) : List Bool := graphBits G ++ rationalData x γ

end EdgeSublinearMWIS.Main


