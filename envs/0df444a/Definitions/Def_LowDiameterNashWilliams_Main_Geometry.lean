-- Prove2me | Definitions.Def_LowDiameterNashWilliams_Main_Geometry
-- name    : LowDiameterNashWilliams_Main_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:15.041197+00:00
-- url     : https://prove2.me/theorems/b4393a8e-8f06-4132-b121-582fc4105f57
-- title:
--   Finite simple hosts, tree geometry, orientations and integer weights
-- statement:
--   A host has vertices $V=\{0,\ldots,n-1\}$, edge identities $E=\{0,\ldots,m-1\}$ and an injective unordered endpoint map with no loops. Spanning trees and edge-disjoint packings use the referenced multigraph definitions. A tree partition covers every host edge exactly once. A leaf has degree one; $\operatorname{int}(T)$ comprises vertices of degree at least two. Distances count edges and diameter maximizes over vertex pairs:
--
--   $$d_T(u,v)=\inf_{P:u\leadsto v}|P|,\qquad \operatorname{diam}(T)=\max_{u,v}d_T(u,v).$$
--
--   A missing path has infinite distance; a singleton tree has diameter zero and no internal vertices. Minimum degree is computed from all host edges, with value zero on an empty vertex type. An orientation points each selected edge from its tail to its head. A rooted tree points toward the root when the root has outdegree zero and every other vertex has outdegree one. Outgoing-neighbor counts, tight sets and their exceptional vertices implement Section 3 exactly. Tight sets are nonempty and have $k(|A|-1)$ induced edges. The exceptional set contains the root and every vertex with a nontrivial tight witness and at least $3k/4$ outgoing arcs leaving that witness.
--
--   For $L\subseteq V$, $w(e)=|e\cap L|$. Integer edge weights are summed without truncation. The maximum spanning-tree weight is the maximum over the finite family of all host spanning trees; its empty-family fallback is zero, unused under any theorem hypothesis. An extractable tree leaves an exact partition into $k-1$ spanning trees. Leaf counts and internal counts use the indicated tree indices, and the first half means the first $\lceil k/2\rceil$ trees. These are shared interfaces for the structural milestones.
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Section 2 and Sections 3–6, pp. 4–25 (PDF pp. 5–26)

import Mathlib
import Definitions.Def_NashWilliams61_TreePacking_Graphs

set_option autoImplicit false
open scoped BigOperators
open scoped ENNReal NNReal
open Classical
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main

/-! Section 2 (printed pp. 4–5): finite labelled hosts; all edge sets refer to the same
undirected edge identities. Geometry uses extended distances so a missing path is infinite. -/
abbrev Edges (m : ℕ) := Finset (Fin m)
abbrev Trees (k m : ℕ) := Fin k → Edges m
abbrev Direction (n m : ℕ) := Fin m → Fin n × Fin n

def Simple {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) : Prop :=
  Function.Injective ends ∧ ∀ e, ¬ (ends e).IsDiag

def Packing {n m k : ℕ} (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) : Prop :=
  (∀ i, IsSpanningTree ends (T i)) ∧ ∀ i j, i ≠ j → Disjoint (T i) (T j)

def TreePartition {n m k : ℕ} (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) : Prop :=
  Packing ends T ∧ Finset.univ.biUnion T = Finset.univ

noncomputable def internal {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (T : Edges m) : Finset (Fin n) :=
  Finset.univ.filter fun v => 2 ≤ degIn ends T v

noncomputable def distance {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (T : Edges m)
    (u v : Fin n) : ℝ≥0∞ :=
  ⨅ p : (edgeGraph ends T).Walk u v, (p.length : ℝ≥0∞)

noncomputable def diameter {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (T : Edges m) : ℝ≥0∞ :=
  ⨆ u : Fin n, ⨆ v : Fin n, distance ends T u v

noncomputable def minDegree {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) : ℕ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then
    Finset.univ.inf' h (degIn ends Finset.univ) else 0

noncomputable def outdegree {n m : ℕ} (F : Edges m) (D : Direction n m) (v : Fin n) : ℕ :=
  (F.filter fun e => (D e).1 = v).card

def Orients {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (F : Edges m) (D : Direction n m) : Prop :=
  ∀ e ∈ F, ends e = s((D e).1, (D e).2)

def Toward {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (F : Edges m)
    (D : Direction n m) (r : Fin n) : Prop :=
  Orients ends F D ∧ outdegree F D r = 0 ∧ ∀ v, v ≠ r → outdegree F D v = 1

noncomputable def outgoingTo {n m k : ℕ} (T : Trees k m) (D : Fin k → Direction n m)
    (v : Fin n) (A : Finset (Fin n)) : ℕ :=
  ∑ i, ((T i).filter fun e => (D i e).1 = v ∧ (D i e).2 ∈ A).card

noncomputable def tight {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (k : ℕ) (A : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ ((edgesIn ends A).card : ℤ) = (k : ℤ) * ((A.card : ℤ) - 1)

noncomputable def exceptional {n m k : ℕ} (ends : Fin m → Sym2 (Fin n))
    (T : Trees k m) (D : Fin k → Direction n m) (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => v = r ∨ ∃ A : Finset (Fin n),
    v ∈ A ∧ 2 ≤ A.card ∧ tight ends k A ∧
      (3 : ℝ) * k / 4 ≤ outgoingTo T D v (Finset.univ \ A)

noncomputable def incidenceWeight {n m : ℕ} (ends : Fin m → Sym2 (Fin n))
    (L : Finset (Fin n)) (e : Fin m) : ℤ :=
  ((L.filter fun v => v ∈ ends e).card : ℤ)

def weight {m : ℕ} (f : Fin m → ℤ) (F : Edges m) : ℤ := ∑ e ∈ F, f e

/-- Finite integer maximum; the empty-family fallback is zero and is never used under
any theorem hypothesis (a tree partition supplies at least one tree). -/
noncomputable def maxTreeWeight {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (f : Fin m → ℤ) : ℤ :=
  let values := ((Finset.univ : Edges m).powerset.filter (IsSpanningTree ends)).image (weight f)
  if h : values.Nonempty then values.max' h else 0

def Extractable {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (k : ℕ) (Q : Edges m) : Prop :=
  IsSpanningTree ends Q ∧ ∃ U : Trees (k - 1) m,
    (∀ i, IsSpanningTree ends (U i)) ∧
    (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
    Finset.univ.biUnion U = Finset.univ \ Q

noncomputable def leafCount {n m k : ℕ} (ends : Fin m → Sym2 (Fin n))
    (T : Trees k m) (J : Finset (Fin k)) (v : Fin n) : ℕ :=
  (J.filter fun j => degIn ends (T j) v = 1).card

noncomputable def internalCount {n m k : ℕ} (ends : Fin m → Sym2 (Fin n))
    (T : Trees k m) (I : Finset (Fin k)) (v : Fin n) : ℕ :=
  (I.filter fun i => v ∈ internal ends (T i)).card

noncomputable def firstHalf (k : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun i => i.val < (k + 1) / 2

/-- Both bounds concern the same family. -/
noncomputable def GoodPacking {n m k : ℕ} (ends : Fin m → Sym2 (Fin n))
    (D I : ℝ) (T : Trees k m) : Prop :=
  Packing ends T ∧ ∀ i, diameter ends (T i) ≤ ENNReal.ofReal D ∧
    ((internal ends (T i)).card : ℝ) ≤ I

end LowDiameterNashWilliams.Main


