-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P35
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P35
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:18:24.654263+00:00
-- url     : https://prove2.me/theorems/55c8f5ea-2a37-459d-b2a8-334efce2ec25
-- title:
--   Definitions for Linear programs for entanglement and key distribution in the quantum internet
-- statement:
--   The objects the formalized statements of *Linear programs for entanglement and key distribution in the quantum internet* (arXiv:1809.03120) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `EdgeGraph`: PDF pp.11,17: finite labelled undirected edges, with arbitrary endpoint ordering. Parallel edges are needed for the rounded multigraph. IsSimple is imposed on G'.
--   - `IsSimple`: PDF p.17: G' has one edge per unordered adjacent pair.
--   - `Flow`: PDF pp.11--12: two nonnegative oriented flows per physical undirected edge.
--   - `netSourceOutflow`: PDF p.12, (9): net outgoing flow, counting each labelled edge once.
--   - `SingleFeasible`: PDF p.12, (10): the full feasible single-pair LP, including nonnegativity.
--   - `singlePairFlowValue`: PDF p.12, (10): optimum of the actual flow LP. On the theorem domain the feasible set contains zero, is compact, and the objective is bounded; the supremum is an attained maximum, including at c=0.
--   - `ConcurrentFeasible`: PDF pp.13--14, (18),(20): every commodity and both orientations share c(e).
--   - `totalValue`: PDF p.13, (18), and p.24, (91)--(93): maximum SUM of net source flows.
--   - `worstValue`: PDF p.14, (20), and p.23, (83)--(86): one jointly feasible flow family, with a common slack value bounded by every commodity's net source flow.
--   - `SimpleEdgePath`: PDF p.19, (54): ALL simple directed paths in the undirected graph. The length is bounded by n-1, hence this is a genuinely finite, computed type. Edge labels and vertex order are retained; no free list of paths is supplied.
--   - `pathCount`: PDF pp.20,26--27: finite cardinality of the complete path type.
--   - `copyGraph`: PDF pp.15,17: replace each edge by L(e) individually labelled unit copies.
--   - `Packing`: PDF pp.20,26--28: a SINGLE concurrent packing in the physical multigraph. The disjointness condition ranges across commodities as well as within them. Each path carries actual copy labels, not just an aggregate edge-load bound.
--   - `roundedCopies`: PDF pp.20,26--27: nonnegative real capacities are floored AFTER scaling.
--   - `maxPathCount`: PDF p.26: Lemma 2 uses the maximum, allowing every path count to be zero.
--   - `sumPathCount`: PDF p.27: Lemma 3 uses the SUM, in contrast to Lemma 2.
--   - `TerminalPair`: PDF p.15: one representative per UNORDERED pair of distinct terminals.
--   - `ConnectivityFeasible`: PDF pp.15,30, (32)--(36),(146)--(150): independent full edge budgets for each connectivity test, with a common lower slack. These tests are not concurrent commodities and their loads are NOT summed over terminal pairs.
--   - `connectivityValue`: PDF pp.15,30, (32),(146): the connectivity LP's actual optimized slack.
--   - `cutCapacity`: PDF p.12, (13): cut sum, each undirected edge counted once.
--   - `SteinerCut`: PDF p.15, (29): the finite nonempty collection of cuts separating S.
--   - `steinerValue`: PDF pp.15,30, (29),(145): minimum of computed Steiner cut sums. For |S|>=2 the domain is finite nonempty, so no totalized empty infimum is used.
--   - `LPRow`: PDF p.16: a stored linear constraint, in equality or <= form.
--   - `FiniteLP`: PDF p.16: an LP stores its actual coefficient rows and linear objective.
--   - `coefficientRow`: Store a linear expression by evaluating it on coordinate unit vectors. All callers below are explicitly homogeneous linear combinations.
--   - `indexedRows`: Enumerate one row for each element of a computed finite index type.
--   - `LPVariable`: Common coordinates: oriented commodity flows, directed usage frequencies, and one slack. For the single and total programs the slack is fixed at zero.
--   - `lpFlow`: Read an oriented flow coordinate from the common LP vector.
--   - `lpFrequency`: Read a directed-channel usage frequency.
--   - `lpSlack`: Read the common slack coordinate.
--   - `lpCapacity`: PDF p.12, (11): sum directed weighted frequencies with the same undirected edge. D labels actual orientations; missing orientations contribute no summand.
--   - `optimizedLP`: PDF pp.12--16, (12),(19),(21),(37): complete explicit constraint arrays. independent=true uses a full capacity copy for every pair, as (34) requires. Otherwise all commodities share the same physical edge budget. Endpoint conservation rows are 0=0; fixing the unused slack to zero in the single/total programs adds only a redundant coordinate. Both choices preserve exactly the source's feasible flows and objective values.
--   - `descriptionSize`: Dense coefficient storage: one scalar per matrix entry, right-hand-side entry, and objective entry. No bit complexity or exact-real solver is asserted.
-- source:
--   Linear programs for entanglement and key distribution in the quantum internet, arXiv:1809.03120v3, https://arxiv.org/abs/1809.03120v3

import Mathlib

/-!
Bauml--Azuma--Kato--Elkouss, arXiv:1809.03120v3.
Standalone graph statements, PDF pp.15--16,20,26--28,30.
Operational network statements and source defects are deferred individually.
All new definitions are paper-local. No operational capacity is defined by a flow.
Compilation is pending the batch mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P35

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.11,17: finite labelled undirected edges, with arbitrary endpoint ordering.
Parallel edges are needed for the rounded multigraph. IsSimple is imposed on G'. -/
structure EdgeGraph (n : ℕ) (E : Type) where
  left : E → Fin n
  right : E → Fin n
  separated : ∀ e, left e ≠ right e

/-- PDF p.17: G' has one edge per unordered adjacent pair. -/
def IsSimple {n : ℕ} {E : Type} (G : EdgeGraph n E) : Prop :=
  ∀ e f, ((G.left e = G.left f ∧ G.right e = G.right f) ∨
    (G.left e = G.right f ∧ G.right e = G.left f)) → e = f

/-- PDF pp.11--12: two nonnegative oriented flows per physical undirected edge. -/
abbrev Flow (E : Type) := E → Bool → ℝ

/-- PDF p.12, (9): net outgoing flow, counting each labelled edge once. -/
def netSourceOutflow {n : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (f : Flow E) (v : Fin n) : ℝ :=
  ∑ e, ((if G.left e = v then f e false - f e true else 0) +
    (if G.right e = v then f e true - f e false else 0))

/-- PDF p.12, (10): the full feasible single-pair LP, including nonnegativity. -/
def SingleFeasible {n : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (c : E → ℝ) (s t : Fin n) (f : Flow E) : Prop :=
  (∀ e b, 0 ≤ f e b) ∧ (∀ e, f e false + f e true ≤ c e) ∧
    ∀ v, v ≠ s → v ≠ t → netSourceOutflow G f v = 0

/-- PDF p.12, (10): optimum of the actual flow LP.
On the theorem domain the feasible set contains zero, is compact, and the
objective is bounded; the supremum is an attained maximum, including at c=0. -/
def singlePairFlowValue {n : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (c : E → ℝ) (s t : Fin n) : ℝ :=
  sSup {z | ∃ f, SingleFeasible G c s t f ∧ z = netSourceOutflow G f s}

/-- PDF pp.13--14, (18),(20): every commodity and both orientations share c(e). -/
def ConcurrentFeasible {n r : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (c : E → ℝ) (s t : Fin r → Fin n)
    (f : Fin r → Flow E) : Prop :=
  (∀ i e b, 0 ≤ f i e b) ∧
    (∀ e, ∑ i, (f i e false + f i e true) ≤ c e) ∧
    ∀ i v, v ≠ s i → v ≠ t i → netSourceOutflow G (f i) v = 0

/-- PDF p.13, (18), and p.24, (91)--(93): maximum SUM of net source flows. -/
def totalValue {n r : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (c : E → ℝ) (s t : Fin r → Fin n) : ℝ :=
  sSup {z | ∃ f, ConcurrentFeasible G c s t f ∧
    z = ∑ i, netSourceOutflow G (f i) (s i)}

/-- PDF p.14, (20), and p.23, (83)--(86): one jointly feasible flow family,
with a common slack value bounded by every commodity's net source flow. -/
def worstValue {n r : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (c : E → ℝ) (s t : Fin r → Fin n) : ℝ :=
  sSup {z | ∃ f, ConcurrentFeasible G c s t f ∧
    ∀ i, z ≤ netSourceOutflow G (f i) (s i)}

/-- PDF p.19, (54): ALL simple directed paths in the undirected graph.
The length is bounded by n-1, hence this is a genuinely finite, computed type.
Edge labels and vertex order are retained; no free list of paths is supplied. -/
abbrev SimpleEdgePath {n : ℕ} {E : Type} (G : EdgeGraph n E) (s t : Fin n) :=
  Σ l : Fin n,
    {p : (Fin (l.val + 1) → Fin n) × (Fin l.val → E) //
      Function.Injective p.1 ∧ p.1 0 = s ∧ p.1 (Fin.last l.val) = t ∧
      ∀ i : Fin l.val,
        (G.left (p.2 i) = p.1 i.castSucc ∧ G.right (p.2 i) = p.1 i.succ) ∨
        (G.right (p.2 i) = p.1 i.castSucc ∧ G.left (p.2 i) = p.1 i.succ)}

/-- PDF pp.20,26--27: finite cardinality of the complete path type. -/
def pathCount {n : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (s t : Fin n) : ℕ :=
  Fintype.card (SimpleEdgePath G s t)

/-- PDF pp.15,17: replace each edge by L(e) individually labelled unit copies. -/
def copyGraph {n : ℕ} {E : Type} (G : EdgeGraph n E) (L : E → ℕ) :
    EdgeGraph n (Σ e : E, Fin (L e)) where
  left e := G.left e.1
  right e := G.right e.1
  separated e := G.separated e.1

/-- PDF pp.20,26--28: a SINGLE concurrent packing in the physical multigraph.
The disjointness condition ranges across commodities as well as within them.
Each path carries actual copy labels, not just an aggregate edge-load bound. -/
structure Packing {n r : ℕ} {E : Type} (G : EdgeGraph n E) (L : E → ℕ)
    (s t : Fin r → Fin n) where
  count : Fin r → ℕ
  path : (i : Σ j : Fin r, Fin (count j)) → SimpleEdgePath (copyGraph G L) (s i.1) (t i.1)
  disjoint : ∀ i j, i ≠ j → ∀ a : Fin (path i).1.val, ∀ b : Fin (path j).1.val,
    (path i).2.val.2 a ≠ (path j).2.val.2 b

/-- PDF pp.20,26--27: nonnegative real capacities are floored AFTER scaling. -/
def roundedCopies {E : Type} (c : E → ℝ) (m k N : ℕ) (e : E) : ℕ :=
  ⌊((m * k * N : ℕ) : ℝ) * c e⌋₊

/-- PDF p.26: Lemma 2 uses the maximum, allowing every path count to be zero. -/
def maxPathCount {n r : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (s t : Fin r → Fin n) : ℕ :=
  Finset.univ.sup (fun i => pathCount G (s i) (t i))

/-- PDF p.27: Lemma 3 uses the SUM, in contrast to Lemma 2. -/
def sumPathCount {n r : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (s t : Fin r → Fin n) : ℕ :=
  ∑ i, pathCount G (s i) (t i)

/-- PDF p.15: one representative per UNORDERED pair of distinct terminals. -/
abbrev TerminalPair {n : ℕ} (S : Finset (Fin n)) :=
  {p : Fin n × Fin n // p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2}

/-- PDF pp.15,30, (32)--(36),(146)--(150): independent full edge budgets
for each connectivity test, with a common lower slack. These tests are not
concurrent commodities and their loads are NOT summed over terminal pairs. -/
def ConnectivityFeasible {n : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (c : E → ℝ) (S : Finset (Fin n))
    (z : ℝ) (f : TerminalPair S → Flow E) : Prop :=
  ∀ p, SingleFeasible G c p.val.1 p.val.2 (f p) ∧
    z ≤ netSourceOutflow G (f p) p.val.1

/-- PDF pp.15,30, (32),(146): the connectivity LP's actual optimized slack. -/
def connectivityValue {n : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (c : E → ℝ) (S : Finset (Fin n)) : ℝ :=
  sSup {z | ∃ f, ConnectivityFeasible G c S z f}

/-- PDF p.12, (13): cut sum, each undirected edge counted once. -/
def cutCapacity {n : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (c : E → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∑ e, if (G.left e ∈ A ∧ G.right e ∉ A) ∨
    (G.right e ∈ A ∧ G.left e ∉ A) then c e else 0

/-- PDF p.15, (29): the finite nonempty collection of cuts separating S. -/
def SteinerCut {n : ℕ} (S A : Finset (Fin n)) : Prop :=
  ∃ s ∈ S, ∃ t ∈ S, s ∈ A ∧ t ∉ A

/-- PDF pp.15,30, (29),(145): minimum of computed Steiner cut sums.
For |S|>=2 the domain is finite nonempty, so no totalized empty infimum is used. -/
def steinerValue {n : ℕ} {E : Type} [Fintype E]
    (G : EdgeGraph n E) (c : E → ℝ) (S : Finset (Fin n)) : ℝ :=
  sInf {z | ∃ A, SteinerCut S A ∧ z = cutCapacity G c A}

/-- Zero oriented flow has zero net netSourceOutflow, including an empty edge type. -/
example {n : ℕ} {E : Type} [Fintype E] (G : EdgeGraph n E) (v : Fin n) :
    netSourceOutflow G (fun _ _ => 0) v = 0 := by
  simp [netSourceOutflow]

/-- Zero capacities give zero rounded copies, including the N=0 boundary. -/
example {E : Type} (m k N : ℕ) (e : E) :
    roundedCopies (fun _ => 0) m k N e = 0 := by
  simp [roundedCopies]

/-- A cut containing every vertex has capacity zero. -/
example {n : ℕ} {E : Type} [Fintype E] (G : EdgeGraph n E) (c : E → ℝ) :
    cutCapacity G c Finset.univ = 0 := by
  simp [cutCapacity]

/-- PDF p.16: a stored linear constraint, in equality or <= form. -/
structure LPRow (X : Type) where
  coefficient : X → ℝ
  rhs : ℝ
  equality : Bool

/-- PDF p.16: an LP stores its actual coefficient rows and linear objective. -/
structure FiniteLP (X : Type) where
  rows : List (LPRow X)
  objective : X → ℝ

/-- Store a linear expression by evaluating it on coordinate unit vectors.
All callers below are explicitly homogeneous linear combinations. -/
def coefficientRow {X : Type} (l : (X → ℝ) → ℝ) (rhs : ℝ)
    (equality : Bool) : LPRow X :=
  ⟨fun j => l (Pi.single j 1), rhs, equality⟩

/-- Enumerate one row for each element of a computed finite index type. -/
def indexedRows {I X : Type} [Fintype I] (f : I → LPRow X) : List (LPRow X) :=
  Finset.univ.toList.map f

/-- Common coordinates: oriented commodity flows, directed usage frequencies,
and one slack. For the single and total programs the slack is fixed at zero. -/
abbrev LPVariable (I E D : Type) := ((I × E × Bool) ⊕ D) ⊕ Unit

/-- Read an oriented flow coordinate from the common LP vector. -/
def lpFlow {I E D : Type} (x : LPVariable I E D → ℝ) (i : I) : Flow E :=
  fun e b => x (Sum.inl (Sum.inl (i, e, b)))

/-- Read a directed-channel usage frequency. -/
def lpFrequency {I E D : Type} (x : LPVariable I E D → ℝ) (d : D) : ℝ :=
  x (Sum.inl (Sum.inr d))

/-- Read the common slack coordinate. -/
def lpSlack {I E D : Type} (x : LPVariable I E D → ℝ) : ℝ :=
  x (Sum.inr ())

/-- PDF p.12, (11): sum directed weighted frequencies with the same undirected
edge. D labels actual orientations; missing orientations contribute no summand. -/
def lpCapacity {I E D : Type} [Fintype D]
    (edgeOf : D → E) (C : D → ℝ) (x : LPVariable I E D → ℝ) (e : E) : ℝ :=
  ∑ d, if edgeOf d = e then C d * lpFrequency x d else 0

/-- PDF pp.12--16, (12),(19),(21),(37): complete explicit constraint arrays.
independent=true uses a full capacity copy for every pair, as (34) requires.
Otherwise all commodities share the same physical edge budget.
Endpoint conservation rows are 0=0; fixing the unused slack to zero in the
single/total programs adds only a redundant coordinate. Both choices preserve
exactly the source's feasible flows and objective values. -/
def optimizedLP {n : ℕ} {I E D : Type} [Fintype I] [Fintype E] [Fintype D]
    (G : EdgeGraph n E) (s t : I → Fin n) (edgeOf : D → E) (C : D → ℝ)
    (independent hasSlack : Bool) : FiniteLP (LPVariable I E D) where
  rows :=
    indexedRows (fun j : I × E × Bool => coefficientRow
      (fun x => -lpFlow x j.1 j.2.1 j.2.2) 0 false) ++
    indexedRows (fun d : D => coefficientRow (fun x => -lpFrequency x d) 0 false) ++
    indexedRows (fun d : D => coefficientRow (fun x => lpFrequency x d) 1 false) ++
    [coefficientRow (fun x => ∑ d, lpFrequency x d) 1 true] ++
    indexedRows (fun j : I × Fin n => coefficientRow
      (fun x => if j.2 ≠ s j.1 ∧ j.2 ≠ t j.1 then
        netSourceOutflow G (lpFlow x j.1) j.2 else 0) 0 true) ++
    (if independent then
      indexedRows (fun j : I × E => coefficientRow
        (fun x => lpFlow x j.1 j.2 false + lpFlow x j.1 j.2 true -
          lpCapacity edgeOf C x j.2) 0 false)
    else
      indexedRows (fun e : E => coefficientRow
        (fun x => (∑ i, (lpFlow x i e false + lpFlow x i e true)) -
          lpCapacity edgeOf C x e) 0 false)) ++
    (if hasSlack then
      indexedRows (fun i : I => coefficientRow
        (fun x => lpSlack x - netSourceOutflow G (lpFlow x i) (s i)) 0 false)
    else [coefficientRow (fun x => lpSlack x) 0 true])
  objective := fun j =>
    let x := Pi.single j 1
    if hasSlack then lpSlack x else ∑ i, netSourceOutflow G (lpFlow x i) (s i)

/-- Dense coefficient storage: one scalar per matrix entry, right-hand-side
entry, and objective entry. No bit complexity or exact-real solver is asserted. -/
def descriptionSize {X : Type} [Fintype X] (P : FiniteLP X) : ℕ :=
  Fintype.card X * (P.rows.length + 1) + P.rows.length

/-- Extracting coefficients retains a one-coordinate homogeneous expression. -/
example (a : ℝ) (j : Fin 1) :
    (coefficientRow (fun x : Fin 1 → ℝ => a * x j) 0 false).coefficient j = a := by
  simp [coefficientRow]

end QAlgorithms.Papers.Independent.Intakethird100.P35


