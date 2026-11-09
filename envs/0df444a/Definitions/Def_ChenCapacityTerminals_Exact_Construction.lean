-- Prove2me | Definitions.Def_ChenCapacityTerminals_Exact_Construction
-- name    : ChenCapacityTerminals_Exact_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:52.360876+00:00
-- url     : https://prove2.me/theorems/004e0e52-28d9-409e-acd3-3d0307755310
-- title:
--   Single-tail SCC construction, greedy cover and weighted guide marks
-- statement:
--   This is the construction of Sections 2.1–2.3, recorded as finite partitions, merge guides, representatives, tail lists, greedy selections and retained masses. For $\tau=L/(4d)$, a quotient edge $A\to C$ requires one original tail $u\in A$ with $w(\{u\},C)>\tau$.
--   $$\tau=\frac{L}{4d}.$$
--   Each round merges exactly the strongly connected components. The stopping test uses the condensation formed in that round, counting newly merged sources. Representatives follow a largest child. Each unchanged final source has its distinct positive external tails sorted by their aggregate incoming capacity; all full groups of $d$ tails are covered by maximum-current-coverage greedy choices.
--
--   Witnessed child outtrees, final predecessor edges and dummy-root edges determine the guide. A vertex is marked precisely when its mass plus its children’s retained masses exceeds $t$; a mark passes zero upward. The returned terminals combine the source and greedy probes with all marks other than the original and dummy roots.
--
--   The legality predicate contains these construction rules and permits every legal tie choice. Its fields contain no terminal-count estimate, stopping-round bound, expansion certificate or runtime promise.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 3–6, PDF p. 4–7, §§2.1–2.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=4–7

import Definitions.Def_ChenCapacityTerminals_Exact_Network

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

abbrev Parts := Finset (Finset ℕ)

def Partition (V : Finset ℕ) (P : Parts) : Prop :=
  (∀ A ∈ P, A.Nonempty ∧ A ⊆ V) ∧
  P.biUnion id = V ∧ ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B

def quotientEdge (G : Network) (τ : ℝ) (A C : Finset ℕ) : Prop :=
  A ≠ C ∧ ∃ u ∈ A, τ < weight G {u} C

def quotientReach (G : Network) (τ : ℝ) (P : Parts) (A C : Finset ℕ) : Prop :=
  Relation.ReflTransGen (fun B D => B ∈ P ∧ D ∈ P ∧ quotientEdge G τ B D) A C

noncomputable def sccParts (G : Network) (τ : ℝ) (P : Parts) (A : Finset ℕ) : Parts := by
  classical
  exact P.filter fun B => quotientReach G τ P A B ∧ quotientReach G τ P B A

noncomputable def mergeRound (G : Network) (τ : ℝ) (P : Parts) : Parts :=
  P.image fun A => (sccParts G τ P A).biUnion id

/-- Sources in the condensation of the OLD quotient. This does not threshold the new parts. -/
def FinalSource (G : Network) (τ : ℝ) (old : Parts) (C : Finset ℕ) : Prop :=
  C ∈ mergeRound G τ old ∧ ∀ A ∈ old, ∀ B ∈ old,
    B ⊆ C → quotientEdge G τ A B → A ⊆ C

noncomputable def newSources (G : Network) (τ : ℝ) (old : Parts) : Parts := by
  classical
  exact (mergeRound G τ old).filter fun C => C ∉ old ∧ FinalSource G τ old C

noncomputable def unchangedSources (G : Network) (r : ℕ) (τ : ℝ) (old : Parts) : Parts := by
  classical
  exact old.filter fun C => r ∉ C ∧ FinalSource G τ old C

/-- A quotient-child guide arc is recorded by its ORIGINAL tail and its target child. -/
structure JoinGuide where
  parent : Finset ℕ
  children : Parts
  heavy : Finset ℕ
  edges : List (ℕ × Finset ℕ)
  deriving Inhabited

def childRelation (j : JoinGuide) : Finset ℕ → Finset ℕ → Prop :=
  fun A C => ∃ u, (u, C) ∈ j.edges ∧ u ∈ A

def LegalJoin (G : Network) (τ : ℝ) (rep : Finset ℕ → ℕ) (j : JoinGuide) : Prop :=
  2 ≤ j.children.card ∧ Partition j.parent j.children ∧ j.heavy ∈ j.children ∧
  (∀ C ∈ j.children, C.card ≤ j.heavy.card) ∧ rep j.parent = rep j.heavy ∧
  (j.edges.map Prod.snd).Nodup ∧
  (j.edges.map Prod.snd).toFinset = j.children \ {j.heavy} ∧
  (∀ u C, (u, C) ∈ j.edges → ∃ A ∈ j.children,
    u ∈ A ∧ A ≠ C ∧ τ < weight G {u} C) ∧
  ∀ C ∈ j.children, Relation.ReflTransGen (childRelation j) j.heavy C

noncomputable def positiveExternalTails (G : Network) (C : Finset ℕ) : Finset ℕ := by
  classical
  exact (G.vertices \ C).filter fun u => 0 < weight G {u} C

def SortedTails (G : Network) (C : Finset ℕ) (xs : List ℕ) : Prop :=
  xs.Nodup ∧ xs.toFinset = positiveExternalTails G C ∧
    xs.Pairwise (fun u v => weight G {v} C ≤ weight G {u} C)

def fullGroups (d : ℕ) (xs : List ℕ) : List (Finset ℕ) :=
  (List.range (xs.length / d)).map fun i => ((xs.drop (i * d)).take d).toFinset

def uncoveredCount (groups : List (Finset ℕ)) (v : ℕ) : ℕ :=
  (groups.filter fun g => v ∈ g).length

/-- Greedy is an operational selection relation, without a size guarantee in its hypotheses. -/
def Greedy (V : Finset ℕ) : List (Finset ℕ) → List ℕ → Prop
  | groups, [] => groups = []
  | groups, v :: rest => v ∈ V ∧ 0 < uncoveredCount groups v ∧
    (∀ u ∈ V, uncoveredCount groups u ≤ uncoveredCount groups v) ∧
    Greedy V (groups.filter fun g => v ∉ g) rest

/-- All construction choices are data. Legality below checks the recipe, never the desired bounds. -/
structure Construction where
  rounds : ℕ
  partitions : ℕ → Parts
  representative : Finset ℕ → ℕ
  joins : List JoinGuide
  tails : Finset ℕ → List ℕ
  greedy : List ℕ
  finalEdges : List (ℕ × Finset ℕ)
  retained : ℕ → ℕ

def dummy (G : Network) : ℕ := G.vertices.sup id + 1

noncomputable def Construction.finalSources (c : Construction) (G : Network) (τ : ℝ) : Parts := by
  classical
  exact (c.partitions c.rounds).filter fun C =>
    FinalSource G τ (c.partitions (c.rounds - 1)) C

noncomputable def Construction.earlyProbes (c : Construction) (G : Network) (r : ℕ) (τ : ℝ) : Finset ℕ :=
  ((newSources G τ (c.partitions (c.rounds - 1))).filter fun C => r ∉ C).image c.representative ∪
    (c.greedy.toFinset \ {r})

noncomputable def Construction.guide (c : Construction) (G : Network) (τ : ℝ) : List (ℕ × ℕ) :=
  (c.joins.flatMap fun j => j.edges.map fun e => (e.1, c.representative e.2)) ++
  (c.finalEdges.map fun e => (e.1, c.representative e.2)) ++
  ((c.finalSources G τ).toList.map fun C => (dummy G, c.representative C))

def guideChildren (edges : List (ℕ × ℕ)) (v : ℕ) : Finset ℕ :=
  ((edges.filter fun e => e.1 = v).map Prod.snd).toFinset

def subtotal (c : Construction) (edges : List (ℕ × ℕ)) (b : ℕ → ℕ) (v : ℕ) : ℕ :=
  b v + ∑ u ∈ guideChildren edges v, c.retained u

noncomputable def Construction.marks (c : Construction) (G : Network) (τ : ℝ)
    (b : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (insert (dummy G) G.vertices).filter fun v =>
    t < subtotal c (c.guide G τ) (fun u => if u = dummy G then 0 else b u) v

noncomputable def Construction.terminals (c : Construction) (G : Network) (r : ℕ) (τ : ℝ)
    (b : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  c.earlyProbes G r τ ∪ (c.marks G τ b t \ {r, dummy G})

/-- Specifies every SCC round, its first stopping test, all witness joins, the common greedy
cover, final incoming edges and the strict postorder mass rule. No expansion, termination bound,
terminal-count bound, or resource estimate is a field of this predicate. -/
def LegalConstruction (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : Construction) : Prop :=
  let τ : ℝ := (L : ℝ) / (4 * d)
  let old := c.partitions (c.rounds - 1)
  1 ≤ c.rounds ∧ c.partitions 0 = G.vertices.image (fun v => {v}) ∧
  (∀ i ≤ c.rounds, Partition G.vertices (c.partitions i)) ∧
  (∀ i < c.rounds, c.partitions (i + 1) = mergeRound G τ (c.partitions i)) ∧
  (∀ i, 1 ≤ i → i < c.rounds →
    G.vertices.card / d < (newSources G τ (c.partitions (i - 1))).card) ∧
  (newSources G τ old).card ≤ G.vertices.card / d ∧
  (∀ i ≤ c.rounds, ∀ C ∈ c.partitions i, c.representative C ∈ C) ∧
  (c.joins.map JoinGuide.parent).Nodup ∧
  (∀ j ∈ c.joins, LegalJoin G τ c.representative j ∧
    ∃ i < c.rounds, j.parent ∈ c.partitions (i + 1) ∧ j.parent ∉ c.partitions i ∧
      j.children = (c.partitions i).filter (fun C => C ⊆ j.parent)) ∧
  (∀ i < c.rounds, ∀ C ∈ c.partitions (i + 1), C ∉ c.partitions i →
    ∃ j ∈ c.joins, j.parent = C) ∧
  (∀ C ∈ unchangedSources G r τ old, SortedTails G C (c.tails C)) ∧
  Greedy G.vertices
    ((unchangedSources G r τ old).toList.flatMap fun C => fullGroups d (c.tails C)) c.greedy ∧
  (c.finalEdges.map Prod.snd).Nodup ∧
  (c.finalEdges.map Prod.snd).toFinset = c.partitions c.rounds \ c.finalSources G τ ∧
  (∀ u Q, (u, Q) ∈ c.finalEdges → ∃ A ∈ old, ∃ C ∈ old,
    u ∈ A ∧ Disjoint A Q ∧ C ⊆ Q ∧ τ < weight G {u} C) ∧
  ∀ v ∈ insert (dummy G) G.vertices,
    let s := subtotal c (c.guide G τ) (fun u => if u = dummy G then 0 else b u) v
    c.retained v = if t < s then 0 else s

def guideEntries (edges : List (ℕ × ℕ)) (X : Finset ℕ) : ℕ :=
  (edges.filter fun e => e.1 ∉ X ∧ e.2 ∈ X).length

end ChenCapacityTerminals.Exact


