-- Prove2me | Definitions.Def_PermanentStars_Counting_Graphs
-- name    : PermanentStars_Counting_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:50:29.008223+00:00
-- url     : https://prove2.me/theorems/310450d6-8d3f-4ac0-86fb-5f31110637ca
-- title:
--   Signed finite multigraph ABPs and path semantics
-- statement:
--   An **algebraic branching program** is a finite directed multigraph with a source and a sink and polynomial transition weights. Each edge occurrence is distinct, including parallel occurrences. Its value is
--   $$D_B[v]=\sum_{P:s\leadsto v}\prod_{e\in P}\lambda(e).$$
--   The empty source path contributes one. The acyclicity and source/sink conditions are explicit predicates. Total size counts vertices and transitions; effective size counts reachable vertices even when some labels are zero. A general graph accepts any label type with an interpretation; the signed alphabet used here consists of $0,1,-1,x_{ij},-x_{ij}$. Elementary labels exclude $-x_{ij}$.
--
--   This interface separates graph semantics from every correctness and resource theorem. Finite rule enumeration is a mathematical description of an ambient graph; it is not charged as a construction algorithm.
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Definition 2.2, p.6; §§3–4, pp.6–10

import Mathlib

namespace PermanentStars.Counting

/-- Definition 2.2, p.6. Edge occurrences in a list are distinct transitions. -/
structure Graph (V L : Type*) where
  source : V
  sink : V
  edges : List (V × V × L)

/-- Acyclicity, and the source/sink conditions; no correctness is built into this predicate. -/
def Graph.IsABP {V L : Type} (G : Graph V L) : Prop :=
  (∃ rank : V → ℕ, ∀ e ∈ G.edges, rank e.1 < rank e.2.1) ∧
  (∀ e ∈ G.edges, e.2.1 ≠ G.source) ∧ (∀ e ∈ G.edges, e.1 ≠ G.sink)

def Graph.size {V L : Type} [Fintype V] (G : Graph V L) : ℕ :=
  Fintype.card V + G.edges.length

/-- The truncated path sum: all paths of length at most k, including the empty source path. -/
noncomputable def Graph.paths {V L R : Type*} [CommRing R]
    (G : Graph V L) (w : L → R) : ℕ → V → R
  | 0, v => by classical exact if v = G.source then 1 else 0
  | k + 1, v => by
      classical
      exact (if v = G.source then 1 else 0) +
        (G.edges.map fun e => if e.2.1 = v then G.paths w k e.1 * w e.2.2 else 0).sum

noncomputable def Graph.output {V L R : Type*} [Fintype V] [CommRing R]
    (G : Graph V L) (w : L → R) : R := G.paths w (Fintype.card V) G.sink

def Graph.Reachable {V L : Type} (G : Graph V L) (v : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ l, (a, b, l) ∈ G.edges) G.source v

noncomputable def Graph.effectiveSize {V L : Type} [Fintype V] (G : Graph V L) : ℕ := by
  classical
  exact (Finset.univ.filter G.Reachable).card

/-- Signed variable labels are needed internally; the goal explicitly excludes negVar. -/
inductive Label (n : ℕ) where
  | zero | one | negOne
  | var (i j : Fin n)
  | negVar (i j : Fin n)
  deriving DecidableEq, Fintype

def Label.elementary {n : ℕ} : Label n → Prop
  | .negVar _ _ => False
  | _ => True

def Label.eval {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R) : Label n → R
  | .zero => 0
  | .one => 1
  | .negOne => -1
  | .var i j => A i j
  | .negVar i j => -A i j

noncomputable def Label.symbolic {n : ℕ} : Label n → MvPolynomial (Fin n × Fin n) ℤ :=
  Label.eval (fun i j => MvPolynomial.X (i, j))

/-- A finite rule relation, with a separate slot to retain parallel transitions. -/
noncomputable def ruleGraph (V L : Type) [Fintype V] [Fintype L]
    (s t : V) (slots : ℕ) (allowed : V → V → L → Fin slots → Prop) : Graph V L := by
  classical
  exact ⟨s, t, ((Finset.univ : Finset (V × V × L × Fin slots)).filter
    (fun e => allowed e.1 e.2.1 e.2.2.1 e.2.2.2)).toList.map
      (fun e => (e.1, e.2.1, e.2.2.1))⟩

end PermanentStars.Counting


