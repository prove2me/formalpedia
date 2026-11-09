-- Prove2me | Definitions.Def_SignFreeOracle_Separation_Graph
-- name    : SignFreeOracle_Separation_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:59.002365+00:00
-- url     : https://prove2.me/theorems/77cf1169-c8af-4b26-854e-28e2c21273d6
-- title:
--   Finite graph spectra, degeneracy, closure and labelled queries
-- statement:
--   For finite simple undirected graphs, degeneracy means that every nonempty induced vertex set has a vertex of degree at most $c$; this is equivalent to quantifying over all subgraphs. The adjacency operator norm is the Euclidean norm of the actual zero/one adjacency matrix, while the largest eigenvalue reuses the published spectral definition. Girth lower bounds quantify over all cycles and therefore allow infinite girth for forests.
--
--   For an integer $r\ge2$, a legal closure step inserts the internal vertices of a simple path of length $2,\ldots,r$ whose distinct endpoints are in the current set and whose internal vertices are outside it. The closure is the least path-closed superset:
--   $$\operatorname{clos}_{G,r}(U)=\bigcap\{S:U\subseteq S,\ S\text{ contains every short simple path between its vertices}\}.$$
--   No size or run-length estimate is assumed. Neighbours are sorted by their numerical labels; a missing zero-based position returns the query label. These definitions supply the paper's combinatorial objects and distinguish its operator norm from its Perron eigenvalue.
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Definitions 2.3, 2.5, 2.7, 3.1, pp. 7–9 (PDF pp. 7–9)

import Mathlib
import Definitions.Def_SpecExtremalConj_specRad

set_option autoImplicit false

namespace SignFreeOracle.Separation

/-- Source degeneracy, Definition 2.3: every nonempty induced vertex set has a low-degree
vertex. This is equivalent to the version over all subgraphs, since deleting edges decreases degree. -/
def Degenerate {V : Type} [Fintype V] (G : SimpleGraph V) (c : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ v ∈ S,
    Nat.card {u : V // u ∈ S ∧ G.Adj v u} ≤ c

noncomputable def maxDegree {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  ⨆ v, Nat.card {u : V // G.Adj v u}

noncomputable def avgDegree {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  (∑ v, (Nat.card {u : V // G.Adj v u} : ℝ)) / Fintype.card V

/-- The Euclidean operator norm of the actual zero/one adjacency matrix, including both
signs of the spectrum. Finite nonempty unit spheres are compact; the empty-carrier value is zero. -/
noncomputable def adjNorm {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact sSup {z : ℝ | ∃ x : EuclideanSpace ℝ V, ‖x‖ = 1 ∧
    z = ‖(WithLp.toLp 2 (fun v => ∑ u, (if G.Adj v u then (1 : ℝ) else 0) * x u) : EuclideanSpace ℝ V)‖}

/-- A legal path addition; endpoints are distinct, all vertices are distinct, and all internal
vertices are outside the current set. No quantitative bound is built into this relation. -/
def ClosureStep {V : Type} [DecidableEq V] (G : SimpleGraph V) (r : ℕ)
    (U W : Finset V) : Prop :=
  ∃ (a b : V) (inside : List V), a ∈ U ∧ b ∈ U ∧ a ≠ b ∧
    1 ≤ inside.length ∧ inside.length + 1 ≤ r ∧
    (a :: (inside ++ [b])).Nodup ∧ (a :: (inside ++ [b])).IsChain G.Adj ∧
    (∀ v ∈ inside, v ∉ U) ∧ W = U ∪ inside.toFinset

/-- Terminal sets for the source's iterative procedure. -/
def PathClosed {V : Type} (G : SimpleGraph V) (r : ℕ) (S : Set V) : Prop :=
  ∀ (a b : V) (inside : List V), a ∈ S → b ∈ S → a ≠ b →
    1 ≤ inside.length → inside.length + 1 ≤ r →
    (a :: (inside ++ [b])).Nodup → (a :: (inside ++ [b])).IsChain G.Adj →
    ∀ v ∈ inside, v ∈ S

/-- The finite least path-closed superset. Equivalently, the terminal set of Definition 2.7. -/
def closure {V : Type} (G : SimpleGraph V) (r : ℕ) (U : Set V) : Set V :=
  ⋂ S ∈ {S : Set V | U ⊆ S ∧ PathClosed G r S}, S

/-- Neighbours are sorted by their labels; zero-based index i corresponds to source index i+1.
Missing neighbours return the query label itself. -/
noncomputable def graphQuery {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (G : SimpleGraph V) (π : V ≃ Fin (2 ^ m)) (x : Fin (2 ^ m)) (i : ℕ) : Fin (2 ^ m) := by
  classical
  exact ((Finset.univ.filter fun y => G.Adj (π.symm x) (π.symm y)).sort (· ≤ ·)).getD i x

noncomputable def perron {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℝ := by
  classical
  exact SpecExtremalConj.specRad G

/-- Every cycle has length at least g; acyclic graphs have infinite girth. -/
def GirthAtLeast {V : Type} (G : SimpleGraph V) (g : ℝ) : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.IsCycle → g ≤ p.length

end SignFreeOracle.Separation


