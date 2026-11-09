-- Prove2me | Definitions.Def_ThinningSprinkling306_ToughCycles_Paths
-- name    : ThinningSprinkling306_ToughCycles_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:23.145037+00:00
-- url     : https://prove2.me/theorems/4626efca-418a-4d7b-8eed-caae3f84c032
-- title:
--   Simple paths, terminal packings, linear forests, matchings and cycles
-- statement:
--   Let $G$ be a finite simple graph. A path is a Mathlib walk with no repeated vertices, including a singleton path. Its length counts edges. For $A\subseteq V(G)$, an $A$-path has positive length and both endpoints in $A$; internal vertices may also belong to $A$. A packing is a finite family of paths with pairwise disjoint whole vertex sets.
--
--   A spanning linear forest on $W$ is a family of disjoint simple paths whose vertex sets partition $W$. Its endpoint set includes the vertex of every singleton path. For disjoint $X,R$, a matching covering $X$ into $R$ is an injective assignment $f:X\to R$ satisfying
--   $$
--   \forall x\in X,\qquad \{x,f(x)\}\in E(G).
--   $$
--   A cycle is a Mathlib simple cycle in $G$. A cycle containing $W$ may use additional vertices. The long-cycle predicate requires its edge length, equivalently its number of distinct vertices, to be at least a real threshold.
--
--   For a collection of parts, connecting paths have endpoints in two distinct parts. Intersections are allowed only inside the union of the parts. The short-connection event additionally keeps interiors outside all selected components and requires at least $kt/4$ paths of length at most three for every collection of $k$ distinct seeded components. These are predicates defining the events, with no existence assertion built into the definition layer.
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 11, Section 5; Lemmas 4.3 and 5.3, pp. 9 and 11 (PDF pp. 11 and 13) (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Cuts

namespace ThinningSprinkling306.ToughCycles

/-- A simple path, allowing the singleton path. -/
structure Path {n : ℕ} (G : SimpleGraph (Fin n)) where
  first : Fin n
  last : Fin n
  walk : G.Walk first last
  isPath : walk.IsPath

noncomputable def Path.vertices {n : ℕ} {G : SimpleGraph (Fin n)}
    (P : Path G) : Finset (Fin n) := P.walk.support.toFinset

noncomputable def Path.interior {n : ℕ} {G : SimpleGraph (Fin n)}
    (P : Path G) : Finset (Fin n) := (P.vertices.erase P.first).erase P.last

def TerminalPath {n : ℕ} {G : SimpleGraph (Fin n)}
    (A : Finset (Fin n)) (P : Path G) : Prop :=
  1 ≤ P.walk.length ∧ P.first ∈ A ∧ P.last ∈ A

noncomputable def DisjointPaths {n r : ℕ} {G : SimpleGraph (Fin n)}
    (P : Fin r → Path G) : Prop :=
  ∀ i j, i ≠ j → Disjoint (P i).vertices (P j).vertices

noncomputable def HasTerminalPacking {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (r : ℕ) : Prop :=
  ∃ P : Fin r → Path G, (∀ i, TerminalPath A (P i)) ∧ DisjointPaths P

/-- The forest is the union of the edges of its disjoint simple paths. -/
structure LinearForest {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) where
  count : ℕ
  paths : Fin count → Path G
  disjoint : DisjointPaths paths
  spanning : Finset.univ.biUnion (fun i => (paths i).vertices) = W

noncomputable def LinearForest.endpoints {n : ℕ} {G : SimpleGraph (Fin n)}
    {W : Finset (Fin n)} (F : LinearForest G W) : Finset (Fin n) :=
  Finset.univ.biUnion fun i => {(F.paths i).first, (F.paths i).last}

/-- With disjoint X and R, precisely a graph matching from X into R covering X. -/
def MatchingInto {n : ℕ} (G : SimpleGraph (Fin n))
    (X R : Finset (Fin n)) : Prop :=
  ∃ f : X → R, Function.Injective f ∧ ∀ x, G.Adj x.val (f x).val

/-- A simple cycle in G that contains W; reservoir vertices may also occur. -/
def CycleContaining {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) : Prop :=
  ∃ v : Fin n, ∃ c : G.Walk v v,
    c.IsCycle ∧ ∀ w ∈ W, w ∈ c.support

def LongCycle {n : ℕ} (G : SimpleGraph (Fin n)) (L : ℝ) : Prop :=
  ∃ v : Fin n, ∃ c : G.Walk v v, c.IsCycle ∧ L ≤ (c.length : ℝ)

noncomputable def unionParts {n k : ℕ}
    (C : Fin k → Finset (Fin n)) : Finset (Fin n) := Finset.univ.biUnion C

def JoinsParts {n k : ℕ} {G : SimpleGraph (Fin n)}
    (C : Fin k → Finset (Fin n)) (P : Path G) : Prop :=
  ∃ i j, i ≠ j ∧ P.first ∈ C i ∧ P.last ∈ C j

/-- Intersections are permitted in the specified parts, and nowhere else. -/
noncomputable def DisjointOutside {n r : ℕ} {G : SimpleGraph (Fin n)}
    (W : Finset (Fin n)) (P : Fin r → Path G) : Prop :=
  ∀ i j, i ≠ j → Disjoint ((P i).vertices \ W) ((P j).vertices \ W)

/-- The short connecting-path event used in Claims 1 and 2 of Lemma 4.2. -/
noncomputable def WellJoined {n : ℕ} (G : SimpleGraph (Fin n))
    (W A : Finset (Fin n)) (k : ℕ) (t : ℝ) : Prop :=
  ∀ C : Fin k → Finset (Fin n), Function.Injective C →
    (∀ i, C i ∈ seededComponents G W A) →
    ∃ r : ℕ, ∃ P : Fin r → Path G,
      (k : ℝ) * t / 4 ≤ (r : ℝ) ∧
      (∀ i, (P i).walk.length ≤ 3 ∧ JoinsParts C (P i) ∧
        Disjoint (P i).interior (unionParts C)) ∧
      DisjointOutside (unionParts C) P

end ThinningSprinkling306.ToughCycles


