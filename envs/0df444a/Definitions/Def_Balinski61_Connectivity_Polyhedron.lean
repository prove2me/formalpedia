-- Prove2me | Definitions.Def_Balinski61_Connectivity_Polyhedron
-- name    : Balinski61_Connectivity_Polyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:27:48.917204+00:00
-- url     : https://prove2.me/theorems/b11cc63f-d5b6-46d4-85a0-a403cf559db2
-- title:
--   System (1) with Balinski's two standing assumptions, and the graph $G(S)$ of its vertices and edges
-- statement:
--   Balinski studies the polyhedral convex set in $n$-space described by a system of $m$ linear inequalities (system (1) of the paper)
--   $$S=\{X\in\mathbb R^n : AX\le b\}=\{x\in\mathbb R^n:\ \langle a_i,x\rangle\le b_i,\ i=1,\dots,m\},$$
--   where $a_1,\dots,a_m\in\mathbb R^n$ are the rows of the $m\times n$ matrix $A$ and $b\in\mathbb R^m$. Here $n$ is the dimension of the space and $m$ the number of inequalities.
--
--   1. **Standing assumptions.** The paper assumes throughout that
--      - (i) the only solution to $AX\le 0$ is $X=0$, that is, $\langle a_i,x\rangle\le 0$ for all $i$ implies $x=0$;
--      - (ii) there exists a solution $X^0$ with $AX^0<b$, that is, $\langle a_i,X^0\rangle<b_i$ for every $i$.
--   2. **The graph $G(S)$.** The vertices of $S$ are its extreme points. Two distinct vertices $u\neq v$ are joined by a line when the segment $[u,v]$ is an edge of $S$, i.e. an extreme subset of $S$ (if a point of $[u,v]$ lies in the open segment between two points of $S$, both points lie in $[u,v]$). The graph $G(S)$ has the vertices of $S$ as its points and the edges of $S$ as its lines ("the vertices, considered as points, and the edges, considered as lines", p. 432).
--
--   These are the objects of Balinski's THEOREM and of every statement of this mission: the theorems assume (i) and (ii) for the system and speak about $G(S)$.
--
--   **Formalization Note** The polyhedron is `Hirsch.Hpoly a b` and the edge relation is `Hirsch.Adj` from the published definition `Hirsch_model`, with `a : Fin m → EuclideanSpace ℝ (Fin n)`. In `Hirsch_model` the letter `d` is the dimension and `n` the number of rows; here, as on Balinski's page, `n` is the dimension and `m` the number of rows. The two assumptions are kept literally, not replaced by their consequences (bounded, full-dimensional, nonempty). `polyGraph S` is a simple graph on the subtype of extreme points of an arbitrary set `S` in a real vector space; its symmetry and irreflexivity are the only proofs in this file.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 432, system (1) and the assumptions following it; p. 432, preliminary remark and THEOREM (the graph G(S))

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

/-- The two standing assumptions Balinski places on the system (1) `AX ≤ b` (p. 432), with
the rows of `A` given as vectors `a i ∈ ℝⁿ`, `i < m`:
(i) the only solution of `AX ≤ 0` is `X = 0`;
(ii) some `X⁰` satisfies `AX⁰ < b`, i.e. every inequality strictly. -/
structure StandingAssumptions {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : Fin m → ℝ) : Prop where
  only_zero : ∀ x : EuclideanSpace ℝ (Fin n), (∀ i, ⟪a i, x⟫ ≤ 0) → x = 0
  strict_point : ∃ x₀ : EuclideanSpace ℝ (Fin n), ∀ i, ⟪a i, x₀⟫ < b i

/-- The graph `G(S)` of a set `S` (p. 432): its points are the vertices (extreme points) of `S`,
and two vertices `u ≠ v` are joined by a line when the segment `[u, v]` is an edge of `S`,
i.e. an extreme subset of `S` (`Hirsch.Adj`). -/
def polyGraph {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) :
    SimpleGraph (Set.extremePoints ℝ S) where
  Adj u v := Hirsch.Adj S u v
  symm := ⟨fun u v (h : Hirsch.Adj S u v) =>
    ⟨fun e => h.1 e.symm, by rw [segment_symm]; exact h.2⟩⟩
  loopless := ⟨fun u (h : Hirsch.Adj S u u) => h.1 rfl⟩

end Balinski61.Connectivity


