-- Prove2me | Definitions.Def_Hirsch_model
-- name    : Hirsch_model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T02:24:54.586397+00:00
-- url     : https://prove2.me/theorems/58c5800d-5f71-43e7-89ae-76454d14f110
-- title:
--   H-polytopes, edges, and combinatorial diameter
-- statement:
--   The basic model for polytope-diameter questions.
--
--   `Hpoly a b` is the **H-polytope** $\{x \in \mathbb{R}^d \mid \langle a_i, x\rangle \le b_i,\ i = 1,\dots,n\}$ cut out by $n$ linear inequalities, with normals $a_i$ and offsets $b_i$; nonemptiness and boundedness are not built in — theorems assume them explicitly.
--
--   `Adj P u v` says $u \ne v$ and the segment $[u, v]$ is an extreme subset of $P$. For a polytope, the convex extreme subsets are exactly the faces, so adjacency says precisely that $[u,v]$ is a one-dimensional face of $P$ — an **edge** — and its endpoints are then vertices (extreme points) of $P$.
--
--   `DiamLE P B` says every two vertices of $P$ (extreme points, `Set.extremePoints ℝ P`) are joined by a walk of exactly $B$ steps, each step either staying put or crossing an edge. Stationary steps make the predicate monotone in $B$, so `DiamLE P B` says exactly that the vertex-edge graph of $P$ is connected with combinatorial diameter at most $B$.
-- source:
--   Standard definitions; see Santos, Recent progress on the combinatorial diameter of polytopes and simplicial complexes, TOP 21 (2013), Section 2, https://arxiv.org/abs/1307.5900

import Mathlib

open scoped RealInnerProductSpace

namespace Hirsch

/-- The **H-polytope** cut out in $\mathbb{R}^d$ by the `n` linear inequalities
$\langle a_i, x\rangle \le b_i$: the set of points satisfying every inequality.
Boundedness and nonemptiness are not part of the definition; theorems assume
them explicitly. -/
def Hpoly {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, ⟪a i, x⟫ ≤ b i}

/-- Two points `u ≠ v` are **adjacent** on `P` when the segment `[u, v]` is an
extreme subset of `P`. For a polytope the convex extreme subsets are exactly
the faces, so this says `[u, v]` is a face of dimension one — an **edge** —
and its endpoints are then vertices (extreme points) of `P`. -/
def Adj {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (u v : E) : Prop :=
  u ≠ v ∧ IsExtreme ℝ P (segment ℝ u v)

/-- `DiamLE P B`: every two vertices (extreme points) of `P` are joined by a
walk of `B` steps in the vertex-edge graph of `P`, where each step either
stays put or crosses an edge. Stationary steps make the predicate monotone in
`B`, so this says exactly that the combinatorial diameter of the graph of `P`
is at most `B` (and in particular that the graph is connected). -/
def DiamLE {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (B : ℕ) : Prop :=
  ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P,
    ∃ w : ℕ → E, w 0 = u ∧ w B = v ∧
      ∀ i < B, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1))

end Hirsch


