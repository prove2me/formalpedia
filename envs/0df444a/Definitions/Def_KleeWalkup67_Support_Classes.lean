-- Prove2me | Definitions.Def_KleeWalkup67_Support_Classes
-- name    : KleeWalkup67_Support_Classes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T05:48:36.570451+00:00
-- url     : https://prove2.me/theorems/0b1d9042-c176-4a78-a83a-06282c04dcf4
-- title:
--   Classes, nonempty face complexes, boundedness regimes, and unbounded incident edges
-- statement:
--   For a real facet presentation $(a,b)$ in $\mathbb R^d$, class $(d,n)$ means $1\le d<n$, exactly $n$ geometric facets, and at least one vertex. The published facet-presentation predicate supplies nonempty interior and irredundancy.
--
--   The face complex is the collection of all nonempty faces, including the polyhedron itself, with equality and inclusion of their actual point sets. Different sets of tight inequalities describing the same face do not give different faces.
--
--   There are three boundedness regimes: bounded polyhedra, unbounded polyhedra, and all polyhedra. A vertex is incident to an unbounded edge when it belongs to a nonempty face of affine dimension one that is not bounded.
--
--   This interface builds on the published general polyhedron and walk objects and the published Klee–Walkup face definitions. It contains no existence, perturbation, path-transfer, or extremal-realization assertion.
-- source:
--   Klee and Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Mathematica 117 (1967), 53–78, https://doi.org/10.1007/BF02395040, §1, pp.55–57; §2, p.60.

import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

namespace KleeWalkup67.FiveStep.Support

/-- Class `(d,n)` consists of pointed, intrinsically `d`-dimensional real polyhedra
with exactly `n` geometric facets, in the range `1 ≤ d < n`. -/
def IsClass {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) : Prop :=
  1 ≤ d ∧ d < n ∧ IsFacetPresentation a b ∧
    (Set.extremePoints ℝ (Hirsch.Hpoly a b)).Nonempty

/-- All nonempty faces, including the polyhedron itself. Equality is equality of
geometric sets, even if different collections of tight rows describe the same face. -/
def FaceComplex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) :=
  {F : Set (EuclideanSpace ℝ (Fin d)) // IsFace a b F}

/-- The three regimes of Lemma 2.7: unrestricted, bounded, and unbounded. -/
def InRegime {d : ℕ} (regime : Option Bool)
    (P : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  match regime with
  | none => True
  | some true => Bornology.IsBounded P
  | some false => ¬ Bornology.IsBounded P

/-- Incidence with an unbounded edge means membership in an actual unbounded
one-dimensional nonempty face. -/
def IncidentUnboundedEdge {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ F : Set (EuclideanSpace ℝ (Fin d)),
    IsFace a b F ∧ dim F = 1 ∧ x ∈ F ∧ ¬ Bornology.IsBounded F

end KleeWalkup67.FiveStep.Support


