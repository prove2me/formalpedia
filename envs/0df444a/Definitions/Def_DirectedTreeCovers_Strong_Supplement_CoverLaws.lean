-- Prove2me | Definitions.Def_DirectedTreeCovers_Strong_Supplement_CoverLaws
-- name    : DirectedTreeCovers_Strong_Supplement_CoverLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:54:25.693926+00:00
-- url     : https://prove2.me/theorems/01590586-b8ca-493e-9fbc-cb0ccc7607b0
-- title:
--   Finite randomized covers and sourcewise/prioritized targets
-- statement:
--   A cover law is a finite set of preprocessing outcomes carrying a probability mass function of total mass one and an actual list of weighted tree-pairs for each outcome. Per-vertex overlap is the finite probability-weighted sum of the actual support counts. Neither validity nor an overlap estimate is a field of this data structure.
--
--   Sourcewise coverage requires the exact k-strong inequality for all finite-roundtrip queries in S × V, with original graph paths allowed outside S. A priority order is a bijection ranking every vertex from 1 to n. For an ordered pair, j is the smaller endpoint rank and q=max(1,ceil(k log(j)/log(n))); prioritized coverage requires additive error (q−1) times the original roundtrip. The real root n^(1/k) uses real division. These are shared targets for Theorems 1.1, 1.8 and 1.9, not assumed-correct algorithms.
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), Theorems 1.1, 1.8–1.9, printed pp.3,5 (PDF pp.4,6); §§9.1–9.2, printed pp.44,47 (PDF pp.45,48).

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Supplement_Roundtrip

noncomputable section

namespace DirectedTreeCovers.Strong.Supplement

open scoped Classical
open EulerSparsify

variable {V E : Type} [Fintype V] [Fintype E]

/-- A mass-one, finite preprocessing distribution, with actual pair collections
as its outputs. Neither coverage nor an overlap estimate is a field. Finite laws
suffice for the finite hierarchies and their finite products in §§4,9. -/
structure CoverLaw (V E : Type) where
  atoms : ℕ
  law : PMF (Fin atoms)
  output : Fin atoms → List (TreePair V E)

/-- Finite expected per-vertex overlap, counting the actual union support of each
pair, rather than membership in a numerical proxy cluster. -/
def meanOverlap (L : CoverLaw V E) (v : V) : ℝ :=
  ∑ ω : Fin L.atoms, (L.law ω).toReal * (overlap (L.output ω) v : ℝ)

/-- The real root, with real division; used only at k ≥ 1. -/
def rootScale (n k : ℕ) : ℝ := (n : ℝ) ^ (1 / (k : ℝ))

/-- Sourcewise coverage on S × V. Searches and routes remain in the entire graph,
not in the graph induced by S (§9.1, printed p.44 / PDF p.45). -/
def SourcewiseCover (G : DiGraph V E) (k : ℕ) (S : Finset V)
    (ts : List (TreePair V E)) : Prop :=
  (∀ T ∈ ts, IsTreePair G T) ∧ ∀ u ∈ S, ∀ v, roundtrip G u v ≠ ⊤ →
    ∃ T ∈ ts, pairDist G T u v ≤
      dist G u v + ((k - 1 : ℕ) : ENNReal) * roundtrip G u v

/-- A priority ordering ranks EVERY vertex, with ranks 1,...,n in formulas.
The equivalence itself is zero based. -/
abbrev Priority (V : Type) [Fintype V] := V ≃ Fin (Fintype.card V)

def endpointRank (ρ : Priority V) (u v : V) : ℕ :=
  min ((ρ u).val + 1) ((ρ v).val + 1)

/-- Exact source formula max(1,ceil(k log(j)/log(n))). Denominator is positive
in its theorem (n ≥ 2); the better endpoint may be in either position. -/
def priorityParameter (k : ℕ) (ρ : Priority V) (u v : V) : ℕ :=
  max 1 ⌈(k : ℝ) * Real.log (endpointRank ρ u v : ℝ) /
    Real.log (Fintype.card V : ℝ)⌉₊

def PrioritizedCover (G : DiGraph V E) (k : ℕ) (ρ : Priority V)
    (ts : List (TreePair V E)) : Prop :=
  (∀ T ∈ ts, IsTreePair G T) ∧ ∀ u v, roundtrip G u v ≠ ⊤ →
    ∃ T ∈ ts, pairDist G T u v ≤ dist G u v +
      ((priorityParameter k ρ u v - 1 : ℕ) : ENNReal) * roundtrip G u v

end DirectedTreeCovers.Strong.Supplement


