-- Prove2me | Definitions.Def_GarrettFA_IsNetComplete
-- name    : GarrettFA_IsNetComplete
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T19:22:49.793982+00:00
-- url     : https://prove2.me/theorems/4ef40310-dbd4-4ce1-93d7-4415a8e4bd96
-- title:
--   Complete topological vector space (Cauchy nets converge)
-- statement:
--   Let $E$ be a topological vector space. With nets, Cauchy nets and convergence as in the definition of quasi-completeness, $E$ is **complete** if every Cauchy net in $E$ converges. No boundedness condition is imposed.
--
--   This is the "stronger general notion of completeness" of the notes. It fails, for example, for weak-star duals of infinite-dimensional Fréchet spaces (Theorem 5.0.1 and Corollary 5.0.2).
--
--   **Formalization Note** Index sets are taken in the same universe as $E$.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 6, definition of completeness preceding Proposition 4.0.1

import Mathlib

namespace GarrettFA

open Topology

universe u

/-- Garrett, *Completeness and quasi-completeness*, §4. A topological vector space `E` is
complete when every Cauchy net converges. A net is a map `v : I → E` from a directed partially
ordered set `I`; it is Cauchy when for every neighbourhood `N` of `0` there is `i₀` with
`v i - v j ∈ N` for all `i, j ≥ i₀`, and it converges to `x` when for every neighbourhood `N`
of `0` there is `i₀` with `v i - x ∈ N` for all `i ≥ i₀`. Index sets are taken in the same
universe as `E`. -/
def IsNetComplete (E : Type u) [AddCommGroup E] [TopologicalSpace E] : Prop :=
  ∀ (I : Type u) [PartialOrder I] [IsDirected I (· ≤ ·)] (v : I → E),
    (∀ N ∈ 𝓝 (0 : E), ∃ i₀ : I, ∀ i ≥ i₀, ∀ j ≥ i₀, v i - v j ∈ N) →
    ∃ x : E, ∀ N ∈ 𝓝 (0 : E), ∃ i₀ : I, ∀ i ≥ i₀, v i - x ∈ N

end GarrettFA


