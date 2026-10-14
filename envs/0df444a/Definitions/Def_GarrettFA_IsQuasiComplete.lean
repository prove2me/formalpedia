-- Prove2me | Definitions.Def_GarrettFA_IsQuasiComplete
-- name    : GarrettFA_IsQuasiComplete
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T19:22:34.887921+00:00
-- url     : https://prove2.me/theorems/30a6fbc9-e3d0-4a6f-96f5-9981b468b57e
-- title:
--   Quasi-complete topological vector space
-- statement:
--   Let $E$ be a topological vector space over a normed field $\mathbb K$. A **net** in $E$ is a map $v : I \to E$ from a directed partially ordered set $I$. The net is **Cauchy** if for every neighbourhood $N$ of $0$ there is $i_0\in I$ with $v_i - v_j \in N$ for all $i, j \ge i_0$. It is **bounded** if its set of values $\{v_i\}$ is a bounded subset of $E$ (absorbed by every neighbourhood of $0$). It **converges** to $x$ if for every neighbourhood $N$ of $0$ there is $i_0$ with $v_i - x \in N$ for all $i\ge i_0$.
--
--   The space $E$ is **quasi-complete** if every bounded Cauchy net in $E$ converges.
--
--   This is the general completeness notion used throughout the notes. It is weaker than completeness but holds for all Fréchet spaces, LF-spaces, weak-star duals of these, and spaces of operators with the pointwise topology.
--
--   **Formalization Note** Boundedness is Mathlib's von Neumann boundedness. Index sets are taken in the same universe as $E$; this loses nothing, since every Cauchy net gives a Cauchy filter, which is again represented by a net indexed in that universe.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 6, Definition 4.0.2 (with the definitions of bounded set, directed set, net, convergent net and Cauchy net on pp. 5–6)

import Mathlib

namespace GarrettFA

open Topology

universe u

/-- Garrett, *Completeness and quasi-completeness*, Definition 4.0.2.
A topological vector space `E` over `𝕜` is quasi-complete when every bounded Cauchy net
converges. A net is a map `v : I → E` from a directed partially ordered set `I`; it is
Cauchy when for every neighbourhood `N` of `0` there is `i₀` with `v i - v j ∈ N` for all
`i, j ≥ i₀`, bounded when its set of values is von Neumann bounded, and it converges to `x`
when for every neighbourhood `N` of `0` there is `i₀` with `v i - x ∈ N` for all `i ≥ i₀`.
Index sets are taken in the same universe as `E`. -/
def IsQuasiComplete (𝕜 : Type*) (E : Type u) [SeminormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]
    [TopologicalSpace E] : Prop :=
  ∀ (I : Type u) [PartialOrder I] [IsDirected I (· ≤ ·)] (v : I → E),
    Bornology.IsVonNBounded 𝕜 (Set.range v) →
    (∀ N ∈ 𝓝 (0 : E), ∃ i₀ : I, ∀ i ≥ i₀, ∀ j ≥ i₀, v i - v j ∈ N) →
    ∃ x : E, ∀ N ∈ 𝓝 (0 : E), ∃ i₀ : I, ∀ i ≥ i₀, v i - x ∈ N

end GarrettFA


