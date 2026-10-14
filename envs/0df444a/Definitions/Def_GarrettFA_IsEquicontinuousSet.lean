-- Prove2me | Definitions.Def_GarrettFA_IsEquicontinuousSet
-- name    : GarrettFA_IsEquicontinuousSet
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T19:23:13.986865+00:00
-- url     : https://prove2.me/theorems/d200f308-9242-4566-b472-9d2a9e2ca8e0
-- title:
--   Equicontinuous set of maps
-- statement:
--   Let $X$ and $Y$ be topological vector spaces and let $S$ be a set of maps $X\to Y$. The set $S$ is **equicontinuous** if for every neighbourhood $U$ of $0$ in $Y$ there is a neighbourhood $N$ of $0$ in $X$ such that
--
--   $$T(N)\subseteq U\qquad\text{for every } T\in S.$$
--
--   For sets of linear maps this is uniform equicontinuity. It is the conclusion of the Banach–Steinhaus theorem.
--
--   **Formalization Note** The predicate is stated for an arbitrary set of functions; linear maps enter through their coercions to functions.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 4, §2.2 (definition of equicontinuity)

import Mathlib

namespace GarrettFA

open Topology

/-- Garrett, *Completeness and quasi-completeness*, §2.2. A set `S` of maps `X → Y` between
topological vector spaces is equicontinuous when for every neighbourhood `U` of `0` in `Y`
there is a neighbourhood `N` of `0` in `X` with `T(N) ⊆ U` for every `T ∈ S`. -/
def IsEquicontinuousSet {X Y : Type*} [TopologicalSpace X] [Zero X] [TopologicalSpace Y] [Zero Y]
    (S : Set (X → Y)) : Prop :=
  ∀ U ∈ 𝓝 (0 : Y), ∃ N ∈ 𝓝 (0 : X), ∀ T ∈ S, Set.MapsTo T N U

end GarrettFA


