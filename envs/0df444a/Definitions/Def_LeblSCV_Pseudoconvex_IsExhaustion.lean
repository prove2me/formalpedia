-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_IsExhaustion
-- name    : LeblSCV_Pseudoconvex_IsExhaustion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:13:27.797632+00:00
-- url     : https://prove2.me/theorems/5d3e5522-8256-4aef-9ba0-674b55666833
-- title:
--   Definition 2.5.3 — exhaustion function
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open. A function $f : U \to \mathbb{R}$ is an **exhaustion function** for $U$ if every sublevel set is relatively compact in $U$:
--   $$\{ z \in U : f(z) < r \} \subset\subset U \quad \text{for every } r \in \mathbb{R}.$$
--
--   **Formalization Note.** The definition is stated for an arbitrary topological space in place of $\mathbb{C}^n$. It uses the relative compactness `IsRelCompactIn` of this mission.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 92, Definition 2.5.3

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsRelCompactIn

namespace LeblSCV.Pseudoconvex

/-- Definition 2.5.3, first part (Lebl, p. 92): `f : U → ℝ` is an *exhaustion function* for the
open set `U` if every sublevel set `{z ∈ U : f(z) < r}`, `r ∈ ℝ`, is relatively compact in `U`. -/
def IsExhaustion {X : Type*} [TopologicalSpace X] (f : X → ℝ) (U : Set X) : Prop :=
  ∀ r : ℝ, IsRelCompactIn {z | z ∈ U ∧ f z < r} U

end LeblSCV.Pseudoconvex


