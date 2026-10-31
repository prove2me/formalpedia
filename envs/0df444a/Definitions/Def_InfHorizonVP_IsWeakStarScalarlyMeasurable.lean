-- Prove2me | Definitions.Def_InfHorizonVP_IsWeakStarScalarlyMeasurable
-- name    : InfHorizonVP_IsWeakStarScalarlyMeasurable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:55.083154+00:00
-- url     : https://prove2.me/theorems/30865f17-9bdb-49af-ab2d-827831770b9e
-- title:
--   Weak$^*$ scalar measurability
-- statement:
--   A function $f:A\to E^*$, $A\subseteq\mathbb R$, is **weakly$^*$ scalarly measurable** if for every $x\in E$ the scalar function $t\mapsto\langle f(t),x\rangle$ is Lebesgue measurable on $A$.
--
--   **Formalization Note** Strong (Bochner) measurability is not assumed.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §A.2, p.21

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Weak\* scalar measurability.**
Frankowska, Sagara, arXiv:1801.00400v3, §A.2, p.21: "Let I be a nonempty closed subset of the
real line R with the Lebesgue measure and the Lebesgue σ-algebra 𝓛. … A function f : I → E* is
said to be weakly* scalarly measurable if the scalar function ⟨f(·), x⟩ is measurable for every
x ∈ E."

**Formalization Note.** `E* = E →L[ℝ] ℝ`; a function on `A` is a function on `ℝ` whose values off
`A` are ignored; measurability is Lebesgue measurability on `A` (`NullMeasurable` for Lebesgue
measure restricted to `A`). Strong (Bochner) measurability is not assumed. -/
def IsWeakStarScalarlyMeasurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E →L[ℝ] ℝ) (A : Set ℝ) : Prop :=
  ∀ x : E, NullMeasurable (fun t => f t x) (volume.restrict A)

end InfHorizonVP


