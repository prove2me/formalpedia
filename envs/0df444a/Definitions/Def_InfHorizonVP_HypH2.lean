-- Prove2me | Definitions.Def_InfHorizonVP_HypH2
-- name    : InfHorizonVP_HypH2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:22.16454+00:00
-- url     : https://prove2.me/theorems/037880dd-7b4d-4135-a7ef-69e30c34f5ee
-- title:
--   Hypothesis (H2): measurability of $L(\cdot,x,y)$
-- statement:
--   **(H2)** For every $(x,y)\in E\times E$ the function $t\mapsto L(t,x,y)$ is Lebesgue measurable on $\mathbb R_+$.
--
--   **Formalization Note** Lebesgue measurability is `NullMeasurable` for Lebesgue measure restricted to $[0,\infty)$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.1, p.8, (H2)

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Hypothesis (H2).**
Frankowska, Sagara, arXiv:1801.00400v3, §3.1, p.8: "(H2) L(·, x, y) is measurable for every
(x, y) ∈ E × E." Here ℝ₊ carries "the Lebesgue measure and the Lebesgue σ-algebra 𝓛" (p.7).

**Formalization Note.** Lebesgue measurability on `ℝ₊` is `NullMeasurable` with respect to
Lebesgue measure restricted to `[0, ∞)` (the completion of the Borel σ-algebra is the Lebesgue
σ-algebra). -/
def HypH2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ → E → E → ℝ) : Prop :=
  ∀ x y : E, NullMeasurable (fun t => L t x y) (volume.restrict (Ici 0))

end InfHorizonVP


