-- Prove2me | Definitions.Def_HeilmanMax3Cut_angProf
-- name    : HeilmanMax3Cut_angProf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:37.395696+00:00
-- url     : https://prove2.me/theorems/f9230b62-fc52-4064-8ae5-69455285fe77
-- title:
--   Normalized angular measure $p_i(r)$
-- statement:
--   For a triple $A=(A_1,A_2,A_3)$ of subsets of $\mathbb R^2$ and $r>0$, $p_i(r)$ is the normalized angular measure of $A_i$ on the circle of radius $\sqrt{2r}$:
--
--   $$p_i(r)=\int_{A_i\cap\sqrt{2r}S^1}\frac{dx}{2\pi\sqrt{2r}}=\frac1{2\pi}\Bigl|\bigl\{\theta\in(-\pi,\pi]:\ \sqrt{2r}(\cos\theta,\sin\theta)\in A_i\bigr\}\Bigr|.$$
--
--   For a partition, $p(r)\in\Delta_3$.
--
--   **Formalization Note** The arc-length integral is computed in the angle variable.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), p.21 (after (53))

import Mathlib
import Definitions.Def_GaussianPropeller
open MeasureTheory Real OAI.GaussianPropeller

namespace HeilmanMax3Cut

/-- **Normalized angular measure on a circle.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), p.21 (after (53)): "on the circle of radius
`√(2r)`, let `pᵢ(r)` … be the normalized angular measures of `Aᵢ` … That is,
`pᵢ(r) = ∫_{Aᵢ ∩ √(2r)S¹} dx/(2π√(2r))`."

`angProf A i r` is the fraction of the circle of radius `√(2r)` (in arc length) lying in `Aᵢ`:
`(2π)⁻¹ · |{θ ∈ (−π, π] : (√(2r) cos θ, √(2r) sin θ) ∈ Aᵢ}|`.

**Formalization Note.** The arc-length integral is computed in the angle variable (arc length
`√(2r) dθ`, divided by `2π√(2r)`). The set lies in an interval of length `2π`, so its Lebesgue
measure is finite and `toReal` is exact. -/
noncomputable def angProf (A : Fin 3 → Set (Space 2)) (i : Fin 3) (r : ℝ) : ℝ :=
  (2 * π)⁻¹ * (volume {θ : ℝ | θ ∈ Set.Ioc (-π) π ∧
    !₂[Real.sqrt (2 * r) * Real.cos θ, Real.sqrt (2 * r) * Real.sin θ] ∈ A i}).toReal

end HeilmanMax3Cut


