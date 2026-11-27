-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_IsDivergenceFn
-- name    : RockafellianRelax_Supplement_IsDivergenceFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:13:07.543877+00:00
-- url     : https://prove2.me/theorems/83566525-ffff-42d4-84a2-51ad3b5c5099
-- title:
--   Admissible function $\Phi$ of a $\Phi$-divergence
-- statement:
--   A function $\Phi : \mathbb R \to \overline{\mathbb R}$ is **admissible** for a $\Phi$-divergence when it is convex, real-valued on $[0,\infty)$, and has $1$ as its unique minimizer with minimum value $0$:
--
--   $$
--   \Phi(1) = 0, \qquad \Phi(a) > 0 \quad (a \ne 1).
--   $$
--
--   The Kullback–Leibler, $\chi^2$, variational and Hellinger functions are examples.
--
--   **Formalization Note** Convexity is convexity of the real epigraph (published `IsConvexExt`). Continuity at $0$, lower semicontinuity, strict convexity and superlinearity are not required.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §4.2, Refinement A, p.14 (conditions on Φ)

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_IsConvexExt

namespace RockafellianRelax.Supplement

/-- **Admissible function `Φ` of a Φ-divergence.** Royset, Chen & Eckstrand, arXiv:2204.04762v4, §4.2, Refinement A, p.14: "where Φ : ℝ → R̄
is a convex function, real-valued on [0, ∞), with a unique minimizer at 1 and a minimum value of 0."

**Formalization Note.** Convexity is convexity of the real epigraph (the published
`WassersteinDRO.ConvexLossP1.IsConvexExt`). "Unique minimizer at 1 with minimum value 0" is
`Φ 1 = 0 ∧ ∀ a ≠ 1, 0 < Φ a`, over all of `ℝ`. Nothing further (continuity at `0`, lower
semicontinuity, strict convexity, superlinearity) is required. -/
def IsDivergenceFn (Φ : ℝ → EReal) : Prop :=
  WassersteinDRO.ConvexLossP1.IsConvexExt Φ ∧ (∀ a : ℝ, 0 ≤ a → Φ a ≠ ⊤ ∧ Φ a ≠ ⊥) ∧
    Φ 1 = 0 ∧ ∀ a : ℝ, a ≠ 1 → 0 < Φ a

end RockafellianRelax.Supplement


