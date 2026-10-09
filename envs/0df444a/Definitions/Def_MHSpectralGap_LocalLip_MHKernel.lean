-- Prove2me | Definitions.Def_MHSpectralGap_LocalLip_MHKernel
-- name    : MHSpectralGap_LocalLip_MHKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:00.538722+00:00
-- url     : https://prove2.me/theorems/7373be47-453a-47bd-99b3-19c23b3c1556
-- title:
--   (1.3), p. 3 — the Metropolis–Hastings transition kernel
-- statement:
--   Let $Q(x,dy)$ be a proposal kernel on a measurable space $X$ and $\alpha(x,y)\in[0,1]$ an acceptance probability. The **Metropolis–Hastings kernel** (1.3) is
--
--   $$P(x,dz)=Q(x,dz)\,\alpha(x,z)+\delta_x(dz)\int\bigl(1-\alpha(x,u)\bigr)\,Q(x,du).$$
--
--   A step from $x$ draws a proposal $z\sim Q(x,\cdot)$, moves to $z$ with probability $\alpha(x,z)$, and stays at $x$ otherwise. Both the pCN and the random-walk Metropolis algorithms of the paper are of this form.
--
--   **Formalization Note** $\alpha$ takes values in $[0,\infty]$ with truncated subtraction $1-\alpha$; every use in this mission has $\alpha\le1$ and $\alpha$ measurable (the pCN acceptance with a continuous potential). The density construction of Mathlib returns the zero kernel for a non-measurable density, which is why measurability matters.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 3, (1.3)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.LocalLip

/-- The Metropolis–Hastings kernel (1.3) with proposal `Q` and acceptance probability `α`:
`P(x, dz) = Q(x, dz) α(x, z) + δ_x(dz) ∫ (1 − α(x, u)) Q(x, du)`. -/
noncomputable def mhKernel {X : Type} [MeasurableSpace X] (Q : Kernel X X) [IsSFiniteKernel Q]
    (α : X → X → ℝ≥0∞) : Kernel X X :=
  Q.withDensity (fun x y => α x y) +
    Kernel.withDensity Kernel.id (fun x _ => ∫⁻ u, (1 - α x u) ∂(Q x))

end MHSpectralGap.LocalLip


