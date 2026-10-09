-- Prove2me | Definitions.Def_MHSpectralGap_GlobalLip_MHKernel
-- name    : MHSpectralGap_GlobalLip_MHKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:01.675996+00:00
-- url     : https://prove2.me/theorems/93ada5a2-5585-494b-9268-86fd565f6c28
-- title:
--   Equation (1.3): Metropolis–Hastings transition kernel
-- statement:
--   Given a proposal kernel $Q$ and an acceptance probability $\alpha(x,y)$, the Metropolis–Hastings kernel moves according to the accepted part of $Q$ and otherwise remains at its current state:
--
--   $$P(x,dz)=Q(x,dz)\alpha(x,z)+\delta_x(dz)\int(1-\alpha(x,u))Q(x,du).$$
--
--   This definition supplies the common accept–reject mechanism for the pCN transition kernel.
--
--   **Formalization Note** The two terms use kernel densities; every theorem using this definition has a measurable pCN acceptance function. An input acceptance function that is not measurable gives Mathlib's zero kernel, so measurability is essential.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 3, (1.3)

import Mathlib

namespace MHSpectralGap.GlobalLip

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Metropolis–Hastings accept–reject kernel, (1.3). -/
noncomputable def mhKernel {X : Type} [MeasurableSpace X]
    (Q : Kernel X X) [IsMarkovKernel Q] (α : X → X → ℝ≥0∞) : Kernel X X :=
  Q.withDensity α +
    (Kernel.id : Kernel X X).withDensity
      (fun x _ => ∫⁻ u, (1 - α x u) ∂(Q x))

end MHSpectralGap.GlobalLip


