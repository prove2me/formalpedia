-- Prove2me | Definitions.Def_TierneyMH_Mixture_maxMHKernel
-- name    : TierneyMH_Mixture_maxMHKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T02:21:08.52622+00:00
-- url     : https://prove2.me/theorems/170e0b54-e7cb-4a81-ac78-ed2ba941b801
-- title:
--   The maximal Metropolis–Hastings kernel for a proposal $Q$
-- statement:
--   Let $\pi$ be the target distribution and $Q$ a proposal kernel on $E$. The **maximal Metropolis–Hastings kernel for $Q$** is the Metropolis–Hastings kernel (1) that uses the acceptance probability $\alpha_{MH}$:
--
--   $$P(x,dy) = Q(x,dy)\,\alpha_{MH}(x,y) + \delta_x(dy)\int\bigl(1-\alpha_{MH}(x,u)\bigr)\,Q(x,du).$$
--
--   It is maximal with respect to off-diagonal domination among all reversible Metropolis–Hastings kernels with the proposal $Q$. Proposition 5 compares the maximal kernel of a mixture proposal with the mixture of the maximal kernels of its components.
--
--   **Formalization Note** The file also records that the maximal kernel of a finite proposal kernel is s-finite, which is needed to form mixtures of maximal kernels in Lean.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 7, §3 (definition of the maximal Metropolis–Hastings kernel)

import Mathlib
import Definitions.Def_TierneyMH_Shared_mhKernel
import Definitions.Def_TierneyMH_Mixture_alphaMH

open TierneyMH.Shared

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Mixture

/-- The **maximal Metropolis–Hastings kernel** for the proposal `Q` (Tierney 1998, §3, p. 7):
"The Metropolis–Hastings kernel for a given `Q` that uses the acceptance probability
`α_MH(x, y)` will be called the maximal Metropolis–Hastings kernel for `Q`." It is the kernel
(1) with `α = α_MH` for the target `π`. -/
noncomputable def maxMHKernel {E : Type*} [MeasurableSpace E] (π : Measure E) (Q : Kernel E E)
    [IsSFiniteKernel Q] : Kernel E E :=
  mhKernel Q (alphaMH π Q)

/-- For a finite proposal kernel the maximal Metropolis–Hastings kernel is s-finite
(structural instance, needed to form mixtures of maximal kernels). -/
instance isSFiniteKernel_maxMHKernel {E : Type*} [MeasurableSpace E] (π : Measure E)
    (Q : Kernel E E) [IsFiniteKernel Q] : IsSFiniteKernel (maxMHKernel π Q) := by
  unfold maxMHKernel mhKernel
  have h1 : IsSFiniteKernel (Q.withDensity fun x y => alphaMH π Q (x, y)) :=
    Kernel.IsSFiniteKernel.withDensity Q fun _ _ =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (alphaMH_le_one π Q _)
  have h2 : IsSFiniteKernel (Kernel.withDensity Kernel.id
      fun x (_ : E) => ∫⁻ u, (1 - alphaMH π Q (x, u)) ∂(Q x)) := by
    refine Kernel.IsSFiniteKernel.withDensity _ fun x _ => ?_
    refine ne_top_of_le_ne_top (measure_ne_top (Q x) Set.univ) ?_
    calc ∫⁻ u, (1 - alphaMH π Q (x, u)) ∂(Q x) ≤ ∫⁻ _u, 1 ∂(Q x) :=
          lintegral_mono fun _ => tsub_le_self
      _ = Q x Set.univ := by simp
  infer_instance

end TierneyMH.Mixture


