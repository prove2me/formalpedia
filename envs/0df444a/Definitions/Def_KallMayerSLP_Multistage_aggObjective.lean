-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_aggObjective
-- name    : KallMayerSLP_Multistage_aggObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:18:11.218025+00:00
-- url     : https://prove2.me/theorems/1a6810fc-47d1-4952-b81f-46f0ea6f513f
-- title:
--   Objective of the aggregated problem (3.14)
-- statement:
--   The objective of the fully aggregated problem (3.14) is
--   $$
--   \sum_{m\in\mathcal N}p_mc_{t_m}^{\mathsf T}x_m.
--   $$
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.14), p.263 (PDF 272)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_nodeProb

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The objective `Σ_{m∈𝒩} p_m c_{t_m}ᵀ x_m` of the fully aggregated problem (3.14) (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 3, (3.14), p.263, PDF 272). -/
noncomputable def aggObjective {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)
    (X : ∀ t, 𝒯.Node t → Fin (D.n t) → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 D.T, ∑ n : 𝒯.Node t, nodeProb 𝒯 P ξ n * (D.c t ⬝ᵥ X t n)

end KallMayerSLP.Multistage


