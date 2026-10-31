-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_IsAggFeasible
-- name    : KallMayerSLP_Multistage_IsAggFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:18:49.586538+00:00
-- url     : https://prove2.me/theorems/15ae8ba1-4fb3-48bf-af0a-f21623d83f1e
-- title:
--   Feasibility in the aggregated problem (3.14)
-- statement:
--   A family $(x_m)_{m\in\mathcal N}$ is feasible for the fully aggregated problem (3.14) if, for every node $n$,
--   $$
--   \sum_{m\in\mathcal H(n)}A_{t_nt_m}x_m=b_{t_n}(\widehat\zeta^n),\qquad x_n\ge0.
--   $$
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.14), p.263 (PDF 272)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_zetaHat

namespace KallMayerSLP.Multistage

open MeasureTheory
open scoped Matrix

/-- Feasibility in the fully aggregated problem (3.14) (Kall & Mayer, *Stochastic Linear
Programming* (2005), Chapter 3, (3.14), p.263, PDF 272): for every node `n`,
`Σ_{m∈ℋ(n)} A_{t_n t_m} x_m = b_{t_n}(ζ̂^n)` and `x_n ≥ 0`.

**Formalization Note.** The history `ℋ(n)` is indexed by the stages `τ = 1, …, t_n`, with
`x_m = X τ (anc n)`. -/
def IsAggFeasible {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ∀ t, Ω → Fin (D.r t) → ℝ)
    (X : ∀ t, 𝒯.Node t → Fin (D.n t) → ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ D.T → ∀ n : 𝒯.Node t,
    ∑ τ : Set.Icc 1 t, D.A t τ *ᵥ X τ (𝒯.anc τ.2.2 n) = D.b t (zetaHat 𝒯 P ξ n) ∧ 0 ≤ X t n

end KallMayerSLP.Multistage


