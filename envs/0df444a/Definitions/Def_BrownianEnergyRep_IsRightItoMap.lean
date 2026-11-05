-- Prove2me | Definitions.Def_BrownianEnergyRep_IsRightItoMap
-- name    : BrownianEnergyRep_IsRightItoMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:37.556819+00:00
-- url     : https://prove2.me/theorems/92855b81-b6ee-47c9-bf00-27edab913c37
-- title:
--   The right Brownian motion $B^R$ (Itô map)
-- statement:
--   The right Brownian motion is
--   $$
--   B^R_t=\int_0^t\delta g_\tau\,g_\tau^{-1},
--   $$
--   a Stratonovich integral. This predicate says that $B$ is a $\mu$-a.e. defined version of $g\mapsto B^R(g)$.
--
--   **Formalization Note** The conventions are those of $B^L$, with the sums $\sum_i(g_{s_{i+1}}-g_{s_i})\tfrac12(g_{s_i}^{-1}+g_{s_{i+1}}^{-1})$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Definition 2.8, p.5

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_TimeGrid

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The trapezoidal sum of the Stratonovich integral `∫ δg g⁻¹` (arXiv:1511.07378v1, Definition 2.8, p.5). -/
noncomputable def stratRightSum {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {T : ℝ} [Fact (0 < T)]
    {t : ℝ} (π : TimeGrid t) (γ : ↥(WienerGroup G T)) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i : Fin π.k, (matAt γ (π.s i.succ) - matAt γ (π.s i.castSucc)) *
    (1 / 2 : ℝ) • (matAt γ⁻¹ (π.s i.castSucc) + matAt γ⁻¹ (π.s i.succ))

/-- `B` is the right Brownian motion `B^R_t = ∫₀ᵗ δg_τ g⁻¹_τ` (arXiv:1511.07378v1, Definition 2.8, p.5), with
the conventions of `IsLeftItoMap`. -/
def IsRightItoMap {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (μ : Measure ↥(WienerGroup G T))
    (B : ↥(WienerGroup G T) → ↥(WienerPath E T)) : Prop :=
  AEMeasurable B μ ∧ ∀ t ∈ Icc 0 T, ∀ π : ℕ → TimeGrid t,
    Tendsto (fun j => (π j).mesh) atTop (𝓝 0) → ∀ i k,
      TendstoInMeasure μ (fun j γ => stratRightSum (π j) γ i k) atTop
        (fun γ => L.incl (wAt (B γ) t) i k)

end BrownianEnergyRep


