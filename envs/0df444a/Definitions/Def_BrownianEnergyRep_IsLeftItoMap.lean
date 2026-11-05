-- Prove2me | Definitions.Def_BrownianEnergyRep_IsLeftItoMap
-- name    : BrownianEnergyRep_IsLeftItoMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:44.776205+00:00
-- url     : https://prove2.me/theorems/d0b0bca2-79a1-4703-a345-3220fe107b98
-- title:
--   The left Brownian motion $B^L$ (Itô map)
-- statement:
--   The left Brownian motion is
--   $$
--   B^L_t=\int_0^tg_\tau^{-1}\,\delta g_\tau,
--   $$
--   a Stratonovich integral. This predicate says that $B:W(G)\to W(\mathfrak g)$ is a $\mu$-a.e. defined version of the map $g\mapsto B^L(g)$.
--
--   **Formalization Note** The Stratonovich integral is the limit in $\mu$-probability, along every sequence of partitions with mesh $\to0$, of the trapezoidal sums $\sum_i\tfrac12(g_{s_i}^{-1}+g_{s_{i+1}}^{-1})(g_{s_{i+1}}-g_{s_i})$. The limit is never pathwise. Convergence is entrywise.
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

/-- The trapezoidal sum of the Stratonovich integral `∫ g⁻¹δg`: the sum over the partition of
`½(g⁻¹_{sᵢ} + g⁻¹_{sᵢ₊₁})(g_{sᵢ₊₁} − g_{sᵢ})` (arXiv:1511.07378v1, Definition 2.8, p.5). -/
noncomputable def stratLeftSum {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {T : ℝ} [Fact (0 < T)]
    {t : ℝ} (π : TimeGrid t) (γ : ↥(WienerGroup G T)) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i : Fin π.k, (1 / 2 : ℝ) • (matAt γ⁻¹ (π.s i.castSucc) + matAt γ⁻¹ (π.s i.succ)) *
    (matAt γ (π.s i.succ) - matAt γ (π.s i.castSucc))

/-- `B` is the left Brownian motion `B^L_t = ∫₀ᵗ g⁻¹_τ δg_τ` (arXiv:1511.07378v1, Definition 2.8, p.5).

**Formalization Note** `B` is a `μ`-a.e. defined map `W(G) → W(𝔤)`. The Stratonovich integral is the
limit in `μ`-probability of the trapezoidal sums along every sequence of partitions with mesh → 0;
the convergence is entrywise, as matrices carry no canonical norm here. Never pathwise. -/
def IsLeftItoMap {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (μ : Measure ↥(WienerGroup G T))
    (B : ↥(WienerGroup G T) → ↥(WienerPath E T)) : Prop :=
  AEMeasurable B μ ∧ ∀ t ∈ Icc 0 T, ∀ π : ℕ → TimeGrid t,
    Tendsto (fun j => (π j).mesh) atTop (𝓝 0) → ∀ i k,
      TendstoInMeasure μ (fun j γ => stratLeftSum (π j) γ i k) atTop
        (fun γ => L.incl (wAt (B γ) t) i k)

end BrownianEnergyRep


