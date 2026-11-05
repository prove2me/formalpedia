-- Prove2me | Definitions.Def_BrownianEnergyRep_IsLeftSDESolution
-- name    : BrownianEnergyRep_IsLeftSDESolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:28.640668+00:00
-- url     : https://prove2.me/theorems/a6d4b11d-a4d2-4559-b275-6aa0780f5c33
-- title:
--   Solutions of the Stratonovich equation $\delta w=w\,\delta b$
-- statement:
--   A map $\Phi:W(\mathfrak g)\to W(G)$ solves $\delta w=w\,\delta b$, $w_0=e$, if, writing $w=\Phi(b)$,
--   $$
--   w_t-e=\int_0^tw\,\delta b,
--   $$
--   where the Stratonovich integral is the limit in $\nu$-probability of the trapezoidal sums along partitions with mesh $\to0$. This is the equation that inverts $B^L$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Proposition 2.13, p.7

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_TimeGrid

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `Φ(b)` solves the Stratonovich equation `δw = w δb`, `w₀ = e` (arXiv:1511.07378v1, Proposition 2.13, p.7),
in integrated form with trapezoidal sums converging in `ν`-probability. -/
def IsLeftSDESolution {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (ν : Measure ↥(WienerPath E T))
    (Φ : ↥(WienerPath E T) → ↥(WienerGroup G T)) : Prop :=
  ∀ t ∈ Icc 0 T, ∀ π : ℕ → TimeGrid t, Tendsto (fun j => (π j).mesh) atTop (𝓝 0) → ∀ i k,
    TendstoInMeasure ν
      (fun j b => (∑ l : Fin (π j).k,
        (1 / 2 : ℝ) • (matAt (Φ b) ((π j).s l.castSucc) + matAt (Φ b) ((π j).s l.succ)) *
          L.incl (wAt b ((π j).s l.succ) - wAt b ((π j).s l.castSucc))) i k) atTop
      (fun b => (matAt (Φ b) t - 1) i k)

end BrownianEnergyRep


