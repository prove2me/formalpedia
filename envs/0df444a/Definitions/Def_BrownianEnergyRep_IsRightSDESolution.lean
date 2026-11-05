-- Prove2me | Definitions.Def_BrownianEnergyRep_IsRightSDESolution
-- name    : BrownianEnergyRep_IsRightSDESolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:37.797021+00:00
-- url     : https://prove2.me/theorems/d0953946-2a27-4c18-9e47-3456afe3a73d
-- title:
--   Solutions of the Stratonovich equation $\delta w=\delta b\,w$
-- statement:
--   A map $\Phi:W(\mathfrak g)\to W(G)$ solves $\delta w=\delta b\,w$, $w_0=e$, in the same sense as for the left equation. This is the equation that inverts $B^R$.
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

/-- `Φ(b)` solves the Stratonovich equation `δw = δb w`, `w₀ = e` (arXiv:1511.07378v1, Proposition 2.13, p.7). -/
def IsRightSDESolution {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] (ν : Measure ↥(WienerPath E T))
    (Φ : ↥(WienerPath E T) → ↥(WienerGroup G T)) : Prop :=
  ∀ t ∈ Icc 0 T, ∀ π : ℕ → TimeGrid t, Tendsto (fun j => (π j).mesh) atTop (𝓝 0) → ∀ i k,
    TendstoInMeasure ν
      (fun j b => (∑ l : Fin (π j).k,
        L.incl (wAt b ((π j).s l.succ) - wAt b ((π j).s l.castSucc)) *
          (1 / 2 : ℝ) • (matAt (Φ b) ((π j).s l.castSucc) + matAt (Φ b) ((π j).s l.succ))) i k)
      atTop (fun b => (matAt (Φ b) t - 1) i k)

end BrownianEnergyRep


