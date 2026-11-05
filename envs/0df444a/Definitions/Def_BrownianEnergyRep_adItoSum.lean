-- Prove2me | Definitions.Def_BrownianEnergyRep_adItoSum
-- name    : BrownianEnergyRep_adItoSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:39.576924+00:00
-- url     : https://prove2.me/theorems/27d42781-ae3c-4d53-82bf-99f4f7ccae73
-- title:
--   Itô and Stratonovich sums of $\int\mathrm{Ad}_\gamma\,dw$
-- statement:
--   For a partition $(s_i)$, a path $\gamma$ in $G$ and $w\in W(\mathfrak g)$, these are the left-point sum $\sum_i\mathrm{Ad}_{\gamma_{s_i}}(w_{s_{i+1}}-w_{s_i})$ and the trapezoidal sum $\sum_i\tfrac12(\mathrm{Ad}_{\gamma_{s_i}}+\mathrm{Ad}_{\gamma_{s_{i+1}}})(w_{s_{i+1}}-w_{s_i})$. They express the Itô integral $\int\mathrm{Ad}_\gamma\,dw$ and the Stratonovich integral $\int\mathrm{Ad}_\gamma\,\delta w$ of clauses (1) and (2) of Theorem 2.10.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Theorem 2.10, p.6

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_TimeGrid

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The left-point (Itô) sum of `∫ Ad_γ dw` along a partition (arXiv:1511.07378v1, Theorem 2.10, p.6). -/
noncomputable def adItoSum {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] {t : ℝ} (π : TimeGrid t) (γ : ↥(WienerGroup G T))
    (w : ↥(WienerPath E T)) : E :=
  ∑ i : Fin π.k, L.Ad (pathAt γ (π.s i.castSucc)) (wAt w (π.s i.succ) - wAt w (π.s i.castSucc))

/-- The trapezoidal (Stratonovich) sum of `∫ Ad_γ δw` along a partition (arXiv:1511.07378v1, Theorem 2.10, p.6). -/
noncomputable def adStratSum {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [Fact (0 < T)] {t : ℝ} (π : TimeGrid t) (γ : ↥(WienerGroup G T))
    (w : ↥(WienerPath E T)) : E :=
  ∑ i : Fin π.k, (1 / 2 : ℝ) •
    (L.Ad (pathAt γ (π.s i.castSucc)) (wAt w (π.s i.succ) - wAt w (π.s i.castSucc)) +
      L.Ad (pathAt γ (π.s i.succ)) (wAt w (π.s i.succ) - wAt w (π.s i.castSucc)))

end BrownianEnergyRep


