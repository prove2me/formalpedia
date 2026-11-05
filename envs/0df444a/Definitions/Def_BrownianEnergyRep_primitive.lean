-- Prove2me | Definitions.Def_BrownianEnergyRep_primitive
-- name    : BrownianEnergyRep_primitive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:27.322197+00:00
-- url     : https://prove2.me/theorems/658392cd-7564-42e9-b9dc-d88ea869fa86
-- title:
--   The primitive $\int_0^\cdot f$ as a path in $W(\mathfrak g)$
-- statement:
--   For a $\mathfrak g$-valued function $f$ integrable on $(0,T]$, this is the path $t\mapsto\int_0^tf(s)\,ds$ in $W(\mathfrak g)$. It gives the translation $\int_0^\cdot\varphi^{-1}d\varphi$ of (5.4) and the drifts of Theorem 2.10.
--
--   **Formalization Note** On a non-integrable $f$ it is the zero path, in line with the Lean convention that such an integral is $0$. All integrands used in this mission are integrable.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, (5.4), p.18

import Mathlib
import Definitions.Def_BrownianEnergyRep_WienerPath

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

open Classical in
/-- The path `∫₀^· f` in `W(𝔤)` for an integrand `f` integrable on `(0,T]`.

**Formalization Note** The Bochner integral of a non-integrable function is `0` in Lean, and this
definition follows that convention. Every integrand in this development is integrable on the
paths where it is used (`notation_2_3`, `FiniteEnergy`). -/
noncomputable def primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ)
    [hT : Fact (0 < T)] (f : ℝ → E) : ↥(WienerPath E T) :=
  if hf : IntegrableOn f (Ioc 0 T) then
    ⟨⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), f s, by
      have h0 : IntegrableOn f (uIcc 0 T) := by
        rw [uIcc_of_le hT.out.le]
        exact (integrableOn_Icc_iff_integrableOn_Ioc (by simp)).2 hf
      have hc := intervalIntegral.continuousOn_primitive_interval h0
      rw [uIcc_of_le hT.out.le] at hc
      exact hc.domRestrict⟩, by
      change (∫ s in (0 : ℝ)..(0 : ℝ), f s) = 0
      simp⟩
  else 0

end BrownianEnergyRep


