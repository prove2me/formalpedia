-- Prove2me | Definitions.Def_BrownianEnergyRep_IsPathWienerSpace
-- name    : BrownianEnergyRep_IsPathWienerSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:46.360742+00:00
-- url     : https://prove2.me/theorems/bf410f18-3f26-43ab-aa7f-36614dc78ba7
-- title:
--   The path abstract Wiener space $(H(\mathfrak g),W(\mathfrak g),\nu)$
-- statement:
--   This predicate says that an abstract Wiener space structure on $W(\mathfrak g)$ is the path one: $\Gamma$ is $\nu$, and the Cameron-Martin space $H(\mathfrak g)$ embeds by $a\mapsto\int_0^\cdot a(s)\,ds$.
--
--   **Formalization Note** $H(\mathfrak g)$ is represented by $L^2([0,T];\mathfrak g)$ through this embedding, which is an isometry for the norm of $H(\mathfrak g)$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, proof of Theorem 5.8, p.19

import Mathlib
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_IsGaussianWienerMeasure
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `(L²([0,T]; 𝔤), W(𝔤), ν)` is the path abstract Wiener space (arXiv:1511.07378v1, proof of Theorem 5.8, p.19).

**Formalization Note** The Cameron-Martin space `H(𝔤)` is represented by `L²([0,T]; 𝔤)` through
`a ↦ ∫₀^· a`, an isometry for the norm of `H(𝔤)`. -/
def IsPathWienerSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℝ} [Fact (0 < T)]
    (A : AbstractWienerSpace (Lp E 2 (volume.restrict (Ioc (0 : ℝ) T))) ↥(WienerPath E T)) :
    Prop :=
  IsGaussianWienerMeasure E T A.Γ ∧
    ∀ a, ∀ t ∈ Icc 0 T, wAt (A.j a) t = ∫ s in (0 : ℝ)..t, (a : ℝ → E) s

end BrownianEnergyRep


