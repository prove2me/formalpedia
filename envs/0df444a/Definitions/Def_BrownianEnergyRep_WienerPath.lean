-- Prove2me | Definitions.Def_BrownianEnergyRep_WienerPath
-- name    : BrownianEnergyRep_WienerPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:00:36.953654+00:00
-- url     : https://prove2.me/theorems/c88fc15d-1462-4e3c-a293-5fb2f52c9cd5
-- title:
--   The path space $W(\mathfrak g)$
-- statement:
--   $W(\mathfrak g)$ is the space of continuous paths $w:[0,T]\to\mathfrak g$ with $w_0=0$, with the sup norm and its Borel $\sigma$-algebra. It is the representation space of the energy representation, through $L^2(W(\mathfrak g),\nu)$.
--
--   **Formalization Note** It is a closed subspace of $C([0,T],E)$. The module also defines the projection $w_s$ for real $s$, by the nearest endpoint outside $[0,T]$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Notation 2.3(4), p.3

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `W(𝔤)`: the continuous paths `[0,T] → 𝔤` starting at `0` (arXiv:1511.07378v1, Notation 2.3(4), p.3), a
closed subspace of `C([0,T], E)` with the sup norm and its Borel σ-algebra. -/
def WienerPath (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ)
    [hT : Fact (0 < T)] : Submodule ℝ C(Icc (0 : ℝ) T, E) :=
  LinearMap.ker (ContinuousMap.evalCLM ℝ (⟨0, le_rfl, hT.out.le⟩ : Icc (0 : ℝ) T)).toLinearMap

instance wienerPathMeasurableSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ)
    [Fact (0 < T)] : MeasurableSpace ↥(WienerPath E T) := borel _

instance wienerPathBorelSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ)
    [Fact (0 < T)] : BorelSpace ↥(WienerPath E T) := ⟨rfl⟩

/-- The projection `w_s` on `W(𝔤)` (arXiv:1511.07378v1, p.18). For `s` outside `[0,T]` it is the value at the
nearest endpoint. -/
noncomputable def wAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} [hT : Fact (0 < T)]
    (w : ↥(WienerPath E T)) (t : ℝ) : E :=
  w.1 (projIcc 0 T hT.out.le t)

end BrownianEnergyRep


