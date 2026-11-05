-- Prove2me | Definitions.Def_BrownianEnergyRep_AbstractWienerSpace_pairing
-- name    : BrownianEnergyRep_AbstractWienerSpace_pairing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:15.001347+00:00
-- url     : https://prove2.me/theorems/f6e18372-9ced-4073-b592-860ebe8c01db
-- title:
--   The random variable $\langle h,\cdot\rangle$ for $h\in H$
-- statement:
--   For $h\in H$, the map $\langle h,\cdot\rangle$ is the element of $L^2(\Gamma)$ obtained as the limit of $\varphi_i\in W^*$ whose representatives converge to $h$ in $H$. It appears in the Cameron-Martin density and in the Gaussian regular representation (5.1).
--
--   **Formalization Note** `IsPaleyWiener` is the limit description, and `pairing` is a representative chosen by `Classical.epsilon`. The item `pairing_isometry` says that it satisfies the description, is unique a.e., and agrees with $\varphi$ on $W^*$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, p.16; (5.1), p.17

import Mathlib
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `X` is the continuous extension of `⟨h, ·⟩` to `h ∈ H`: the `L²(Γ)` limit of `φᵢ ∈ W*` whose
representatives converge to `h` in `H` (arXiv:1511.07378v1, p.16). -/
def AbstractWienerSpace.IsPaleyWiener {H W : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] (A : AbstractWienerSpace H W) (h : H) (X : W → ℝ) : Prop :=
  MemLp X 2 A.Γ ∧ ∃ φ : ℕ → StrongDual ℝ W,
    Tendsto (fun i => A.dualRep (φ i)) atTop (𝓝 h) ∧
    Tendsto (fun i => eLpNorm (fun w => φ i w - X w) 2 A.Γ) atTop (𝓝 0)

/-- The `L²(Γ)` random variable `⟨h, ·⟩` for `h ∈ H` (arXiv:1511.07378v1, p.16 and (5.1), p.17).

**Formalization Note** A representative chosen by `Classical.epsilon`; `pairing_isometry` says it
is the extension, unique a.e. -/
noncomputable def AbstractWienerSpace.pairing {H W : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] (A : AbstractWienerSpace H W) (h : H) : W → ℝ :=
  Classical.epsilon (A.IsPaleyWiener h)

end BrownianEnergyRep


