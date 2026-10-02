-- Prove2me | Definitions.Def_ProcessingNetworks_FluidStability_FluidLimitStable
-- name    : ProcessingNetworks_FluidStability_FluidLimitStable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:35:00.531858+00:00
-- url     : https://prove2.me/theorems/0279eb66-1e2f-4cc5-843b-33bacf23e0ff
-- title:
--   Definition 6.1 — fluid limit stability
-- statement:
--   **Definition 6.1 (fluid limit stability).** The fluid limit of the SPN is said to be stable
--   if there is a constant $\gamma > 0$ such that, for every fluid limit path
--   $(\hat D, \hat F, \hat T, \hat Z)$ (Definition 6.6), one has $\hat Z(t) = 0$ for all
--   $t \ge \gamma |\hat Z(0)|$ — informally, fluid limit paths are uniformly attracted to the
--   origin.
--
--   This is the hypothesis of the goal theorem (Theorem 6.2): fluid limit stability, a property
--   of the actual stochastic scaling limits of the SPN, implies stability of the original
--   stochastic model (positive recurrence of the ambient Markov chain).
--
--   **Formalization note.** Distinct from `FluidModelStable` (Definition 6.3), which is the same
--   "$\gamma|\hat Z(0)|$-attraction" property applied instead to *fluid model solutions*
--   (`IsFluidModelSolution`) — any four-tuple satisfying the fluid equations, not necessarily an
--   actual limit. The two are kept as separate definitions throughout this mission, since
--   conflating them would make Theorem 6.2 (which needs `FluidLimitStable`) a different,
--   strictly easier statement if `FluidModelStable` were substituted instead.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 106, Definition 6.1

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily
import Definitions.Def_ProcessingNetworks_FluidStability_FluidLimitPath

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

/-- Definition 6.1 (fluid limit stability), Dai & Harrison p. 106 (PDF p. 122): the fluid limit
of the SPN is said to be stable if there is a constant `γ > 0` such that every fluid limit path
`(D̂, F̂, T̂, Ẑ)` (Definition 6.6, `FluidLimitPath`) satisfies `Ẑ(t) = 0` for all
`t ≥ γ|Ẑ(0)|`. -/
def FluidLimitStable {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧
    ∀ (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ),
      FluidLimitPath fam Dh Fh Th Zh →
      ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = 0

end ProcessingNetworks.FluidStability


