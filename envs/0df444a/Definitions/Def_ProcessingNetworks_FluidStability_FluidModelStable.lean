-- Prove2me | Definitions.Def_ProcessingNetworks_FluidStability_FluidModelStable
-- name    : ProcessingNetworks_FluidStability_FluidModelStable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:33:04.783991+00:00
-- url     : https://prove2.me/theorems/188ce578-ead0-4b7f-84f9-078ea15bf833
-- title:
--   Definition 6.3 — fluid model stability
-- statement:
--   **Definition 6.3 (fluid model stability).** A fluid model (i.e. the model data of
--   `FluidEquationData`, together with its fluid equations `IsFluidModelSolution`) is stable if
--   there is a constant $\gamma > 0$ such that, for every fluid model solution
--   $(\hat D, \hat F, \hat T, \hat Z)$, one has $\hat Z(t) = 0$ for all $t \ge \gamma |\hat Z(0)|$,
--   where $|\hat Z(0)| := \sum_i \hat Z(0)_i$.
--
--   Unlike fluid *limit* stability (Definition 6.1), this is a property of a purely deterministic
--   system of equations — it can be checked without any reference to the underlying stochastic
--   process — and it is what every later chapter of the book actually verifies, via
--   policy-specific "ancillary" fluid equations added to (6.1)-(6.6).
--
--   **Formalization note.** This mirrors `FluidLimitStable`'s definition exactly, with
--   `FluidLimitPath` (an actual scaling limit) replaced by the purely equational
--   `IsFluidModelSolution` — the distinction the goal theorem (Theorem 6.2, via Theorem 6.5)
--   bridges.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 107, Definition 6.3

import Mathlib
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData

namespace ProcessingNetworks.FluidStability

/-- Definition 6.3 (fluid model stability), Dai & Harrison p. 107 (PDF p. 123): a fluid model
(the model data `dat`) is said to be stable if there is a constant `γ > 0` such that, for every
fluid model solution `(D̂, F̂, T̂, Ẑ)` (`IsFluidModelSolution`), one has `Ẑ(t) = 0` for all
`t ≥ γ|Ẑ(0)|`, where `|Ẑ(0)| := ∑ i, Ẑ(0) i` is Section 6.4's norm convention
`|x| := |z| := ∑ i, zᵢ` applied to the vector `Ẑ(0) ∈ ℝ^I_{≥0}`. -/
def FluidModelStable {I J K : ℕ} (dat : FluidEquationData I J K) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧
    ∀ (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ),
      IsFluidModelSolution dat Dh Fh Th Zh →
      ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = 0

end ProcessingNetworks.FluidStability


