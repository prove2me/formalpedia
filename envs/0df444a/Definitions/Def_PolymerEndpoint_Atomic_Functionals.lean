-- Prove2me | Definitions.Def_PolymerEndpoint_Atomic_Functionals
-- name    : PolymerEndpoint_Atomic_Functionals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:01.100401+00:00
-- url     : https://prove2.me/theorems/17da080e-5776-4a58-812d-a45fa0153d2e
-- title:
--   Atom mass and pure atomicity functionals
-- statement:
--   For a partitioned subprobability measure $f$ and threshold $\varepsilon$, the functional $\|f\|_\varepsilon$ is the sum of masses larger than $\varepsilon$. The indicator $I_\varepsilon(f)$ records whether the maximum site mass is at least $\varepsilon$. For the polymer, asymptotic pure atomicity means that for every positive threshold sequence $\varepsilon_i\to0$, the Cesàro mean of the endpoint mass on sites with $f_i(x)>\varepsilon_i$ converges almost surely to one:
--   $$
--   \frac1n\sum_{i=0}^{n-1}\rho_i(\omega_i\in\mathcal A_i^{\varepsilon_i})\longrightarrow1.
--   $$
--
--   These functionals connect the topology of partitioned measures to the observable endpoint localization.
--
--   **Formalization Note** A real supremum represents the maximum in $I_\varepsilon$; for summable nonnegative $f$ the positive maximum is attained.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 42, §6.1; p. 43, Theorem 6.3(a)

import Definitions.Def_PolymerEndpoint_Atomic_Partitioned

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

noncomputable def normEps {d : ℕ} (ε : ℝ) (f : PSM d) : ℝ :=
  ∑' u, if ε < f.toFun u then f.toFun u else 0

noncomputable def Ieps {d : ℕ} (ε : ℝ) (f : PSM d) : ℝ :=
  if ε ≤ ⨆ u, f.toFun u then 1 else 0

def AsympPurelyAtomic {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Cell d → Ω → ℝ) (β : ℝ) (P : Measure Ω) : Prop :=
  ∀ ε : ℕ → ℝ, (∀ i, 0 < ε i) → Tendsto ε atTop (𝓝 0) →
    ∀ᵐ a ∂P, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, atomMass X β i (ε i) a)
      atTop (𝓝 1)

end PolymerEndpoint.Atomic


