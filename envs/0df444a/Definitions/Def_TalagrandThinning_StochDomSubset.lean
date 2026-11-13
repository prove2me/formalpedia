-- Prove2me | Definitions.Def_TalagrandThinning_StochDomSubset
-- name    : TalagrandThinning_StochDomSubset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:07.462194+00:00
-- url     : https://prove2.me/theorems/99e823de-74da-46cc-8e93-b6b8d13b63e8
-- title:
--   Stochastic domination $\rho\le_d\sigma$ by a containing coupling
-- statement:
--   For laws $\rho,\sigma$ on the Hamming cube, $\rho\le_d\sigma$ means that there is a **coupling** $(A,B)$ with $A\sim\rho$, $B\sim\sigma$ and
--
--   $$A\subseteq B\quad\text{almost surely}.$$
--
--   This is the paper's definition of domination. Its equivalence with $\rho(\mathcal U)\le\sigma(\mathcal U)$ for every increasing family $\mathcal U$ (eq. (1.2)) is Strassen's theorem.
--
--   **Formalization Note** The coupling is a probability measure $\pi$ on pairs of cube points with first marginal $\rho$, second marginal $\sigma$, and $\pi(\{(A,B): A\not\subseteq B\})=0$. This is literally clause (ii) of the platform theorem `StochIneqPO.Comparison.theorem1_tfae`, instantiated at the cube.
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), §1.1, p.2 (definition of ≤_d before eq. (1.2))

import Mathlib
import Definitions.Def_TalagrandThinning_Cube

set_option autoImplicit false

open MeasureTheory

namespace TalagrandThinning

/-- Stochastic domination `ρ ≤_d σ` of laws on the Hamming cube: there is a coupling `(A, B)` with
marginals `ρ` and `σ` such that `A ⊆ B` almost surely
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §1.1, p.2, the sentence before eq. (1.2)).

**Formalization Note** The coupling is a probability measure `π` on pairs whose first and second
marginals are `ρ` and `σ` and which gives zero mass to `{(A,B) | ¬ A ⊆ B}`. This is literally
clause (ii) of the platform's Strassen theorem `StochIneqPO.Comparison.theorem1_tfae` on
`E = Fin N → Bool`. -/
def StochDomSubset {N : ℕ} (ρ σ : Measure (Cube N)) : Prop :=
  ∃ π : Measure (Cube N × Cube N), IsProbabilityMeasure π ∧
    π {z : Cube N × Cube N | z.1 ≤ z.2}ᶜ = 0 ∧ π.map Prod.fst = ρ ∧ π.map Prod.snd = σ

end TalagrandThinning


