-- Prove2me | Definitions.Def_RainsSep_Distill_AchievableSepRate
-- name    : RainsSep_Distill_AchievableSepRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:57:33.842839+00:00
-- url     : https://prove2.me/theorems/e948447c-53f0-4cfd-8bde-04cd9ef96b47
-- title:
--   Separably achievable entanglement-distillation rate
-- statement:
--   Let $\rho$ be a state on $A\otimes A$. A real number $R$ is a **separably achievable rate** for $\rho$ if there are block lengths $n_i\ge 1$, output dimensions $K_i$ and separable superoperators $\mathcal P_i$ from $n_i$ copies of $\rho$ (operators on $A^{\otimes n_i}\otimes A^{\otimes n_i}$) to operators on $\mathbb C^{K_i}\otimes\mathbb C^{K_i}$ such that
--
--   $$
--   \lim_{i\to\infty}F\big(\mathcal P_i(\rho^{\otimes n_i})\big)=1\qquad\text{and}\qquad \lim_{i\to\infty}\frac{\log_2 K_i}{n_i}=R .
--   $$
--
--   The **separably distillable entanglement** $D_*(\rho)$ is the largest such $R$: the best rate at which nearly perfect maximally entangled pairs can be extracted from copies of $\rho$ by separable operations. Since every LOCC protocol is separable, $D_*$ bounds the one-way and two-way distillable entanglements $D_1$ and $D_2$.
--
--   **Formalization Note** "$\mathcal P_i$ maps states on $V^{\otimes n_i}$ to states on $W_i$" is read as acting on the $n_i$ copies of the bipartite state and producing a $K_i\times K_i$ bipartite state, with the rate counted by the local dimension $K_i$, as in the proof of Theorem 2. The condition $n_i\ge1$ only excludes an undefined rate. Results are stated about the set of achievable rates rather than a supremum.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eqs. (3)–(4), p. 1, with S the separable superoperators (p. 1)

import Mathlib
import Definitions.Def_RainsSep_Distill_entFidelity
import Definitions.Def_RainsSep_Distill_IsSeparableSuperop
import Definitions.Def_RainsSep_Distill_pairPower

namespace RainsSep.Distill

/-- **Separably achievable distillation rate.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, p. 1, Eqs. (3)–(4): "the distillable entanglement D_S(ρ) is defined as the largest number
such that there exists a sequence of transformations P_i ∈ S, with P_i mapping states on V^{⊗n_i}
to states on W_i, such that lim_{i→∞} F(P_i(ρ)) = 1 (3) and lim_{i→∞} log2 dim W_i / n_i = D_S(ρ).
(4) … For the new measure D∗(ρ), we take the set S to be the set of separable superoperators."

`R` is achievable from the bipartite state `ρ` if there are block lengths `n_i ≥ 1`, output
dimensions `K_i` and separable superoperators `P_i` from `n_i` copies of `ρ` (Alice's
`n_i` halves ⊗ Bob's `n_i` halves) to `ℂ^{K_i} ⊗ ℂ^{K_i}` whose output entanglement fidelity
tends to `1` while `log₂ K_i / n_i → R`. The separably distillable entanglement `D∗(ρ)` is the
largest achievable `R`; statements are made about the set of achievable `R`.

**Formalization Note.** "`P_i` maps states on `V^{⊗n_i}`" is read as acting on
`pairPower ρ n_i`, the `n_i` copies of the bipartite state, and `W_i` as the bipartite output
space `ℂ^{K_i} ⊗ ℂ^{K_i}` with the rate counted by the local dimension `K_i` (as in the proof of
Theorem 2, "producing a K_i × K_i bipartite state from n_i + n_i qubits"). `0 < n_i` only
excludes the undefined rate `log₂ K_i / 0`. -/
def AchievableSepRate {α : Type*} [Fintype α] [DecidableEq α]
    (ρ : Matrix (α × α) (α × α) ℂ) (R : ℝ) : Prop :=
  ∃ (n K : ℕ → ℕ)
    (P : ∀ i, QAlgorithms.Superop ((Fin (n i) → α) × (Fin (n i) → α)) (Fin (K i) × Fin (K i))),
    (∀ i, 0 < n i) ∧ (∀ i, IsSeparableSuperop (P i)) ∧
      Filter.Tendsto (fun i => entFidelity (P i (pairPower ρ (n i)))) Filter.atTop (nhds 1) ∧
      Filter.Tendsto (fun i => Real.logb 2 (K i) / n i) Filter.atTop (nhds R)

end RainsSep.Distill


