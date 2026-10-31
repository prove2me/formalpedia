-- Prove2me | Definitions.Def_EDPMBandit_UUCB
-- name    : EDPMBandit_UUCB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:32.28298+00:00
-- url     : https://prove2.me/theorems/939810c9-cf7d-46f0-b043-7b97f50f012e
-- title:
--   The U-UCB policy (15) with $\varphi$ and $\varphi^{-1}$
-- statement:
--   Let $\upsilon,b,q$ be the stability parameters and $\gamma>0$. Put
--
--   $$
--   \varphi(y)=\min\Big\{\upsilon\Big(\frac{y}{2b}\Big)^2,\ \upsilon\Big(\frac{y}{2b}\Big)^{2/q}\Big\},\qquad
--   \varphi^{-1}(x)=\max\Big\{2b\Big(\frac{x}{\upsilon}\Big)^{1/2},\ 2b\Big(\frac{x}{\upsilon}\Big)^{q/2}\Big\}.
--   $$
--
--   The **U-UCB** policy samples each arm once in rounds $1,\dots,K$, and in every round $t\ge K+1$ plays
--
--   $$
--   \pi^{U\text{-}UCB}_t\in\arg\max_{i}\Big[U\big(\hat F^{(i)}_{\tau_i(t-1)}\big)+\varphi^{-1}\Big(\frac{\gamma\log t}{\tau_i(t-1)}\Big)\Big]\qquad(15).
--   $$
--
--   It is the analogue of $(\alpha,\psi)$-UCB for a stable EDPM: the index is the performance of the arm's own empirical distribution plus an exploration bonus.
--
--   **Formalization Note** `IsUUCBRun` says that an admissible policy is a run of U-UCB: each arm is pulled exactly once in rounds $1,\dots,K$ ($\tau_i(K)=1$; any order) and, for every outcome and every round $t\ge K+1$, the chosen arm maximizes the index `ucbIndex`. Ties and the order of the initial pulls are resolved by the policy's own non-anticipating (possibly randomized) rule; every such rule is allowed. Powers are `Real.rpow`.
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.8, φ, φ⁻¹ and (15)

import Mathlib
import Definitions.Def_EDPMBandit_Model

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

variable {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*} [MeasurableSpace 𝒱]

/-- `φ(y) = min{υ(y/2b)², υ(y/2b)^{2/q}}`, arXiv:1806.01380v3, p.8, where `υ, b, q` are the
parameters of Definition 1. `Real.rpow` for the exponent `2/q`; the paper evaluates `φ` at
`y > 0` only. -/
noncomputable def phi (υ b q y : ℝ) : ℝ :=
  min (υ * (y / (2 * b)) ^ (2 : ℝ)) (υ * (y / (2 * b)) ^ (2 / q))

/-- `φ⁻¹(x) = max{2b(x/υ)^{1/2}, 2b(x/υ)^{q/2}}`, arXiv:1806.01380v3, p.8 (`Real.rpow`; the
paper evaluates it at `x = γ log t / τ_i(t−1) ≥ 0`). -/
noncomputable def phiInv (υ b q x : ℝ) : ℝ :=
  max (2 * b * (x / υ) ^ (1 / 2 : ℝ)) (2 * b * (x / υ) ^ (q / 2))

/-- The U-UCB index of arm `i` at round `t`, the bracket in (15), arXiv:1806.01380v3, p.8:
`U(F̂^{(i)}_{τ_i(t−1)}) + φ⁻¹(γ log t / τ_i(t−1))`. Used only at rounds `t ≥ K + 1`, where every
arm has been pulled at least once, so `τ_i(t−1) ≥ 1`. -/
noncomputable def ucbIndex (S : DistSpace) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱)
    (π : Policy K 𝒱) (υ b q γ : ℝ) (t : ℕ) (i : Fin K) (ω : Ω) : ℝ :=
  U (empArm S M i (pulls M π i (t - 1) ω) ω) +
    phiInv υ b q (γ * Real.log t / (pulls M π i (t - 1) ω : ℝ))

/-- `π` is a run of U-UCB, (15), arXiv:1806.01380v3, p.8: "π_t^{U−UCB} ∈ argmax_{i∈K}
[U(F̂^{(i)}_{τ_i(t−1)}) + φ⁻¹(γ log t/τ_i(t−1))], t ≥ K + 1, where for 1 ≤ t ≤ K, it samples each
arm once as initialization."

**Formalization Note.** `π` is an admissible policy (`Policy`), so ties in the argmax, and the
order of the initial pulls, are resolved by a non-anticipating rule, possibly randomized through
`V`; every such rule is allowed. The initialization is "each arm is pulled exactly once in
rounds `1, …, K`" (`τ_i(K) = 1` for every `i`), in any order. The argmax condition holds for
every outcome `ω`. -/
def IsUUCBRun (S : DistSpace) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱) (υ b q γ : ℝ)
    (π : Policy K 𝒱) : Prop :=
  (∀ ω (i : Fin K), pulls M π i K ω = 1) ∧
    ∀ ω (t : ℕ), K + 1 ≤ t →
      ∀ j : Fin K, ucbIndex S U M π υ b q γ t j ω ≤ ucbIndex S U M π υ b q γ t (arm M π t ω) ω

end EDPMBandit


