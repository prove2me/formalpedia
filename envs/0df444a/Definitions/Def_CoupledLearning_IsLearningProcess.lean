-- Prove2me | Definitions.Def_CoupledLearning_IsLearningProcess
-- name    : CoupledLearning_IsLearningProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:05.835911+00:00
-- url     : https://prove2.me/theorems/0123e7b6-160b-40fc-b89b-a9f487e7be42
-- title:
--   A realization of the learning dynamics (θ-update)–(q-update)
-- statement:
--   On a probability space $(\Omega,P)$ with filtration $(\mathcal F_k)$, processes $q^k$ (profiles), $y^k$ (payoffs) and a random set $T(\omega)$ of update stages realize the learning dynamics with true parameter $s^*$ and initial state $(\theta^1,q^1)$ if:
--
--   1. $q^1$ is the given initial profile;
--   2. $q^k$ is $\mathcal F_k$-measurable and $y^k$ is $\mathcal F_{k+1}$-measurable;
--   3. given $\mathcal F_k$, $y^k$ has density $\varphi^{s^*}(\cdot|q^k)$: for every measurable $A$, $P(y^k\in A\mid\mathcal F_k)=\int_A\varphi^{s^*}(y|q^k)\,dy$ almost surely;
--   4. the first stage is an update stage, and almost surely there are infinitely many update stages;
--   5. almost surely $q^{k+1}\in F(\theta^{k+1},q^k)$ for every $k$, where $\theta^k$ is the belief computed by (θ-update) from $\theta^1$, $(q^j)$, $(y^j)$ and $T(\omega)$.
--
--   Every theorem of the mission is about such a process.
--
--   **Formalization Note** Stages are indexed from $0$. The profiles may be any adapted selection from $F(\theta^{k+1},q^k)$, possibly randomized; a fixed selection rule is a special case. The update stages may be deterministic or random and need no measurability.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, §2, pp.7–8

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_Fprod
import Definitions.Def_CoupledLearning_payoffMeasure
import Definitions.Def_CoupledLearning_belief

open MeasureTheory

namespace CoupledLearning

/-- A realization of the learning dynamics (θ-update)–(q-update) (arXiv:2206.05637v2, §2,
pp.7–8) on a probability space `(Ω, P)` with filtration `ℱ`, true parameter `sstar = s*` and
initial state `(θ₁, q₁)`. The processes are the profiles `q k`, the payoffs `y k` and the random
set `T ω` of belief-update stages; the belief is not a free process but `belief θ₁ φ q y T`.

1. `q^1 = q₁`;
2. `q^k` is `ℱ_k`-measurable and `y^k` is `ℱ_{k+1}`-measurable;
3. given `ℱ_k`, the payoff `y^k` has density `φ^{s*}(·|q^k)`: for every measurable `A`,
   `P(y^k ∈ A | ℱ_k) = ∫_A φ^{s*}(y|q^k) dy` almost surely;
4. the first stage is an update stage, and almost surely there are infinitely many;
5. almost surely, `q^{k+1} ∈ F(θ^{k+1}, q^k)` for every `k`.

**Formalization Note.** Stages are indexed from `0`. The profiles may be any adapted selection
from `F(θ^{k+1}, q^k)`, possibly using extra randomness, as long as item 3 holds; a fixed
selection rule is a special case. The update stages need no measurability and may be deterministic
or random. -/
structure IsLearningProcess {I S : Type*} [Fintype I] [Fintype S] {d : I → ℕ}
    (φ : S → Prof d → (I → ℝ) → ℝ)
    (F : (i : I) → (S → ℝ) → Prof d → Set (EuclideanSpace ℝ (Fin (d i))))
    (sstar : S) (θ₁ : S → ℝ) (q₁ : Prof d)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (q : ℕ → Ω → Prof d) (y : ℕ → Ω → (I → ℝ)) (T : Ω → Set ℕ) : Prop where
  init : ∀ ω, q 0 ω = q₁
  strategy_adapted : ∀ k, Measurable[ℱ k] (q k)
  payoff_measurable : ∀ k, Measurable[ℱ (k + 1)] (y k)
  payoff_law : ∀ k, ∀ A : Set (I → ℝ), MeasurableSet A →
    P[(y k ⁻¹' A).indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[P]
      fun ω => (payoffMeasure φ sstar (q k ω) A).toReal
  first_update : ∀ ω, 0 ∈ T ω
  infinitely_many_updates : ∀ᵐ ω ∂P, (T ω).Infinite
  strategy_update : ∀ᵐ ω ∂P, ∀ k,
    q (k + 1) ω ∈ Fprod F (belief θ₁ φ (fun j => q j ω) (fun j => y j ω) (T ω) (k + 1)) (q k ω)

end CoupledLearning


