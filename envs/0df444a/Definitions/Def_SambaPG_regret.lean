-- Prove2me | Definitions.Def_SambaPG_regret
-- name    : SambaPG_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:22.641366+00:00
-- url     : https://prove2.me/theorems/42b10d77-c6ed-4c3c-9622-124d096725ff
-- title:
--   The regret $\mathcal Rg(T)$ of a policy and of SAMBA, eq. (5)
-- statement:
--   For rewards $R_a(t)$ and arms $I(t)$ played by a policy, the **regret** by time $T$ is the expected difference between the reward of always playing the optimal arm and the reward collected:
--
--   $$
--   \mathcal Rg(T):=r^\star T-\mathbb E\Big[\sum_{t=0}^{T-1}\sum_{a\in\mathcal A}I_a(t)R_a(t)\Big]=r^\star T-\mathbb E\Big[\sum_{t=0}^{T-1}R_{I(t)}(t)\Big].
--   $$
--
--   The regret of SAMBA is this quantity for the arms played by the SAMBA process from a given initial vector.
--
--   **Formalization Note** This is the first expression of (5). The second expression, $\sum_{a\neq a^\star}(r^\star-r_a)\mathbb E[\sum_{t<T}p_a(t)]$, is Lemma 8 and is not used as a definition.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, §3.3, p.7, eq. (5)

import Mathlib
import Definitions.Def_SambaPG_sambaRun

open MeasureTheory

namespace SambaPG

/-- **The regret `Rg(T)` of a policy, first expression of (5).**
Denisov & Walton, arXiv:2007.10229v3, §3.3, p.7, eq. (5):
`Rg(T) := r⋆ T − E[Σ_{t=0}^{T−1} Σ_{a∈A} I_a(t) R_a(t)]`.

`R t ω a` is the reward `R_a(t)` and `I t ω` the arm played at time `t`. Since exactly one arm is
played at each time, `Σ_a I_a(t) R_a(t) = R_{I(t)}(t)`. -/
noncomputable def policyRegret {A : Type*} [Fintype A] (B : BernoulliBandit A) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (R : ℕ → Ω → A → ℝ) (I : ℕ → Ω → A) (T : ℕ) : ℝ :=
  B.rStar * T - ∫ ω, ∑ t ∈ Finset.range T, R t ω (I t ω) ∂μ

/-- **The regret `Rg(T)` of SAMBA, first expression of (5).**
Denisov & Walton, arXiv:2007.10229v3, §3.3, p.7, eq. (5), for the policy SAMBA (algorithm box,
p.4): the regret of the arms `I(t)` played by the SAMBA run from `p₀`, with the rewards `R_a(t)` of
the noise `ξ`. The rewards are `{0, 1}`-valued, so the expectation is that of a bounded variable.

**Formalization Note.** This is the defining expression of (5); the second expression of (5),
`Σ_{a ≠ a⋆} (r⋆ − r_a) E[Σ_{t<T} p_a(t)]`, is Lemma 8 (`SambaPG.lemma_8`), not a definition. -/
noncomputable def regret {A : Type*} [Fintype A] [DecidableEq A] {B : BernoulliBandit A}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (ξ : SambaNoise B μ) (α : ℝ)
    (draw lead : (A → ℝ) → ℝ → A) (p₀ : A → ℝ) (T : ℕ) : ℝ :=
  policyRegret B μ ξ.R (playedArm ξ α draw lead p₀) T

end SambaPG


