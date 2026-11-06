-- Prove2me | Definitions.Def_RiskDistMDP_DPP_BorelMDP
-- name    : RiskDistMDP_DPP_BorelMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:41.107299+00:00
-- url     : https://prove2.me/theorems/4c7ab7d1-7beb-49cb-b82d-35b5999afca9
-- title:
--   Model data: initial law $\mu$, kernel $P$, admissible actions $\mathcal A_t$, costs $C_t$
-- statement:
--   The controlled Markov model consists of a state space $\mathbb X$ and an action space $\mathbb A$ together with
--
--   1. an initial law $\mu$ on $\mathbb X$ (the law of $X_1$);
--   2. a transition kernel $P(t,x,a,\cdot)$, a probability measure on $\mathbb X$ for every $(t,x,a)$;
--   3. admissible-action sets $\mathcal A_t(x)\subseteq\mathbb A$;
--   4. cost functions $C_t:\mathbb X\times\mathbb A\times\mathbb X\to\mathbb R$, with $C_0\equiv0$.
--
--   The standing conditions (`BorelMDP.Standing`) are: $(x,a)\mapsto P(t,x,a,B)$ is $\mathcal B(\mathbb X)\otimes\mathcal B(\mathbb A)$-measurable for every Borel $B$ (Assumption 2.11 (i)); $\mathcal A_t$ is nonempty closed valued and weakly measurable, i.e. $\{x:\mathcal A_t(x)\cap U\neq\emptyset\}\in\mathcal B(\mathbb X)$ for open $U$ (p.5); and $C_t$ is Borel (p.13).
--
--   **Formalization Note** All data are indexed by $t\in\mathbb N_0$; only $t\ge1$ is used and constrained. Measurability of the kernel is stated as measurability into `ProbabilityMeasure 𝕏` with the Giry σ-algebra, which is the same condition.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, §2, p. 5; (2.3), p. 6; Assumption 2.11 (i) and §2.5, p. 13

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- The data of the controlled Markov model of arXiv:2203.09612v4, §2 and §2.5, pp.5–6, 13:
the initial law `μ` of `X₁` (Assumption 2.11 (i)), the transition kernel `P(t, x, a, ·)` (2.3),
the admissible-action correspondence `𝒜_t : 𝕏 → 2^𝔸` (p.5) and the cost functions
`C_t : 𝕏 × 𝔸 × 𝕏 → ℝ` (p.13).

**Formalization Note** All four are indexed by `t : ℕ`; only `t ≥ 1` (the paper's `ℕ = {1,2,…}`)
is ever used, and `C₀ ≡ 0` is built into the cost process (`cost`). `P t x a` is a probability
measure on `𝕏` for every `(t, x, a)`, as Assumption 2.11 (i) requires. -/
structure BorelMDP (𝕏 𝔸 : Type*) [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] where
  /-- the initial law `μ`, `X₁ ∼ μ` -/
  μ : ProbabilityMeasure 𝕏
  /-- the transition kernel `P(t, x, a, ·)` -/
  P : ℕ → 𝕏 → 𝔸 → ProbabilityMeasure 𝕏
  /-- the admissible actions `𝒜_t(x)` -/
  adm : ℕ → 𝕏 → Set 𝔸
  /-- the cost functions `C_t(x, a, y)` -/
  C : ℕ → 𝕏 → 𝔸 → 𝕏 → ℝ

/-- The standing conditions on the model data (arXiv:2203.09612v4): for every `t ∈ ℕ`,
`(x, a) ↦ P(t, x, a, B)` is `ℬ(𝕏) ⊗ ℬ(𝔸)`-measurable for every `B ∈ ℬ(𝕏)` (Assumption 2.11 (i),
p.13); `𝒜_t` is nonempty closed valued and weakly measurable, i.e.
`{x : 𝒜_t(x) ∩ U ≠ ∅} ∈ ℬ(𝕏)` for every open `U ⊆ 𝔸` (§2, p.5); and `C_t` is
`ℬ(𝕏) ⊗ ℬ(𝔸) ⊗ ℬ(𝕏)`-measurable (p.13).

**Formalization Note** Measurability of `(x, a) ↦ P(t, x, a, ·)` into `ProbabilityMeasure 𝕏` with
the Giry (evaluation) σ-algebra is the same as measurability of every `(x, a) ↦ P(t, x, a, B)`. -/
structure BorelMDP.Standing {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸]
    [TopologicalSpace 𝕏] [TopologicalSpace 𝔸] (M : BorelMDP 𝕏 𝔸) : Prop where
  P_meas : ∀ t, 1 ≤ t → Measurable fun p : 𝕏 × 𝔸 => M.P t p.1 p.2
  adm_nonempty : ∀ t, 1 ≤ t → ∀ x, (M.adm t x).Nonempty
  adm_closed : ∀ t, 1 ≤ t → ∀ x, IsClosed (M.adm t x)
  adm_weaklyMeasurable : ∀ t, 1 ≤ t → ∀ U : Set 𝔸, IsOpen U →
    MeasurableSet {x : 𝕏 | (M.adm t x ∩ U).Nonempty}
  C_meas : ∀ t, 1 ≤ t → Measurable fun p : 𝕏 × 𝔸 × 𝕏 => M.C t p.1 p.2.1 p.2.2

end RiskDistMDP.DPP


