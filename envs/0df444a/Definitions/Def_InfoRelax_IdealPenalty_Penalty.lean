-- Prove2me | Definitions.Def_InfoRelax_IdealPenalty_Penalty
-- name    : InfoRelax_IdealPenalty_Penalty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:17.032689+00:00
-- url     : https://prove2.me/theorems/f7b12b66-40fe-46a4-bdc6-9ab94606144d
-- title:
--   Penalties from generating functions (Prop. 2.2), dual value functions (10) and the ideal penalty $z^\star$
-- statement:
--   This file defines the penalties of §2.3 of Brown, Smith and Sun.
--
--   Let $\mathbb G$ be a relaxation of the natural filtration $\mathbb F$ and let $(w_0,\dots,w_T)$ be **generating functions** $w_t(a,\omega)$.
--   1. The **penalty of Proposition 2.2** has period components and total
--   $$z_t(a)=\mathbb E[w_t(a)\mid\mathcal G_t]-\mathbb E[w_t(a)\mid\mathcal F_t],\qquad z(a)=\sum_{t=0}^T z_t(a).$$
--   2. **Regular generating functions:** each $w_t$ depends only on $a_0,\dots,a_t$, each $w_t(a)$ is almost everywhere strongly measurable, and all of them are bounded almost everywhere by one constant.
--   3. For a recursive DP, the **dual value functions** $V^{\mathbb G}_t$ of eq. (10) are the backward recursion of eq. (2) with the penalized rewards $r_t-z_t$ and conditional expectations given $\mathcal G_t$:
--   $$V^{\mathbb G}_t(a_0,\dots,a_{t-1})=\sup_{a_t\in A_t(a_0,\dots,a_{t-1})}\big\{r_t(a_0,\dots,a_t)-z_t(a_0,\dots,a_t)+\mathbb E[V^{\mathbb G}_{t+1}(a_0,\dots,a_t)\mid\mathcal G_t]\big\},\qquad V^{\mathbb G}_{T+1}=0.$$
--   4. The **ideal penalty** $z^\star$ is the penalty of item 1 for the generating functions $w_t(a)=V_{t+1}(a_0,\dots,a_t)$, where $V$ are the primal value functions of eq. (2).
--
--   The ideal penalty is the subject of Theorem 2.3: it closes the duality gap for every information relaxation.
--
--   **Formalization Note** Generating functions are defined on all action sequences (the page: on $A\times\Omega$). Their almost-everywhere measurability and uniform almost-everywhere bound are pinned regularity conditions that make every conditional expectation exist and the penalty integrable along every policy; the primal value functions satisfy them. $V_{t+1}$ is the natural-number-indexed value function at $t+1$, which is $0$ at $t=T$.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, §2.3: Proposition 2.2, eq. (10), and the definition of the ideal penalty before Theorem 2.3

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework
import Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-!
# Good penalties: Proposition 2.2, the dual recursion (10) and the ideal penalty `z⋆`

Brown, Smith & Sun, *Information Relaxations and Duality in Stochastic Dynamic Programs*,
Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, §2.3: Proposition 2.2,
eq. (10), and the paragraph defining the "ideal" penalty `z⋆` before Theorem 2.3.

For a relaxation `𝔾` of `𝔽` and generating functions `w_t(a, ω)`:
* `penaltyComp μ 𝔽 𝔾 w t a = 𝔼[w_t(a) | 𝒢_t] − 𝔼[w_t(a) | 𝓕_t]` is `z_t(a)`;
* `penalty μ 𝔽 𝔾 w a = ∑_{t=0}^T z_t(a)` is `z(a)`;
* `dualValueFn M μ 𝔾 w` is the dual value function `V^𝔾_t` of (10): the recursion (2) with the
  penalized rewards `r_t − z_t` and the filtration `𝔾` in place of `𝔽`, `V^𝔾_{T+1} = 0`;
* `idealPenalty M μ 𝔾` is `z⋆`, the penalty of Proposition 2.2 for `w_t(a) = V_{t+1}(a_0, …, a_t)`,
  with `V` the primal value functions of (2).

`GeneratingFns` collects the regularity of generating functions used with Proposition 2.2.

**Formalization Note.**
* `w_t(a)` is defined for every action sequence (the page: on `A × Ω`); its regularity is
  required for every sequence.
* Pinned regularity: each `w_t(a)` is almost everywhere strongly measurable and the family is
  bounded almost everywhere by one constant, so that every conditional expectation exists and the
  penalty is integrable along every policy. The primal value functions `V_{t+1}` satisfy this.
* Conditional expectations are Mathlib's `μ[· | m]` (fixed versions, determined a.e.).
-/

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] {T : ℕ}

/-- The period-`t` penalty of Proposition 2.2, p. 5:
`z_t(a) = 𝔼[w_t(a) | 𝒢_t] − 𝔼[w_t(a) | 𝓕_t]`. -/
noncomputable def penaltyComp (μ : Measure Ω) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (t : Fin (T + 1))
    (a : Fin (T + 1) → X) : Ω → ℝ :=
  μ[w t a | 𝔾 t] - μ[w t a | 𝔽 t]

/-- The penalty of Proposition 2.2, p. 5: `z(a) = ∑_{t=0}^T z_t(a)`. -/
noncomputable def penalty (μ : Measure Ω) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (a : Fin (T + 1) → X) (ω : Ω) : ℝ :=
  ∑ t, penaltyComp μ 𝔽 𝔾 w t a ω

/-- Regularity of a sequence of generating functions `(w_0, …, w_T)` (Proposition 2.2, p. 5):
each `w_t` depends only on the first `t + 1` actions `a_0, …, a_t` (the page's hypothesis); and
(pinned) each `w_t(a)` is a.e. strongly measurable and the family is a.e. bounded by one
constant. -/
def GeneratingFns (μ : Measure Ω) (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) : Prop :=
  (∀ t a a', (∀ s, s ≤ t → a s = a' s) → w t a = w t a') ∧
  (∀ t a, AEStronglyMeasurable (w t a) μ) ∧
  (∃ C : ℝ, ∀ t a, ∀ᵐ ω ∂μ, |w t a ω| ≤ C)

variable [DecidableEq X]

/-- The dual value functions `V^𝔾_t` of eq. (10), p. 5: the recursion (2) with penalized
rewards `r_t − z_t`, `z_t` the penalty of Proposition 2.2 for `(𝔾, w)`, and conditional
expectations given `𝒢_t`; `V^𝔾_{T+1} = 0`. -/
noncomputable def dualValueFn (M : RecursiveDP Ω X T) (μ : Measure Ω)
    (𝔾 : Filtration (Fin (T + 1)) mΩ) (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) :
    ℕ → (Fin (T + 1) → X) → Ω → ℝ :=
  bellman μ 𝔾 M.Afeas (fun t a ω => M.rt t a ω - penaltyComp μ M.𝔽 𝔾 w t a ω)

/-- The generating functions of the ideal penalty, `w_t(a) = V_{t+1}(a_0, …, a_t)` (p. 5). -/
noncomputable def idealGen (M : RecursiveDP Ω X T) (μ : Measure Ω) :
    Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ :=
  fun t a => valueFn M μ ((t : ℕ) + 1) a

/-- The "ideal" penalty `z⋆` (p. 5): the penalty of Proposition 2.2 for the relaxation `𝔾` and
the generating functions `w_t(a) = V_{t+1}(a_0, …, a_t)`. -/
noncomputable def idealPenalty (M : RecursiveDP Ω X T) (μ : Measure Ω)
    (𝔾 : Filtration (Fin (T + 1)) mΩ) : (Fin (T + 1) → X) → Ω → ℝ :=
  penalty μ M.𝔽 𝔾 (idealGen M μ)

end InfoRelax.IdealPenalty


