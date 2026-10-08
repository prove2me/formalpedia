-- Prove2me | Definitions.Def_InfoRelax_RelaxOrder_Penalty
-- name    : InfoRelax_RelaxOrder_Penalty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:51.481458+00:00
-- url     : https://prove2.me/theorems/98cccb21-aaab-4efe-9688-2690d0191d5f
-- title:
--   Penalties from generating functions (Proposition 2.2) and the dual value functions (10)
-- statement:
--   Let $\mathbb H\subseteq\mathbb G$ be filtrations and $(w_0,\dots,w_T)$ a sequence of **generating functions** $w_t(a,\omega)$. The penalty they generate is
--   $$z_t(a)=\mathbb E[w_t(a)\mid\mathcal G_t]-\mathbb E[w_t(a)\mid\mathcal H_t],\qquad z(a)=\sum_{t=0}^T z_t(a).$$
--   With $\mathbb H=\mathbb F$, the natural filtration, this is the penalty of Proposition 2.2 for the relaxation $\mathbb G$; with $\mathbb H=\mathbb F'$, $\mathbb F\subseteq\mathbb F'\subseteq\mathbb G$, it is the penalty of Proposition 2.3(iii).
--
--   The generating functions are **regular** when each $w_t$ depends only on the first $t+1$ actions $a_0,\dots,a_t$ (the page's hypothesis), and each $w_t(a)$ is almost everywhere strongly measurable with $|w_t(a)|\le C$ almost surely for one constant $C$.
--
--   For a dynamic program in recursive form, a relaxation $\mathbb G$ of $\mathbb F$ and generating functions $w$, the **dual value functions** of (10) are $V^{\mathbb G}_{T+1}=0$ and, for $t=0,\dots,T$,
--   $$V^{\mathbb G}_t(a_0,\dots,a_{t-1})=\sup_{a_t\in A_t(a_0,\dots,a_{t-1})}\Big\{r_t(a_0,\dots,a_t)-z_t(a_0,\dots,a_t)+\mathbb E\big[V^{\mathbb G}_{t+1}(a_0,\dots,a_t)\,\big|\,\mathcal G_t\big]\Big\},$$
--   with $z_t$ the Proposition 2.2 penalty of $(\mathbb G,w)$.
--
--   These are the penalties compared in Proposition 2.3(i) and (iii), and the recursion that evaluates their dual bounds.
--
--   **Formalization Note** Conditional expectations are Mathlib's fixed versions, determined almost surely. The measurability and boundedness of the generating functions are pinned regularity assumptions, so that every conditional expectation exists and every penalty is integrable along every policy.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, Proposition 2.2 and eq. (10); p. 6, Proposition 2.3(iii)

import Mathlib
import Definitions.Def_InfoRelax_RelaxOrder_Framework
import Definitions.Def_InfoRelax_RelaxOrder_RecursiveModel

open MeasureTheory

namespace InfoRelax.RelaxOrder

/-!
# Penalties from generating functions (Proposition 2.2) and the dual recursion (10)

Brown, Smith & Sun, *Information Relaxations and Duality in Stochastic Dynamic Programs*,
Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, §2.3: Proposition 2.2
and eq. (10); p. 6, Proposition 2.3(iii).

For filtrations `ℍ ⊆ 𝔾` and generating functions `w_t(a, ω)`:
* `penaltyComp μ ℍ 𝔾 w t a = 𝔼[w_t(a) | 𝒢_t] − 𝔼[w_t(a) | ℋ_t]` is `z_t(a)`. With `ℍ = 𝔽` (the
  natural filtration) this is the penalty of Proposition 2.2; with `ℍ = 𝔽′`, `𝔽 ⊆ 𝔽′ ⊆ 𝔾`, it is
  the penalty of Proposition 2.3(iii);
* `penalty μ ℍ 𝔾 w a = ∑_{t=0}^T z_t(a)` is `z(a)`;
* `dualValueFn M μ 𝔾 w` is the dual value function `V^𝔾_t` of (10): the recursion (2) with the
  penalized rewards `r_t − z_t` (`z` the Proposition 2.2 penalty of `(𝔾, w)`) and the
  filtration `𝔾` in place of `𝔽`, with `V^𝔾_{T+1} = 0`.

`GeneratingFns` collects the regularity of generating functions used with Proposition 2.2.

**Formalization Note.**
* `w_t(a)` is defined for every action sequence (the page: on `A × Ω`); its regularity is
  required for every sequence.
* Pinned regularity: each `w_t(a)` is almost everywhere strongly measurable and the family is
  bounded almost everywhere by one constant, so that every conditional expectation exists and the
  penalty is integrable along every policy.
* Conditional expectations are Mathlib's `μ[· | m]` (fixed versions, determined a.e.).
* Identical in content to mission 1's `InfoRelax.IdealPenalty.Penalty` restricted to
  `penaltyComp`, `penalty`, `GeneratingFns`, `dualValueFn` (drafts cannot import drafts).
-/

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] {T : ℕ}

/-- The period-`t` penalty built from generating functions `w` (Proposition 2.2, p. 5, and
Proposition 2.3(iii), p. 6): `z_t(a) = 𝔼[w_t(a) | 𝒢_t] − 𝔼[w_t(a) | ℋ_t]`. -/
noncomputable def penaltyComp (μ : Measure Ω) (ℍ 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (t : Fin (T + 1))
    (a : Fin (T + 1) → X) : Ω → ℝ :=
  μ[w t a | 𝔾 t] - μ[w t a | ℍ t]

/-- The penalty `z(a) = ∑_{t=0}^T z_t(a)` (Proposition 2.2, p. 5). -/
noncomputable def penalty (μ : Measure Ω) (ℍ 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (a : Fin (T + 1) → X) (ω : Ω) : ℝ :=
  ∑ t, penaltyComp μ ℍ 𝔾 w t a ω

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

end InfoRelax.RelaxOrder


