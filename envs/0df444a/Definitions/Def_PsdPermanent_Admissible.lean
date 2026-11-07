-- Prove2me | Definitions.Def_PsdPermanent_Admissible
-- name    : PsdPermanent_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:08.00341+00:00
-- url     : https://prove2.me/theorems/24cccf8a-b66f-4243-9814-850c0cfe95ed
-- title:
--   The admissible class $\mathcal A_U$ and the Gibbs objective
-- statement:
--   For $U:\mathbb C^d\to\mathbb R\cup\{-\infty\}$, the class $\mathcal A_U$ consists of the probability densities $\mu$ on $\mathbb C^d$ for which $\mathbb E_\mu[Z^\dagger Z]<\infty$, $h(\mu)$ is well-defined, and $\mathbb E_\mu[U(Z)]$ is well-defined, so that
--   $$\mathbb E_\mu[U(Z)]-\mathbb E_\mu[Z^\dagger Z]+h(\mu)-d\log\pi$$
--   has no indeterminate form $\infty-\infty$.
--
--   **Formalization Note** $\mathbb E_\mu[U(Z)]$ is the `EReal` difference of two `lintegral`s. Since $\top+\bot=\bot$ in `EReal`, the definition excludes outright the case where one of $\mathbb E_\mu[U(Z)]$, $h(\mu)$ is $+\infty$ and the other $-\infty$.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 4, p.5

import Mathlib
import Definitions.Def_PsdPermanent_IsProbDensity
import Definitions.Def_PsdPermanent_entropy
import Definitions.Def_PsdPermanent_secondMoment
open MeasureTheory

namespace PsdPermanent

/-- The part of `E_f[U]` from the positive values of `U`. -/
noncomputable def expectationPos {d : ℕ} (U : (Fin d → ℂ) → EReal) (f : (Fin d → ℂ) → ℝ) : ENNReal :=
  ∫⁻ z, (U z).toENNReal * ENNReal.ofReal (f z)

/-- The part of `E_f[U]` from the negative values of `U`. -/
noncomputable def expectationNeg {d : ℕ} (U : (Fin d → ℂ) → EReal) (f : (Fin d → ℂ) → ℝ) : ENNReal :=
  ∫⁻ z, (-U z).toENNReal * ENNReal.ofReal (f z)

/-- `E_f[U(Z)]` in the extended reals. -/
noncomputable def expectation {d : ℕ} (U : (Fin d → ℂ) → EReal) (f : (Fin d → ℂ) → ℝ) : EReal :=
  (expectationPos U f : EReal) - (expectationNeg U f : EReal)

/-- The trial value in the Gibbs formula, Lemma 4, p.5:
`E_f[U(Z)] − E_f[Z†Z] + h(f) − d log π`. -/
noncomputable def gibbsObjective {d : ℕ} (U : (Fin d → ℂ) → EReal) (f : (Fin d → ℂ) → ℝ) : EReal :=
  expectation U f - ((∫ z, zDaggerZ z * f z : ℝ) : EReal) + entropy f - (((d : ℝ) * Real.log Real.pi : ℝ) : EReal)

/-- **The admissible class A_U.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 4, p.5: "Let A_U be the set of probability densities µ on C^d for which E_µ[Z†Z] < ∞, h(µ) is
well-defined, and E_µ[U(Z)] is well-defined, so that the expression below has no indeterminate ∞ − ∞
form."

**Formalization Note.** `E_f[U]` is built from two `lintegral` parts, never from a Bochner integral. In
`EReal`, `⊤ + ⊥ = ⊥` and `⊤ − ⊤ = ⊥`, so the last two clauses exclude outright the indeterminate form in
`gibbsObjective`, in either order, and the two well-definedness clauses exclude it inside `entropy` and
`expectation`. -/
def Admissible {d : ℕ} (U : (Fin d → ℂ) → EReal) (f : (Fin d → ℂ) → ℝ) : Prop :=
  IsProbDensity f ∧ FiniteSecondMoment f ∧ EntropyWellDefined f ∧
    ¬ (expectationPos U f = ⊤ ∧ expectationNeg U f = ⊤) ∧
    ¬ (expectation U f = ⊤ ∧ entropy f = ⊥) ∧
    ¬ (expectation U f = ⊥ ∧ entropy f = ⊤)

end PsdPermanent


