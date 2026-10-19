-- Prove2me | Definitions.Def_ImperfReport_Regulator_Model
-- name    : ImperfReport_Regulator_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:03.254988+00:00
-- url     : https://prove2.me/theorems/5cba36f9-a7b7-4674-813b-057158076b45
-- title:
--   The value distribution and disclosure cutoff
-- statement:
--   The firm's value is $\omega=\omega_1+\omega_2$, where the reportable component $\omega_1$ is one with prior probability $\alpha\in(0,1)$ and zero otherwise. The independent component $\omega_2$ has an atomless probability law $\mu$ on $[0,1]$, with full support there. Its mean is $\beta$, its second moment is $m_2=\sigma^2+\beta^2$, and its cumulative distribution is $F$.
--
--   If the firm learns $\omega_2$ with probability $q$, the nondisclosure cutoff $t^\dagger(q)$ is the unique value in $[0,1]$ that makes the investors' posterior mean after nondisclosure equal to the cutoff. The inverse probability $q^\dagger(t)$ is the formula in Corollary 1.
--
--   This definition supplies the shared distribution and cutoff objects for every result in the mission. **Formalization Note** The paper's differentiable density is represented by an atomless measure with full support. The cutoff equation is cross-multiplied; its meaning on $q\in[0,1]$ is established by Lemma 1.
-- source:
--   Friedman, Hughes, Michaeli, A Rationale for Imperfect Reporting Standards, SSRN 3636995 (version of November 24, 2020), pp. 9, 12, 15, model and Lemma 1/Corollary 1

import Mathlib

set_option autoImplicit false
open MeasureTheory Set

namespace ImperfReport.Regulator

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020), p. 9, model. The prior probability
`alpha` concerns the reportable binary value, `k` is the payoff threshold, and
`mu` is the law of the independent continuous component on `[0,1]`. -/
structure Model where
  alpha : ℝ
  k : ℝ
  mu : Measure ℝ

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
pp. 9, 12, model assumptions. Formalization Note: `mu` is atomless and has full
support on `[0,1]`; this replaces the paper's differentiable CDF and density and
rules out flat intervals in the cutoff map. -/
def Model.Standing (M : Model) : Prop :=
  0 < M.alpha ∧ M.alpha < 1 ∧ 0 ≤ M.k ∧ M.k ≤ 2 ∧
  IsProbabilityMeasure M.mu ∧ M.mu ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
  NoAtoms M.mu ∧
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → 0 < M.mu (Set.Ioo a b)

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 9, `β = E[ω₂]`. -/
noncomputable def beta (M : Model) : ℝ := ∫ x, x ∂M.mu

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 9, `σ² + β² = E[ω₂²]`. -/
noncomputable def m2 (M : Model) : ℝ := ∫ x, x ^ 2 ∂M.mu

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 9, the CDF of the continuous value component. -/
noncomputable def F (M : Model) (t : ℝ) : ℝ := M.mu.real (Set.Iic t)

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 15, Lemma 1, Bayes indifference at the nondisclosure cutoff. Formalization
Note: the equality is cross-multiplied so the zero-probability nondisclosure
event at `q = 1, t = 0` does not require division by zero. Disclosure is for
`s > t`; equality is null under `NoAtoms`. -/
noncomputable def IsCutoff (M : Model) (q t : ℝ) : Prop :=
  t ∈ Set.Icc (0 : ℝ) 1 ∧
  (1 - q) * beta M + q * (∫ x in Set.Iic t, x ∂M.mu) =
    t * ((1 - q) + q * F M t)

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 15, Lemma 1, the unique disclosure cutoff. Formalization Note: the infimum
denotes the cutoff only after Lemma 1 establishes existence and uniqueness on
`q ∈ [0,1]`; outside that range it has no economic interpretation. -/
noncomputable def tdag (M : Model) (q : ℝ) : ℝ := sInf {t : ℝ | IsCutoff M q t}

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 15, Corollary 1, the information-acquisition probability inducing a cutoff.
Its denominator is positive for the theorem's domain `0 ≤ t ≤ β`. -/
noncomputable def qdag (M : Model) (t : ℝ) : ℝ :=
  (beta M - t) / (beta M - t + ∫ x in (0)..t, F M x)

end ImperfReport.Regulator


