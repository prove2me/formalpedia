-- Prove2me | Definitions.Def_BayesBAI_RegularPrior
-- name    : BayesBAI_RegularPrior
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:38.414695+00:00
-- url     : https://prove2.me/theorems/28cdc119-34de-40a7-88e2-0dfbd4f533d3
-- title:
--   Assumption 1: priors with uniformly continuous conditional densities
-- statement:
--   Let $H$ be a probability measure on $\mathbb R^K$. Data $h_i(x\mid\nu)$ and $h_{ij}(x,y\mid\nu)$ (for $i\ne j$) satisfy **Assumption 1** if:
--
--   1. $h_i$ and $h_{ij}$ are nonnegative and jointly measurable;
--   2. $h_i$ is a conditional density of $\mu_i$ given $\mu_{\setminus i}$: for every measurable $f\ge0$,
--   $$
--   \int f\,dH=\int\!\!\int_0^1 h_i(x\mid\nu)\,f(x,\nu)\,dx\,dH_{\setminus i}(\nu),
--   $$
--   and likewise $h_{ij}$ is a conditional density of $(\mu_i,\mu_j)$ given $\mu_{\setminus ij}$, over $H_{\setminus ij}$;
--   3. the uniform continuity (4) holds: for every $\epsilon>0$ there is $\delta>0$ such that for all conditioning vectors in the cube and all arguments in $[0,1]$,
--   $$
--   |\mu_i-\lambda_i|\le\delta\ \Rightarrow\ |h_i(\mu_i\mid\mu_{\setminus i})-h_i(\lambda_i\mid\mu_{\setminus i})|\le\epsilon,
--   $$
--   $$
--   |\mu_i-\lambda_i|,|\mu_j-\lambda_j|\le\delta\ \Rightarrow\ |h_{ij}(\mu_i,\mu_j\mid\mu_{\setminus ij})-h_{ij}(\lambda_i,\lambda_j\mid\mu_{\setminus ij})|\le\epsilon.
--   $$
--
--   As Remark 1 stresses, $\delta$ does not depend on $\mu$. This is the only regularity the prior needs for Theorem 1; arms may be correlated.
--
--   **Formalization Note.** The paper describes the $h$ through derivatives of conditional cumulative density functions. Here a conditional density is what disintegrates $H$, tested with `lintegral`. That $H$ lives on $[0,1]^K$ follows from the disintegration. Continuity is on $[0,1]$ only, since the zero extension of the uniform density to $\mathbb R$ is discontinuous; the uniform prior satisfies this structure (checked in a verification file at $K=2$).
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Assumption 1, eq. (4), §1.1, p.2

import Mathlib
import Definitions.Def_BayesBAI_dropOne
import Definitions.Def_BayesBAI_dropTwo
import Definitions.Def_BayesBAI_insertOne
import Definitions.Def_BayesBAI_insertTwo

open MeasureTheory Set
open scoped ENNReal

namespace BayesBAI

/-- Assumption 1 and the setting of §1.1, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.2:
`H` is a probability measure with conditional densities `h_i(x | ν)` and `h_ij(x, y | ν)`, which are
uniformly continuous on `[0, 1]`, with a `δ` that does not depend on the conditioning vector (Remark 1).

**Formalization Note.** The paper speaks of conditional cumulative density functions and their
continuous derivatives. Here a conditional density is what makes the disintegration of `H` over `H_\i`
(respectively `H_\ij`) hold, tested on measurable `f ≥ 0` by `lintegral`, with `h` jointly measurable.
That `H` lives on `[0, 1]^K` follows from `h_disint`, so it is not a separate field. Continuity is
required on `[0, 1]` only: extending the uniform density by zero to `ℝ` is discontinuous, and quantifying
over `ℝ` would exclude the paper's main example. Requiring (4) for every `ν` in the cube instead of
almost every `ν` loses nothing, as `h` can be changed to `0` on a null set of `ν`. -/
structure RegularPrior {K : ℕ} (H : Measure (Fin K → ℝ))
    (h : (i : Fin K) → ℝ → ({j : Fin K // j ≠ i} → ℝ) → ℝ)
    (hh : (i j : Fin K) → ℝ → ℝ → ({k : Fin K // k ≠ i ∧ k ≠ j} → ℝ) → ℝ) : Prop where
  /-- `H` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure H
  /-- `h_i` is nonnegative. -/
  h_nonneg : ∀ i x ν, 0 ≤ h i x ν
  /-- `h_i` is jointly measurable. -/
  h_measurable : ∀ i, Measurable (fun p : ℝ × ({j : Fin K // j ≠ i} → ℝ) => h i p.1 p.2)
  /-- `h_i` is a conditional density of `μ_i` given `μ_\i`. -/
  h_disint : ∀ (i : Fin K) (f : (Fin K → ℝ) → ℝ≥0∞), Measurable f →
    ∫⁻ μ, f μ ∂H = ∫⁻ ν, (∫⁻ x in Icc (0 : ℝ) 1,
      ENNReal.ofReal (h i x ν) * f (insertOne i x ν)) ∂(H.map (dropOne i))
  /-- `h_ij` is nonnegative. -/
  hh_nonneg : ∀ i j, i ≠ j → ∀ x y ν, 0 ≤ hh i j x y ν
  /-- `h_ij` is jointly measurable. -/
  hh_measurable : ∀ i j, i ≠ j →
    Measurable (fun p : ℝ × ℝ × ({k : Fin K // k ≠ i ∧ k ≠ j} → ℝ) => hh i j p.1 p.2.1 p.2.2)
  /-- `h_ij` is a conditional density of `(μ_i, μ_j)` given `μ_\ij`. -/
  hh_disint : ∀ (i j : Fin K), i ≠ j → ∀ f : (Fin K → ℝ) → ℝ≥0∞, Measurable f →
    ∫⁻ μ, f μ ∂H = ∫⁻ ν, (∫⁻ x in Icc (0 : ℝ) 1, ∫⁻ y in Icc (0 : ℝ) 1,
      ENNReal.ofReal (hh i j x y ν) * f (insertTwo i j x y ν)) ∂(H.map (dropTwo i j))
  /-- The uniform continuity (4), with `δ` independent of the conditioning vector. -/
  uniform_continuity : ∀ ε > 0, ∃ δ > 0,
    (∀ (i : Fin K) (ν : {j : Fin K // j ≠ i} → ℝ), (∀ j, ν j ∈ Icc (0 : ℝ) 1) →
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ δ → |h i x ν - h i y ν| ≤ ε) ∧
    (∀ (i j : Fin K), i ≠ j → ∀ ν : {k : Fin K // k ≠ i ∧ k ≠ j} → ℝ,
      (∀ k, ν k ∈ Icc (0 : ℝ) 1) →
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, ∀ y' ∈ Icc (0 : ℝ) 1,
        |x - x'| ≤ δ → |y - y'| ≤ δ → |hh i j x y ν - hh i j x' y' ν| ≤ ε)

end BayesBAI


