-- Prove2me | Definitions.Def_LearnManip_Policy
-- name    : LearnManip_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:06.112147+00:00
-- url     : https://prove2.me/theorems/17335801-f338-47dd-a8b6-dc5219d9af95
-- title:
--   Learning manipulation policies $M=(q_t,\Lambda_t)_{t\in\mathbb N}$
-- statement:
--   A policy for prior variance $s_0$ assigns to each history $(\mu_0,\dots,\mu_n)$ a quantity $q\ge0$ for the next period and a distorted law for the next posterior mean. It may depend on the whole past, and both components are measurable in the history. At each history the law must be a distortion of the undistorted law of the next posterior mean, at the current mean and variance.
--
--   The distorted law is an arbitrary kernel subject to this constraint, not a Gaussian. This is the object over which the value function (8) optimizes.
--
--   **Formalization Note.** The rules are defined on every history, also unreachable ones, as a measurable function must be. The measurability of the relative entropy in the history is a field: on $\mathbb R$ it holds automatically, and it makes the expected distortion cost an integral of a measurable function. Admissibility in the sense of expectations existing is `IsAdmissible`.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), §2, p.11

import Mathlib
import Definitions.Def_LearnManip_baseLaw
import Definitions.Def_LearnManip_IsDistortion
import Definitions.Def_LearnManip_History
import Definitions.Def_LearnManip_varPath

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- A learning manipulation policy `M = (δ_t)_{t∈ℕ} = (q_t, Λ_t)_{t∈ℕ}` of §2, p.11, of Keppo, Kim,
Zhang (SSRN 3465030, 2021-09-04), for prior variance `s₀`: it is adapted to the filtration of the
belief process, so both components may depend on the whole past of posterior means.

* `q n h` is the quantity of period `t = n + 1` after the history `h = (μ₀, …, μ_n)`.
* `K n h` is the distorted law of `μ_{n+1}`, an arbitrary distortion of the undistorted law.

**Formalization Note.** Measurability in the history is the meaning of "adapted". `kl_measurable`
makes the expected distortion cost in `horizonValue` an integral of a measurable function; on `ℝ`
this holds automatically for a kernel, so it excludes no policy. The integrability of the `μ_t`,
needed for `E_π` in (8), is `IsAdmissible`, since it depends on the initial mean. -/
structure Policy (s₀ : ℝ≥0) where
  /-- The dissemination quantity. -/
  q : (n : ℕ) → History n → ℝ≥0
  /-- The distorted law of the next posterior mean. -/
  K : (n : ℕ) → Kernel (History n) ℝ
  q_measurable : ∀ n, Measurable (q n)
  distortion : ∀ n h, IsDistortion (History.last h) (varPath q s₀ n h) (q n h) (K n h)
  kl_measurable : ∀ n, Measurable fun h : History n =>
    InformationTheory.klDiv (K n h) (baseLaw (History.last h) (varPath q s₀ n h) (q n h))

instance Policy.isMarkovKernel {s₀ : ℝ≥0} (M : Policy s₀) (n : ℕ) : IsMarkovKernel (M.K n) :=
  ⟨fun h => (M.distortion n h).isProb⟩

end LearnManip


