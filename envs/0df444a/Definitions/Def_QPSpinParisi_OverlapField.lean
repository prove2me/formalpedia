-- Prove2me | Definitions.Def_QPSpinParisi_OverlapField
-- name    : QPSpinParisi_OverlapField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:46.391705+00:00
-- url     : https://prove2.me/theorems/9f399435-9a3b-468d-822b-4eb9384fe70e
-- title:
--   A realization of the Gaussian field $Y_n$
-- statement:
--   A realization of the process $Y_n$ is a probability space with a centered Gaussian process $(Y_n(s))_{s\in(S^2)^n}$ with
--   $$\mathbb E\,Y_n(s)Y_n(t)=n\,\xi(q(s,t))$$
--   and almost surely continuous paths. This is the classical vector spin glass to which $X_n$ is compared.
--
--   **Formalization Note** The paper builds $Y_n$ as $\sum_pc_pY_{n,p}$ from independent processes on an unnamed space. Only the covariance is used, so statements hold for every realization.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.11 (PDF p.11)

import Mathlib
import Definitions.Def_QPSpinParisi_xiS
import Definitions.Def_QPSpinParisi_qOv

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- A realization of the process `Y_n` on `(S²)ⁿ` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.11, PDF p.11): a centered Gaussian process with
covariance `E Y_n(s) Y_n(t) = n ξ(q(s,t))` and almost surely continuous paths.

**Formalization Note** The paper builds `Y_n` as `∑_p c_p Y_{n,p}` on an unnamed space. Only the covariance is used,
so the statements of the mission hold for every field of this structure; `exists_overlapField` says that one exists. -/
structure OverlapField (c : ℕ → ℝ) (n : ℕ) where
  /-- The probability space. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- Its probability measure. -/
  P : Measure Ω
  /-- `P` has mass one. -/
  isProb : IsProbabilityMeasure P
  /-- The field. -/
  Y : RGGDetect.Config n 3 → Ω → ℝ
  /-- Each value is a random variable. -/
  measurable_Y : ∀ s, Measurable (Y s)
  /-- The process is Gaussian. -/
  gaussian : IsGaussianProcess Y P
  /-- The process is centered. -/
  centered : ∀ s, ∫ ω, Y s ω ∂P = 0
  /-- The covariance is `n ξ(q(s,t))`. -/
  cov : ∀ s t, ∫ ω, Y s ω * Y t ω ∂P = n * xiS c (qOv s t)
  /-- Almost every path is continuous. -/
  continuous_paths : ∀ᵐ ω ∂P, Continuous fun s => Y s ω

attribute [instance] OverlapField.mΩ OverlapField.isProb

end QPSpinParisi


