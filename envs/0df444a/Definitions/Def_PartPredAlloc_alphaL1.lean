-- Prove2me | Definitions.Def_PartPredAlloc_alphaL1
-- name    : PartPredAlloc_alphaL1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:41.168287+00:00
-- url     : https://prove2.me/theorems/8ffc19a1-eca1-4e34-ac85-cbbd07971fb0
-- title:
--   Constants $\alpha=10+2\sqrt6$, $\bar\epsilon=1/24$, $k=16$, $\Delta$, $\theta$ and the error scale $\epsilon$
-- statement:
--   The constants of the analysis of Algorithm 1:
--
--   1. $\alpha=10+2\sqrt6$, $\bar\epsilon=1/24$ and $k=16$ (Lemma 1);
--   2. $\Delta=\alpha\sqrt{b\log n}$ (proof of Theorem 1);
--   3. the fixed threshold fraction $\theta=\dfrac{1-p}{2-a}$ (Algorithm 1);
--   4. the error scale
--   $$
--   \epsilon=\frac{1}{a(1-p)p}\sqrt{\frac{\log n}{b}}
--   $$
--   (proof of Theorem 1).
--
--   **Formalization Note** $\log$ is the natural logarithm. The theorems using $\theta$ and $\epsilon$ assume $a,p\in(0,1)$ and $b\ge1$, so no division by zero occurs there.
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Lemma 1, p.12; Algorithm 1, p.15; proof of Theorem 1, p.16

import Mathlib

namespace PartPredAlloc

/-- The constant `α ≜ 10 + 2√6` of Lemma 1 (arXiv:1810.00447v1, p.12). -/
noncomputable def alphaL1 : ℝ := 10 + 2 * Real.sqrt 6

/-- The constant `ε̄ ≜ 1/24` of Lemma 1 (arXiv:1810.00447v1, p.12). -/
noncomputable def epsBar : ℝ := 1 / 24

/-- The constant `k ≜ 16` of Lemma 1 (arXiv:1810.00447v1, p.12). -/
noncomputable def kL1 : ℝ := 16

/-- `∆ ≜ α √(b log n)` (arXiv:1810.00447v1, proof of Theorem 1, p.16); `log` is the natural
logarithm. -/
noncomputable def Delta (n b : ℕ) : ℝ := alphaL1 * Real.sqrt ((b : ℝ) * Real.log n)

/-- The fixed threshold fraction `θ ≜ (1 − p)/(2 − a)` (arXiv:1810.00447v1, Algorithm 1, p.15). -/
noncomputable def theta (a p : ℝ) : ℝ := (1 - p) / (2 - a)

/-- The error scale `ε ≜ (1/(a(1 − p)p)) √(log n / b)` (arXiv:1810.00447v1, proof of Theorem 1,
p.16); `log` is the natural logarithm.

**Formalization Note.** The theorems using it assume `a, p ∈ (0, 1)` and `b ≥ 1`, so no division by
zero occurs there. -/
noncomputable def epsErr (n b : ℕ) (a p : ℝ) : ℝ :=
  1 / (a * (1 - p) * p) * Real.sqrt (Real.log n / b)

end PartPredAlloc


