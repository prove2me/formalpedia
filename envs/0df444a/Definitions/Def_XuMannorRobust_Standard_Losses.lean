-- Prove2me | Definitions.Def_XuMannorRobust_Standard_Losses
-- name    : XuMannorRobust_Standard_Losses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T15:27:42.800364+00:00
-- url     : https://prove2.me/theorems/c270b325-8a94-4765-b33a-a567e265e658
-- title:
--   Expected error $\mathcal L(h)$ and training error $l_{\mathrm{emp}}(h)$
-- statement:
--   Let $\mathcal Z$ be a measurable space of samples, $\mathcal H$ a set of hypotheses and $l : \mathcal H \times \mathcal Z \to \mathbb R$ a loss function. For a probability measure $\mu$ on $\mathcal Z$, a hypothesis $h \in \mathcal H$ and a training set $\mathbf s = (s_1, \dots, s_n) \in \mathcal Z^n$, the **expected error** and the **training error** of $h$ are
--
--   $$\mathcal L(h) = \mathbb E_{z \sim \mu}\, l(h, z), \qquad l_{\mathrm{emp}}(h) = \frac1n \sum_{i=1}^n l(h, s_i).$$
--
--   For a learning algorithm $\mathcal A$ these are evaluated at the learned hypothesis $h = \mathcal A_{\mathbf s}$; the difference $\mathcal L(\mathcal A_{\mathbf s}) - l_{\mathrm{emp}}(\mathcal A_{\mathbf s})$ is the generalization gap that Theorem 1 of Xu and Mannor bounds.
--
--   **Formalization Note** The expectation is the Bochner integral, which Lean sets to $0$ for a non-integrable function; every theorem of this mission assumes the loss is measurable and bounded, so it is integrable against a probability measure. The factor $1/n$ is $0$ for $n = 0$; every theorem assumes $n \ge 1$.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 396, Sect. 3 (definitions of L(A_s) and l_emp(A_s))

import Mathlib

open MeasureTheory

namespace XuMannorRobust.Standard

/-- **Expected error** (Xu & Mannor 2012, p. 396, Sect. 3): `𝓛(h) = E_{z∼μ} l(h, z)`, the Bochner
integral of the loss of the hypothesis `h` against the sample distribution `μ`. -/
noncomputable def expectedLoss {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (l : H → Z → ℝ) (h : H) : ℝ :=
  ∫ z, l h z ∂μ

/-- **Training error** (Xu & Mannor 2012, p. 396, Sect. 3):
`l_emp(h) = (1/n) ∑_{i=1}^n l(h, s_i)` on the training set `s = (s_1, …, s_n)`. -/
noncomputable def empiricalLoss {Z H : Type*} {n : ℕ} (l : H → Z → ℝ) (h : H)
    (s : Fin n → Z) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, l h (s i)

end XuMannorRobust.Standard


