-- Prove2me | Definitions.Def_SparseBatchBandit_Assumption1
-- name    : SparseBatchBandit_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:02.771308+00:00
-- url     : https://prove2.me/theorems/d382321a-5b6c-4847-9de2-bd1c188f01de
-- title:
--   Assumption 1 (Sub-Gaussianity)
-- statement:
--   **Assumption 1.** For every arm $a$ the marginal law of $x_{t,a}$ is 1-sub-Gaussian: for every unit vector $v$, the real variable $v^\top x_{t,a}$ is 1-sub-Gaussian.
--
--   **Formalization Note** The paper's display is written at unit scale only, which is not sub-Gaussianity. It is read at every scale, $\mathbb E[e^{\lambda v^\top x}]\le e^{\lambda^2/2}$ for all $\lambda$, as the paper writes it for the noise and as its proof uses it on p.18. Mean zero follows.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Assumption 1, p.5

import Mathlib
open MeasureTheory ProbabilityTheory Matrix

namespace SparseBatchBandit

/-- **Assumption 1** (Sub-Gaussianity), Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, p.5 (PDF 5): every marginal `x_{t,a}` is 1-sub-Gaussian,
that is, `⟨v, x_{t,a}⟩` is 1-sub-Gaussian for every unit vector `v`.

**Formalization Note.** The page's display, at unit `v` only, is the name "1-sub-Gaussian" written
at one scale. It is read at every scale, as §2.1 writes it for the noise ("∀λ ∈ ℝ") and as the proof
uses it on p.18. `HasSubgaussianMGF` implies `E[⟨v, x_{t,a}⟩] = 0`, so `E[X] = 0` is contained. -/
def Assumption1 {Ω : Type*} [MeasurableSpace Ω] {T K d : ℕ} (P : Measure Ω)
    (x : Ω → Fin T → Fin K → Fin d → ℝ) : Prop :=
  ∀ (t : Fin T) (a : Fin K) (v : Fin d → ℝ), ∑ j, v j ^ 2 = 1 →
    HasSubgaussianMGF (fun ω => v ⬝ᵥ x ω t a) 1 P

end SparseBatchBandit


