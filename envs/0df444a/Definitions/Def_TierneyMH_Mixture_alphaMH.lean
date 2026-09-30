-- Prove2me | Definitions.Def_TierneyMH_Mixture_alphaMH
-- name    : TierneyMH_Mixture_alphaMH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T02:10:35.542437+00:00
-- url     : https://prove2.me/theorems/16e0015a-ec8c-4051-9e35-9d34e433111c
-- title:
--   The Metropolis–Hastings acceptance probability $\alpha_{MH}(x,y)=\min\{1,r(y,x)\}$ on $R$, $0$ off $R$
-- statement:
--   Let $\pi$ be the target distribution and $Q$ the proposal kernel, and let $R$ and $r$ be the set and ratio of Proposition 1 for $\mu(dx,dy)=\pi(dx)Q(x,dy)$, built from $h=d\mu/d(\mu+\mu^T)$. The standard **Metropolis–Hastings acceptance probability** is
--
--   $$\alpha_{MH}(x,y)=\begin{cases}\min\{1,r(y,x)\}, & (x,y)\in R,\\ 0, & (x,y)\notin R.\end{cases}$$
--
--   On $R$ this is $\min\{1, h(y,x)/h(x,y)\}$; when $\pi$ and $Q$ have densities it reduces to the familiar $\min\{1, \pi(y)q(y,x)/(\pi(x)q(x,y))\}$. It takes values in $[0,1]$ and gives a reversible kernel; among all acceptance probabilities for the same proposal it is the largest that does.
--
--   **Formalization Note** The paper's $\alpha_{MH}$ is determined only $\mu$-almost everywhere, because it is built from Radon–Nikodym densities. This definition fixes one version (from `canonR` and `canonRatio`), and every statement of the mission about it is insensitive to the choice of version. The page calls $\alpha_{MH}$ the "rejection probability"; it is the acceptance probability. The file also records the structural fact $\alpha_{MH}\le 1$.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 3, §2 (definition of α_MH)

import Mathlib
import Definitions.Def_TierneyMH_Mixture_canonR
import Definitions.Def_TierneyMH_Mixture_canonRatio

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Mixture

/-- The **Metropolis–Hastings acceptance probability** `α_MH` (Tierney 1998, §2, p. 3) for
the proposal kernel `Q` and target `π`:
`α_MH(x, y) = min{1, r(y, x)}` if `(x, y) ∈ R`, and `0` if `(x, y) ∉ R`,
where `R = canonR π Q` and `r = canonRatio π Q` are the set and ratio of Proposition 1 for
`μ(dx, dy) = π(dx) Q(x, dy)`, built as in its proof from `h = dμ/d(μ + μᵀ)`.

The paper's `α_MH` is determined only `μ`-almost everywhere (through Radon–Nikodym
derivatives); this is one fixed version, and every statement of the mission about it is
insensitive to the choice of version. (The page calls it the "rejection probability"; it is the
acceptance probability.) -/
noncomputable def alphaMH {E : Type*} [MeasurableSpace E] (π : Measure E) (Q : Kernel E E) :
    E × E → ℝ≥0∞ :=
  (canonR π Q).indicator (fun p => min 1 (canonRatio π Q p.swap))

/-- `α_MH` takes values in `[0, 1]` (structural). -/
theorem alphaMH_le_one {E : Type*} [MeasurableSpace E] (π : Measure E) (Q : Kernel E E)
    (p : E × E) : alphaMH π Q p ≤ 1 := by
  unfold alphaMH
  by_cases h : p ∈ canonR π Q
  · rw [Set.indicator_of_mem h]; exact min_le_left _ _
  · rw [Set.indicator_of_notMem h]; exact zero_le_one

end TierneyMH.Mixture


