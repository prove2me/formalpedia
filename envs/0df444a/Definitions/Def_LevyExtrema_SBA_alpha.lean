-- Prove2me | Definitions.Def_LevyExtrema_SBA_alpha
-- name    : LevyExtrema_SBA_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:44.256068+00:00
-- url     : https://prove2.me/theorems/aa0665e9-25b2-4d27-92c1-1a4aae1bb2e3
-- title:
--   The indices $\alpha$ and $\alpha_+=\alpha+(\beta_+-\beta)\mathbb 1_{\{\alpha=\beta\}}$ (4.21)
-- statement:
--   For a Lévy process with triplet $(\sigma^2,\nu,b)$, Blumenthal–Getoor index $\beta$ and natural drift $b_0$, the paper defines
--
--   $$\alpha=2\cdot\mathbb 1_{\{\sigma\ne0\}}+\mathbb 1_{\{\sigma=0\}}\begin{cases}1,& I^1_0<\infty\text{ and }b_0\ne0,\\ \beta,&\text{otherwise},\end{cases}\qquad \alpha_+=\alpha+(\beta_+-\beta)\cdot\mathbb 1_{\{\alpha=\beta\}}.\tag{4.21}$$
--
--   $\alpha\in[\beta,2]$ is the index that governs the small-time behaviour of the supremum: $\mathbb E[\overline X_t^p]$ is of order $t^{p/\alpha}$ for $p\le\alpha$. $\alpha_+$ replaces $\alpha$ by $\beta_+$ when $\alpha=\beta$. For a process that is not compound Poisson with drift, $\alpha_+>0$.
--
--   **Formalization Note** $\beta_+$ is the corrected `betaPlus`.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (4.21), p. 24

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_LevyMeasureIntegrals
import Definitions.Def_LevyExtrema_SBA_bgIndex
import Definitions.Def_LevyExtrema_SBA_naturalDrift
import Definitions.Def_LevyExtrema_SBA_betaPlus

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **The index α**, (4.21).
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, (4.21), p. 24:
"α = 2 · 1{σ≠0} + 1{σ=0} {1, I^1_0 < ∞ and b_0 ≠ 0; β, otherwise}". -/
noncomputable def alpha (Tr : Triplet) : ℝ :=
  if Tr.σ ≠ 0 then 2
  else if I0 Tr 1 < ⊤ ∧ naturalDrift Tr ≠ 0 then 1
  else bgIndex Tr

/-- **α₊ = α + (β₊ − β) · 1{α = β}**, (4.21), p. 24, with the (corrected) β₊ of `betaPlus`. -/
noncomputable def alphaPlus (Tr : Triplet) (δ : ℝ) : ℝ :=
  alpha Tr + (betaPlus Tr δ - bgIndex Tr) * (if alpha Tr = bgIndex Tr then 1 else 0)

end LevyExtrema.SBA


