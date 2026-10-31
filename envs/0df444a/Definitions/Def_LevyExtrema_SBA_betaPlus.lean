-- Prove2me | Definitions.Def_LevyExtrema_SBA_betaPlus
-- name    : LevyExtrema_SBA_betaPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:12.092151+00:00
-- url     : https://prove2.me/theorems/29415ce9-69b0-4d85-8b75-85a785dfd0e7
-- title:
--   $\beta_+=\beta+\delta\mathbb 1_{\{I^\beta_0=\infty\}}$ (4.6) and admissible $\delta$ (corrected: β+ = δ when β = 0)
-- statement:
--   Let $\beta$ be the Blumenthal–Getoor index. The paper sets
--
--   $$\beta_+=\beta+\delta\cdot\mathbb 1_{\{I^\beta_0=\infty\}}\in[\beta,2],\tag{4.6}$$
--
--   where, when $I^\beta_0=\infty$, $\delta\in(0,2-\beta)$ is chosen with $\beta+\delta<1$ whenever $\beta<1$. Then $I^{\beta_+}_0<\infty$ always.
--
--   This definition **corrects** (4.6) in one case: $\beta_+=\beta+\delta$ also when $\beta=0$. A number $\delta$ is **admissible** if, whenever $I^\beta_0=\infty$ or $\beta=0$, it satisfies $0<\delta<2-\beta$ and ($\beta<1\Rightarrow\beta+\delta<1$); otherwise $\delta$ plays no role.
--
--   **Formalization Note** As printed, (4.6) gives $\beta_+=0$ for Brownian motion ($\sigma=1$, $\nu=0$: $\beta=0$, $I^0_0=0<\infty$), and then the exponents $p/\beta_+$ of (4.12), (4.13) and (4.23) are undefined. With the correction $\beta_+=\delta\in(0,1)$ in that case. The change affects no instance in which the paper's formulas are defined, keeps $I^{\beta_+}_0<\infty$, $\beta_+\le2$ and $\beta_+\le1$ when $I^1_0<\infty$, and never changes $\alpha_+$ or $\eta_p$ for a process that is not compound Poisson with drift.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (4.6), p. 21

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_LevyMeasureIntegrals
import Definitions.Def_LevyExtrema_SBA_bgIndex

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **Admissible δ for β₊**, (4.6), with the correction for β = 0.
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, p. 21: "If I^β_0 = ∞ we must have
β < 2 and can thus pick δ ∈ (0, 2 − β), satisfying β + δ < 1 whenever β < 1".

`AdmissibleDelta Tr δ`: if `I^β_0 = ∞` or `β = 0`, then `δ ∈ (0, 2 − β)` and `β + δ < 1` when
`β < 1`. Otherwise every δ is admissible (δ is not used).

**Formalization Note (correction).** The disjunct `β = 0` is added together with the matching
change in `betaPlus`: see there. -/
def AdmissibleDelta (Tr : Triplet) (δ : ℝ) : Prop :=
  (I0 Tr (bgIndex Tr) = ⊤ ∨ bgIndex Tr = 0) →
    (0 < δ ∧ δ < 2 - bgIndex Tr ∧ (bgIndex Tr < 1 → bgIndex Tr + δ < 1))

/-- **β₊ = β + δ · 1{I^β_0 = ∞}**, (4.6), p. 21, **corrected**: β₊ = β + δ also when β = 0.

**Formalization Note (correction).** As printed, (4.6) gives β₊ = 0 when β = 0 and
`I^0_0 = ν((−1,1)) < ∞` (e.g. Brownian motion: σ = 1, ν = 0), and then `p/β₊` in (4.12), (4.13),
(4.23) is undefined. Here β₊ = δ in that case (δ ∈ (0, 1) by `AdmissibleDelta`). This changes no
instance where the paper's formulas are defined, keeps `I^{β₊}_0 < ∞`, `β₊ ≤ 2`, and `β₊ ≤ 1` when
`I^1_0 < ∞`, and never changes α₊ or η_p (under "not compound Poisson with drift", β₊ = 0 in the
paper forces σ ≠ 0, so α = 2 ≠ β). -/
noncomputable def betaPlus (Tr : Triplet) (δ : ℝ) : ℝ :=
  if I0 Tr (bgIndex Tr) = ⊤ ∨ bgIndex Tr = 0 then bgIndex Tr + δ else bgIndex Tr

end LevyExtrema.SBA


