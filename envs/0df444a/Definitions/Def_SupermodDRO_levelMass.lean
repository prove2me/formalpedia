-- Prove2me | Definitions.Def_SupermodDRO_levelMass
-- name    : SupermodDRO_levelMass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:58.176463+00:00
-- url     : https://prove2.me/theorems/6c9cd989-377d-40ef-ba33-6b4649f88407
-- title:
--   Worst-case marginal masses (5) on the levels lower / mean / upper
-- statement:
--   For one coordinate with mean $\mu$, MAD bound $\delta$ and support $[\underline z,\overline z]$, let
--   $$
--   \hat\delta=\min\Bigl\{\delta,\ \frac{2(\overline z-\mu)(\mu-\underline z)}{\overline z-\underline z}\Bigr\}.
--   $$
--   The three **levels** $0,1,2$ of the coordinate have the values $\underline z,\mu,\overline z$, and, when $\underline z<\overline z$, the masses of (5):
--   $$
--   \frac{\hat\delta}{2(\mu-\underline z)},\qquad 1-\frac{\hat\delta(\overline z-\underline z)}{2(\overline z-\mu)(\mu-\underline z)},\qquad \frac{\hat\delta}{2(\overline z-\mu)} .
--   $$
--   When $\underline z=\overline z$ (one support point) the masses are $(1,0,0)$.
--
--   These are the masses Algorithm 1 reads in lines 2 and 7.
--
--   **Formalization Note** The degenerate case corrects the paper, which assigns mass $1$ to each of the three coincident points for such a coordinate (p.8) and feeds these masses to Algorithm 1. With masses $(1,1,1)$ the weights returned by Algorithm 1 sum to $3$ and Theorem 1 fails (one coordinate, one scenario, $\delta=0$, $g\equiv1$: Problem (2) has value $1$ and LP (6) value $3$). Masses $(1,0,0)$ describe the same Dirac marginal, counted once.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Proposition 1, (5) and the definition of δ̂, p.8; Algorithm 1 lines 2 and 7, p.10

import Mathlib

namespace SupermodDRO

/-- **`δ̂ᵢᵏ`, p.8.** Long, Qi & Zhang, *Supermodularity in Two-Stage Distributionally Robust
Optimization*, author manuscript (June 2022), Proposition 1, p.8: "δ̂ᵢᵏ = min{δᵢᵏ,
2(z̄ᵢᵏ − µᵢᵏ)(µᵢᵏ − z̲ᵢᵏ)/(z̄ᵢᵏ − z̲ᵢᵏ)} for all i ∈ [n] with z̄ᵢᵏ > z̲ᵢᵏ."

For one coordinate with mean `μ`, MAD bound `δ` and support `[zl, zu]`.

**Formalization Note** Used only when `zl < zu`; there the denominator is positive. -/
noncomputable def deltaHat (μ δ zl zu : ℝ) : ℝ :=
  min δ (2 * (zu - μ) * (μ - zl) / (zu - zl))

/-- **The three levels of a coordinate.** Level `0` is the lower bound `z̲ᵢᵏ`, level `1` the mean
`µᵢᵏ`, level `2` the upper bound `z̄ᵢᵏ` (the three support points of (5), p.8, and the three values
a coordinate takes in Algorithm 1, p.10). -/
def levelValue (μ zl zu : ℝ) : Fin 3 → ℝ :=
  ![zl, μ, zu]

/-- **The worst-case marginal masses (5), p.8, on the three levels.** Long, Qi & Zhang,
*Supermodularity in Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022),
Proposition 1, (5), p.8:
"ℙ^{k*}(z̃ᵢ = w) = δ̂ᵢᵏ/(2(µᵢᵏ − z̲ᵢᵏ)) if w = z̲ᵢᵏ; 1 − δ̂ᵢᵏ(z̄ᵢᵏ − z̲ᵢᵏ)/(2(z̄ᵢᵏ − µᵢᵏ)(µᵢᵏ − z̲ᵢᵏ)) if
w = µᵢᵏ; δ̂ᵢᵏ/(2(z̄ᵢᵏ − µᵢᵏ)) if w = z̄ᵢᵏ; 0 otherwise."

For a coordinate with `zl < zu` the masses of levels `0, 1, 2` are the three lines of (5). For a
coordinate with `zl = zu` (then `zl = μ = zu`, one support point) the masses are `(1, 0, 0)`.

**Formalization Note** The degenerate case is a correction. The paper (p.8) writes
"ℙ^{k*}(z̃ᵢ = z̄ᵢᵏ) = ℙ^{k*}(z̃ᵢ = µᵢᵏ) = ℙ^{k*}(z̃ᵢ = z̲ᵢᵏ) = 1" for such a coordinate, and Algorithm 1
reads its three masses from there; with masses `(1, 1, 1)` the weights returned by Algorithm 1 sum
to `3` and Theorem 1 fails (one coordinate, one scenario, `δ = 0`, `g ≡ 1`: Problem (2) has value
`1`, LP (6) has value `3`). Masses `(1, 0, 0)` describe the same Dirac marginal on the one point,
counted once. The test is `zl < zu`; under the paper's assumptions `zl ≤ zu`, so the `else` branch
is exactly the case `zl = zu`. -/
noncomputable def levelMass (μ δ zl zu : ℝ) : Fin 3 → ℝ :=
  if zl < zu then
    ![deltaHat μ δ zl zu / (2 * (μ - zl)),
      1 - deltaHat μ δ zl zu * (zu - zl) / (2 * (zu - μ) * (μ - zl)),
      deltaHat μ δ zl zu / (2 * (zu - μ))]
  else ![1, 0, 0]

end SupermodDRO


