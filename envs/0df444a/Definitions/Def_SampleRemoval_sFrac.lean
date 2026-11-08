-- Prove2me | Definitions.Def_SampleRemoval_sFrac
-- name    : SampleRemoval_sFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:13:36.22858+00:00
-- url     : https://prove2.me/theorems/c271c30d-8bdb-47f0-8db2-702173b34841
-- title:
--   Fractional stability $s_{\mathrm{frac}}=\inf\{n-\|w\|_1:w\in\mathcal W\}$
-- statement:
--   Given observations and a pair $(e,\theta)$ with feasible set $\mathcal W$, the **fractional stability** is
--
--   $$
--   s_{\mathrm{frac}}=\inf\{\,n-\|w\|_1:\ w\in\mathcal W\,\},
--   $$
--
--   the least total weight that must be removed when observations may be removed fractionally. It is a relaxation of the integral stability, $s_{\mathrm{frac}}\le s_{\mathrm{int}}$.
--
--   **Formalization Note** $\|w\|_1$ is written $\sum_i w_i$, which equals it on $[0,1]^n$. The value set is bounded below by $0$, so on a nonempty $\mathcal W$ Lean's real infimum is the paper's. On $\mathcal W=\emptyset$ the paper's infimum is $+\infty$ while Lean's is $0$; every statement of the mission about $s_{\mathrm{frac}}$ assumes or derives that $\mathcal W$ is nonempty.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Definition 2.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_SampleRemoval_feasible

set_option autoImplicit false

namespace SampleRemoval

/-- The fractional stability `s_frac = inf{n − ∥w∥₁ : w ∈ 𝒲}` (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), Definition 2.1, p.3).

**Formalization Note** `∥w∥₁` is written `∑ i, w i`, which equals it because every
`w ∈ 𝒲` lies in `[0, 1]ⁿ`. The value set is bounded below by `0`, so on a nonempty `𝒲`
Mathlib's real `sInf` is the paper's infimum. On `𝒲 = ∅` the paper's infimum is `+∞` while
Lean's `sInf ∅ = 0`; every statement of the mission about `sFrac` assumes `𝒲` nonempty or
derives it. -/
noncomputable def sFrac {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ)
    (θ : ℝ) : ℝ :=
  sInf ((fun w : Fin n → ℝ => (n : ℝ) - ∑ i, w i) '' feasible x y e θ)

end SampleRemoval


