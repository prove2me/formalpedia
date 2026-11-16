-- Prove2me | Definitions.Def_ManipPotential_Supplement_upperBoundU
-- name    : ManipPotential_Supplement_upperBoundU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:01:28.482195+00:00
-- url     : https://prove2.me/theorems/d0a89be1-fc08-4ab5-8a68-2f0cf9f17e4b
-- title:
--   The bound $U_s(\ell)$ of Theorem 4.6
-- statement:
--   For a scoring vector $s$, the number of voters $n$ and $\ell \in [m-1]$,
--   $$U_s(\ell) := \begin{cases} \dfrac{1}{s_\ell - s_{\ell+1}} - 1 & \text{if } \ell = 1, \\[2ex] \min\left( \dfrac{1}{s_\ell - s_{\ell+1}} - 1,\ \dfrac{(n-1)\bigl(\overline{s}(2) - \underline{s}(\alpha^s_\ell)\bigr) + \frac12}{\overline{s}(\alpha^s_\ell) - s_{\ell+1}} \right) & \text{otherwise,} \end{cases}$$
--   where $\dfrac{1}{s_\ell - s_{\ell+1}} = \infty$ whenever $s_\ell = s_{\ell+1}$.
--
--   This is the term maximized over $\ell$ in the upper bound of Theorem 4.6.
--
--   **Formalization Note** Valued in the extended reals so that the first term is $+\infty$ when $s_\ell = s_{\ell+1}$, as the paper stipulates on p.16, instead of Lean's $1/0 - 1 = -1$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.6, p.15, and the convention on p.16

import Mathlib
import Definitions.Def_ManipPotential_Supplement_topAvg
import Definitions.Def_ManipPotential_Supplement_bottomAvg
import Definitions.Def_ManipPotential_Supplement_alphaIdx

namespace ManipPotential.Supplement

/-- The bound `U_s(ℓ)` of Theorem 4.6 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.6, p.15, and the convention on p.16):
`U_s(1) = 1/(s₁ − s₂) − 1`, and for `ℓ ≥ 2`
`U_s(ℓ) = min( 1/(s_ℓ − s_{ℓ+1}) − 1, ((n−1)(s̄(2) − s̲(α^s_ℓ)) + 1/2) / (s̄(α^s_ℓ) − s_{ℓ+1}) )`,
where `1/(s_ℓ − s_{ℓ+1}) = ∞` whenever `s_ℓ = s_{ℓ+1}`.

**Formalization Note** Valued in `EReal` so that the term `1/(s_ℓ − s_{ℓ+1}) − 1` is `⊤` when
`s_ℓ = s_{ℓ+1}` (p.16), instead of Lean's `1/0 − 1 = −1`. `n` is the number of voters; `ℓ` is
1-based. The overlined `s(·)` is `topAvg`, the underlined one `bottomAvg` (checked on the rendered
page). -/
noncomputable def upperBoundU {m : ℕ} (s : Fin m → ℝ) (n ℓ : ℕ) : EReal :=
  let gap : EReal :=
    if scoreAt s ℓ = scoreAt s (ℓ + 1) then ⊤
    else ((1 / (scoreAt s ℓ - scoreAt s (ℓ + 1)) - 1 : ℝ) : EReal)
  if ℓ = 1 then gap
  else min gap
    (((((n : ℝ) - 1) * (topAvg s 2 - bottomAvg s (alphaIdx s ℓ)) + 1 / 2) /
      (topAvg s (alphaIdx s ℓ) - scoreAt s (ℓ + 1)) : ℝ) : EReal)

end ManipPotential.Supplement


