-- Prove2me | Definitions.Def_BankLiability_lam
-- name    : BankLiability_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:30.729657+00:00
-- url     : https://prove2.me/theorems/d4e91343-f5a2-44ca-bca6-be31ca5f93dc
-- title:
--   The exponent $\lambda$: positive root of $\sigma^2\lambda(1+\lambda)/2-(r-\delta)\lambda-r=0$
-- statement:
--   For parameters $\sigma>0$, $\delta\ge0$, $r>0$, the exponent $\lambda$ of the model is the positive root of the quadratic equation
--
--   $$\frac{\sigma^2\lambda(1+\lambda)}{2}-(r-\delta)\lambda-r=0 .$$
--
--   Writing the equation as $a\lambda^2+b\lambda-r=0$ with $a=\sigma^2/2$ and $b=\sigma^2/2-(r-\delta)$, the definition is the root
--
--   $$\lambda=\frac{-b+\sqrt{b^2+4ar}}{2a}.$$
--
--   In the model the state price of the asset value falling from $V$ to a boundary $L\le V$ is $(L/V)^\lambda$; $\sigma$ and $\delta$ enter the static model only through $\lambda$.
--
--   **Formalization Note** $\lambda$ is defined by the quadratic formula. That it is positive and the only positive root of the quadratic is the milestone `BankLiability.lambda_root`.
-- source:
--   Sundaresan–Wang, Strategic Bank Liability Structure Under Capital Requirements, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance, §2.2, sentence after eq. (2), p.5

import Mathlib
import Definitions.Def_BankLiability_Params

namespace BankLiability

/-- **The exponent λ: the positive root of σ²λ(1 + λ)/2 − (r − δ)λ − r = 0.**
Sundaresan–Wang, Management Science (2023), doi:10.1287/mnsc.2022.4570, Articles in Advance,
§2.2, sentence after (2), p.5: "λ is the positive solution to the quadratic equation
σ²λ(1 + λ)/2 − (r − δ)λ − r = 0".

Written as a quadratic `a λ² + b λ − r = 0` with `a = σ²/2` and `b = σ²/2 − (r − δ)`, the
definition is the `+` root of the quadratic formula, `λ = (−b + √(b² + 4ar)) / (2a)`.

**Formalization Note.** λ is defined explicitly by the quadratic formula; that it is positive and
the only positive root of the paper's quadratic is the milestone `BankLiability.lambda_root`. In
the static model σ and δ enter only through λ. -/
noncomputable def lam (P : Params) : ℝ :=
  let a := P.sigma ^ 2 / 2
  let b := P.sigma ^ 2 / 2 - (P.r - P.delta)
  (-b + Real.sqrt (b ^ 2 + 4 * a * P.r)) / (2 * a)

end BankLiability


