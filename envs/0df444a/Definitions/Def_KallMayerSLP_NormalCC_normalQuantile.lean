-- Prove2me | Definitions.Def_KallMayerSLP_NormalCC_normalQuantile
-- name    : KallMayerSLP_NormalCC_normalQuantile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:04.524331+00:00
-- url     : https://prove2.me/theorems/bd47302e-e28d-4d61-a9dd-2647076cfc2a
-- title:
--   Inverse $\Phi^{-1}$ of the standard normal distribution function
-- statement:
--   Let $\Phi$ be the distribution function of the standard normal distribution. For $\alpha\in\mathbb R$ put
--   $$\Phi^{-1}(\alpha)=\inf\{q\in\mathbb R\mid \Phi(q)\ge\alpha\}.$$
--   Since $\Phi$ is a continuous, strictly increasing bijection of $\mathbb R$ onto $(0,1)$, for $0<\alpha<1$ this is the unique $q$ with $\Phi(q)=\alpha$, the quantity $\Phi^{-1}(\alpha)$ appearing in the deterministic equivalents (2.33), (2.35), (2.36).
--
--   **Formalization Note** $\Phi$ is the platform definition `FinancialDerivatives.FD06.standardNormalCDF` ($=\,$`cdf (gaussianReal 0 1)`). For $\alpha\le0$ and $\alpha\ge1$ the infimum is of an unbounded or empty set and Lean returns the junk value $0$; every statement in this mission uses $\Phi^{-1}(\alpha)$ only for $0<\alpha<1$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, used in eqs. (2.33), p.106 (PDF p.116), (2.35)–(2.36), p.108 (PDF p.118); Φ defined p.104 (PDF p.114)

import Mathlib
import Definitions.Def_fd06_standardNormalCDF

namespace KallMayerSLP.NormalCC

/-- **The inverse `Φ⁻¹` of the standard normal distribution function** (Kall & Mayer 2005,
Chapter 2, used in (2.33), p.106, PDF p.116, and (2.35)–(2.36), p.108, PDF p.118). `Φ` is the
standard normal distribution function (p.104), here the platform definition
`FinancialDerivatives.FD06.standardNormalCDF` (`cdf (gaussianReal 0 1)`).

`Φ⁻¹(α) = inf { q ∈ ℝ | Φ(q) ≥ α }`.

**Formalization Note.** `Φ` is a continuous strictly increasing bijection of `ℝ` onto `(0, 1)`,
so for `0 < α < 1` the set is a nonempty closed half-line bounded below and `Φ⁻¹(α)` is the unique
`q` with `Φ(q) = α`. For `α ≤ 0` (set `= ℝ`, unbounded below) and for `α ≥ 1` (empty set) Lean's
`sInf` returns the junk value `0`; every statement using `normalQuantile α` assumes `0 < α < 1`,
which is where the book uses `Φ⁻¹`. -/
noncomputable def normalQuantile (α : ℝ) : ℝ :=
  sInf {q : ℝ | α ≤ FinancialDerivatives.FD06.standardNormalCDF q}

end KallMayerSLP.NormalCC


