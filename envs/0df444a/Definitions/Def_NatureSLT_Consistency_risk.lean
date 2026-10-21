-- Prove2me | Definitions.Def_NatureSLT_Consistency_risk
-- name    : NatureSLT_Consistency_risk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:09.02301+00:00
-- url     : https://prove2.me/theorems/d9c9f745-7877-462f-9618-a7bbeff6e2ec
-- title:
--   Risk $R(\alpha)=\int Q(z,\alpha)\,dF(z)$ and empirical risk $R_{\mathrm{emp}}(\alpha)$
-- statement:
--   Let $F$ be a probability measure on a measurable space $Z$ and let $Q(z,\alpha)$, $\alpha \in \Lambda$, be a set of real functions on $Z$ indexed by an arbitrary parameter set $\Lambda$ (the parameters need not be vectors). The **risk functional** of the function $Q(\cdot,\alpha)$ is
--
--   $$R(\alpha) = \int Q(z,\alpha)\,dF(z),$$
--
--   and, for a sample $z_1,\dots,z_\ell$ of $\ell$ points of $Z$, the **empirical risk functional** is
--
--   $$R_{\mathrm{emp}}(\alpha) = \frac{1}{\ell}\sum_{i=1}^{\ell} Q(z_i,\alpha).$$
--
--   These are the two functionals of the learning problem: the risk is to be minimized when $F$ is unknown, and the empirical risk, computed from an i.i.d. sample drawn from $F$, replaces it in the empirical risk minimization (ERM) principle. Every theorem of this mission is stated in terms of them.
--
--   **Formalization Note** The sample is a map $z : \{0,\dots,\ell-1\} \to Z$ (`Fin ℓ → Z`). The risk is the Bochner integral, which equals the book's integral only when $Q(\cdot,\alpha)$ is $F$-integrable; every theorem that uses it assumes integrability (or boundedness and measurability). For $\ell = 0$ the empirical risk is $0$ (Lean's $1/0 = 0$); the book only uses $\ell \ge 1$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 20, Eqs. (1.6) and (1.8)

import Mathlib

open MeasureTheory

namespace NatureSLT.Consistency

/-- The **risk functional** `R(α) = ∫ Q(z, α) dF(z)` (Vapnik 2000, Eq. (1.6), p. 20) of the
function `Q(·, α)` of the set `Q(z, α), α ∈ Λ`, under the probability measure `F` on `Z`.
`Λ` is an arbitrary parameter type (footnote 2, p. 17). The Bochner integral is the book's
integral only when `Q α` is `F`-integrable; every theorem using `risk` assumes that. -/
noncomputable def risk {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) (Q : Λ → Z → ℝ)
    (α : Λ) : ℝ :=
  ∫ z, Q α z ∂F

/-- The **empirical risk functional** `R_emp(α) = (1/ℓ) ∑_{i=1}^ℓ Q(zᵢ, α)` (Eq. (1.8), p. 20)
on the sample `z = (z₁, …, z_ℓ)`, written `z : Fin ℓ → Z` (indices `0, …, ℓ − 1`). For `ℓ = 0`
it is `0` (`1/0 = 0` in Lean); the book only uses `ℓ ≥ 1`. -/
noncomputable def empiricalRisk {Z Λ : Type*} (Q : Λ → Z → ℝ) {ℓ : ℕ} (z : Fin ℓ → Z)
    (α : Λ) : ℝ :=
  (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)

end NatureSLT.Consistency


