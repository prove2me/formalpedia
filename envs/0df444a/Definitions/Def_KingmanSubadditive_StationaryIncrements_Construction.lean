-- Prove2me | Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
-- name    : KingmanSubadditive_StationaryIncrements_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:24:17.607128+00:00
-- url     : https://prove2.me/theorems/53e6d6cc-91ea-4a2f-bf02-73791f43d6c1
-- title:
--   The construction of the proof of Theorem 3: the bump ψ, the law of ν, and $y_t = Y_{t+\eta}$ of (1.4.5)
-- statement:
--   These are the objects of the proof of Theorem 3 in Kingman's paper, for a function $\Gamma$ on $(0,\infty)$.
--
--   1. **The bump $\psi$.** A $C^\infty$ function $\psi:\mathbb R\to\mathbb R$ that vanishes outside the interval $(\tfrac14,\tfrac34)$ and satisfies $0\le\psi(x)\le\psi(\tfrac12)=1$ for all $x$.
--   2. **The integer next above $\Gamma(n+\tfrac12)$**, namely $\lfloor\Gamma(n+\tfrac12)\rfloor+1$, the least integer strictly greater than $\Gamma(n+\tfrac12)$.
--   3. **The law $m_\Gamma$ of the $\nu_r$**, which attaches mass $[n(n+1)]^{-1}$ to the integer next above $\Gamma(n+\tfrac12)$ for $n=1,2,\dots$:
--   $$ m_\Gamma=\sum_{n\ge1}\frac{1}{n(n+1)}\,\delta_{\lfloor\Gamma(n+1/2)\rfloor+1}. $$
--   Masses add when several $n$ give the same integer. Since $\sum_{n\ge1}1/(n(n+1))=1$, $m_\Gamma$ is a probability measure on the integers.
--   4. **The process $Y$ of (1.4.5).** For integers $\nu_0,\nu_1,\dots$,
--   $$ Y_t=\nu_n\,\psi[\nu_n(t-n)]\qquad(n\le t<n+1;\ n=0,1,2,\dots). $$
--   5. **The process $y_t=Y_{t+\eta}$** of (1.4.5), a function of time and of the random variables $\eta,\nu_0,\nu_1,\dots$.
--   6. **The random ingredients.** $\eta,\nu_0,\nu_1,\nu_2,\dots$ are independent random variables on $(\Omega,P)$, $\eta$ uniformly distributed on $(0,1)$ and every $\nu_r$ with law $m_\Gamma$.
--
--   The milestone theorems of the mission are statements about this concrete process.
--
--   **Formalization Note** $C^\infty$ means `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (smooth), not the analytic order. In $Y$, $n=\lfloor t\rfloor$ is `Nat.floor`; for $t<0$, a range the paper never uses, the formula reads $\nu_0\psi(\nu_0t)$. Mutual independence of $\eta,\nu_0,\nu_1,\dots$ is stated as two conditions: $\eta$ is independent of the whole sequence $(\nu_r)_{r\ge0}$, and the $\nu_r$ are mutually independent. Together they are equivalent to mutual independence of the family. The uniform law on $(0,1)$ is Lebesgue measure restricted to $(0,1)$.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 888, §1.4, proof of Theorem 3, (1.4.5)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace KingmanSubadditive.StationaryIncrements

/-- **The bump function ψ** of the proof of Theorem 3 (Kingman, *Subadditive ergodic theory*,
Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, §1.4, proof of Theorem 3, p. 888):
a `C^∞` function on `ℝ` which vanishes outside the interval `(1/4, 3/4)` and satisfies
`0 ≤ ψ(x) ≤ ψ(1/2) = 1`.

**Formalization Note.** `C^∞` is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (smooth, the order written
`∞` under `open scoped ContDiff`), not `ContDiff ℝ (⊤ : WithTop ℕ∞)` (analytic). -/
def IsBump (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ x : ℝ, x ∉ Set.Ioo (1 / 4 : ℝ) (3 / 4) → ψ x = 0) ∧
    (∀ x : ℝ, 0 ≤ ψ x ∧ ψ x ≤ ψ (1 / 2)) ∧ ψ (1 / 2) = 1

/-- **The integer next above `Γ(n + 1/2)`** (Kingman 1973, §1.4, proof of Theorem 3, p. 888):
the least integer strictly greater than `Γ(n + 1/2)`, i.e. `⌊Γ(n + 1/2)⌋ + 1`.

**Formalization Note.** `Nat.floor` is used; it agrees with the integer floor because the
construction only uses `n ≥ 1` and `Γ > 0` there. "Next above" is read strictly, which is what
the paper's estimate `P{ν > Γ(n + 1/2)} ≥ …` on p. 889 needs. -/
noncomputable def nextAbove (Γ : ℝ → ℝ) (n : ℕ) : ℕ :=
  ⌊Γ ((n : ℝ) + 1 / 2)⌋₊ + 1

/-- **The common law of the `ν_r`** (Kingman 1973, §1.4, proof of Theorem 3, p. 888): the
distribution on the integers which "attaches mass `[n(n + 1)]⁻¹` to the integer next above
`Γ(n + 1/2)` for `n = 1, 2, ⋯`",
$$ m_\Gamma = \sum_{n \ge 1} \frac{1}{n(n+1)}\, \delta_{\lfloor \Gamma(n+1/2) \rfloor + 1}. $$
When several `n` give the same integer their masses add. Since `∑_{n≥1} 1/(n(n+1)) = 1`, this is a
probability measure on `ℕ`. -/
noncomputable def nuLaw (Γ : ℝ → ℝ) : Measure ℕ :=
  Measure.sum fun n : {n : ℕ // 1 ≤ n} =>
    ENNReal.ofReal (1 / ((n : ℝ) * ((n : ℝ) + 1))) • Measure.dirac (nextAbove Γ n)

/-- **The process `Y` of (1.4.5)** (Kingman 1973, §1.4, proof of Theorem 3, p. 888): for a
sequence `ν = (ν_0, ν_1, …)` of integers,
$$ Y_t = \nu_n\, \psi[\nu_n (t - n)] \qquad (n \le t < n + 1;\ n = 0, 1, 2, \cdots). $$

**Formalization Note.** `n = ⌊t⌋₊`. For `t < 0` (never used by the paper) `⌊t⌋₊ = 0` and the
formula reads `ν_0 ψ(ν_0 t)`. -/
noncomputable def bigY (ψ : ℝ → ℝ) (ν : ℕ → ℕ) (t : ℝ) : ℝ :=
  (ν ⌊t⌋₊ : ℝ) * ψ ((ν ⌊t⌋₊ : ℝ) * (t - (⌊t⌋₊ : ℝ)))

/-- **The process `y_t = Y_{t+η}` of (1.4.5)** (Kingman 1973, §1.4, proof of Theorem 3, p. 888),
as a function of time and of the random variables `η` and `ν_0, ν_1, …` on the sample space. -/
noncomputable def procY {Ω : Type*} (ψ : ℝ → ℝ) (η : Ω → ℝ) (ν : ℕ → Ω → ℕ) (t : ℝ) (ω : Ω) :
    ℝ :=
  bigY ψ (fun r => ν r ω) (t + η ω)

/-- **The random ingredients of the construction** (Kingman 1973, §1.4, proof of Theorem 3,
p. 888): "Let `η, ν₀, ν₁, ν₂, ⋯` be independent random variables, `η` having a uniform
distribution on `(0, 1)`, and the `ν_r` having the same distribution" `m_Γ` (`nuLaw Γ`).

**Formalization Note.** Mutual independence of `η, ν₀, ν₁, …` is encoded as: `η` is independent
of the whole sequence `(ν_r)_{r ≥ 0}` (product σ-algebra on `ℕ → ℕ`), and the `ν_r` are mutually
independent; together these are equivalent to mutual independence of the whole family. The
uniform distribution on `(0, 1)` is Lebesgue measure restricted to `(0, 1)`. -/
structure IsConstruction {Ω : Type*} [MeasurableSpace Ω] (Γ : ℝ → ℝ) (P : Measure Ω)
    (η : Ω → ℝ) (ν : ℕ → Ω → ℕ) : Prop where
  measurable_eta : Measurable η
  measurable_nu : ∀ r, Measurable (ν r)
  law_eta : P.map η = volume.restrict (Set.Ioo (0 : ℝ) 1)
  law_nu : ∀ r, P.map (ν r) = nuLaw Γ
  indep_eta_nu : IndepFun η (fun ω r => ν r ω) P
  iIndep_nu : iIndepFun ν P

end KingmanSubadditive.StationaryIncrements


