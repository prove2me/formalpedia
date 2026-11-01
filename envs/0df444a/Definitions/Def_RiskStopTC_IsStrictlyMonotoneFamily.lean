-- Prove2me | Definitions.Def_RiskStopTC_IsStrictlyMonotoneFamily
-- name    : RiskStopTC_IsStrictlyMonotoneFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:23.664843+00:00
-- url     : https://prove2.me/theorems/4c0edafb-fdcc-4db2-b78a-b536ed496c2d
-- title:
--   Strict monotonicity of the one-step mappings $\varrho_{t|\mathcal F_t}$
-- statement:
--   The family $\varrho_t:\mathcal Z_{t+1}\to\mathcal Z_t$, $t=0,\dots,T-1$, is **strictly monotone** (Definition 3.4) if for every $t<T$ and $X,X'\in\mathcal Z_{t+1}$,
--   $$X\prec X'\ \Longrightarrow\ \varrho_t(X)\prec\varrho_t(X'),$$
--   where $X\prec X'$ means $X\preceq X'$ almost surely and $X\neq X'$ as elements of $L^p$ (§2, p.3).
--
--   The conditional expectations $\mathbb E[\,\cdot\,|\mathcal F_t]$ are strictly monotone; the essential supremum is not. The mission uses this property only in the corrected clause (iii) of Theorem 5.6.
--
--   **Formalization Note** $X\prec X'$ is `X ≤ᵐ[P] X' ∧ ¬ X =ᵐ[P] X'` (below almost surely and different as classes), not "strictly below almost everywhere".
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, Definition 3.4, p.7; ≺ defined in §2, p.3

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions

namespace RiskStopTC

open MeasureTheory RiskFunctionals.NestedAVaR

/-- **Strict monotonicity of the one-step mappings.** Pichler, Liu & Shapiro, arXiv:1808.10807v3,
Definition 3.4, p.7: "We say that preference mapping Rt,u is strictly monotone if for any Zt,u,
Z′t,u ∈ Zt,u such that Zt,u ≺ Z′t,u it follows that R(Zt,u) ≺ R(Z′t,u)", where (§2, p.3)
`Z ≺ Z′` means `Z ⪯ Z′` and `Z ≠ Z′`. Applied to every `ϱ t : Z_{t+1} → Z_t`, `t < T`.

**Formalization Note.** `X ≺ X'` is `X ≤ᵐ[P] X' ∧ ¬ X =ᵐ[P] X'`: a.s. below and different as
classes (not "strictly below almost everywhere"). The mission uses this hypothesis only for the
corrected clause (iii) of Theorem 5.6. -/
def IsStrictlyMonotoneFamily {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (P : Measure[mΩ] Ω) (p : ENNReal) (T : ℕ) (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) : Prop :=
  ∀ t < T, ∀ X X', IsLp (ℱ (t + 1)) P p X → IsLp (ℱ (t + 1)) P p X' →
    X ≤ᵐ[P] X' → ¬ X =ᵐ[P] X' → ϱ t X ≤ᵐ[P] ϱ t X' ∧ ¬ ϱ t X =ᵐ[P] ϱ t X'

end RiskStopTC


