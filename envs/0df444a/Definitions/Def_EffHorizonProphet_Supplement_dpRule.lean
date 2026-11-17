-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_dpRule
-- name    : EffHorizonProphet_Supplement_dpRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:56:24.357254+00:00
-- url     : https://prove2.me/theorems/a1d78704-c74a-492a-8058-5882c84c1d23
-- title:
--   The dynamic-programming stopping rule $\tau_{\mathrm{DP}}$
-- statement:
--   The **dynamic-programming stopping rule** of the law $D$ is
--   $$\tau_{\mathrm{DP}}=\inf\{i\in\{1,\dots,n\}: X_i\ge V_{i+1}\},$$
--   with the values $V$ of $D$; it stops at the first stage whose reward is at least the value of continuing.
--
--   **Formalization Note** Stages are numbered from $0$; if no stage qualifies the rule returns $n$ ("never stop"). For nonnegative rewards the last stage always qualifies because $V_{n+1}=0$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Proposition 17, pp.33–34; Theorem 8, p.11

import Mathlib
import Definitions.Def_EffHorizonProphet_reward
import Definitions.Def_EffHorizonProphet_Supplement_dpValue

open MeasureTheory

namespace EffHorizonProphet.Supplement

open scoped Classical in
/-- The **dynamic-programming stopping rule** `τ_DP := inf{i : X_i ≥ V_{i+1}}` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Proposition 17,
p.33–34; Theorem 8, p.11), with the values `V` of the law `D`.

**Formalization Note** `0`-based: `dpRule γ L D ω` is the least `i < n` with
`reward γ L i ω ≥ dpValue γ L D (i + 1)`, and `n` ("never stop") if there is none. For nonnegative
rewards the last stage always qualifies, since `V_{n+1} = 0`. -/
noncomputable def dpRule {S : ℕ} (γ : ℝ) (L : Fin S → ℕ) (D : Measure ℝ)
    (ω : Fin (∑ s, L s) → ℝ × unitInterval) : ℕ :=
  if h : ∃ i, ∃ hi : i < ∑ s, L s, dpValue γ L D (i + 1) ≤ reward γ L ⟨i, hi⟩ ω then
    Nat.find h
  else ∑ s, L s

end EffHorizonProphet.Supplement


