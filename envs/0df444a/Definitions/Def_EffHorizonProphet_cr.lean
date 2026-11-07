-- Prove2me | Definitions.Def_EffHorizonProphet_cr
-- name    : EffHorizonProphet_cr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:07.874213+00:00
-- url     : https://prove2.me/theorems/616a109d-7858-4f70-8b26-4652d3c916bb
-- title:
--   The worst-case competitive ratio $\mathrm{CR}_n$
-- statement:
--   The **worst-case competitive ratio** of a policy is
--   $$\mathrm{CR}_n(\tau)=\inf_{D\in\mathcal D}\frac{\mathbb E_D[X_\tau]}{\mathbb E_D[\max_{i\in[n]}X_i]}.$$
--
--   The policy is a map $\pi$ from base laws to rules, so the rule may use the known base distribution, as in the class the introduction names.
--
--   **Formalization Note** The infimum is taken in the reals over a nonempty set of nonnegative numbers. A ratio with denominator $0$ counts as $0$; this occurs only when the first phase is empty.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.4

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_gambler
import Definitions.Def_EffHorizonProphet_prophet

open MeasureTheory

namespace EffHorizonProphet

/-- The **worst-case competitive ratio** `CR_n(τ) = inf_{D ∈ 𝒟} E_D[X_τ] / E_D[max_i X_i]` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…),
Section 3, p.4).

**Formalization Note** The rule may depend on the base distribution (`π : Measure ℝ → Rule`), which
is the class the introduction claims (p.2: "even among single-quantile policies that may choose
their acceptance probability using the known base distribution"). The infimum is over a nonempty
set of nonnegative reals (see the sanity file), so the real `⨅` is genuine. -/
noncomputable def cr {S : ℕ} (γ : ℝ) (L : Fin S → ℕ) (π : Measure ℝ → Rule) : ℝ :=
  ⨅ D : {D : Measure ℝ // IsAdmissible D}, gambler γ L D.1 (π D.1) / prophet γ L D.1

end EffHorizonProphet


