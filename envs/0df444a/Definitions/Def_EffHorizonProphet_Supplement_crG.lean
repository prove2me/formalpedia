-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_crG
-- name    : EffHorizonProphet_Supplement_crG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:03:45.202209+00:00
-- url     : https://prove2.me/theorems/b20c5a04-25cf-40a5-a792-908676d56bd1
-- title:
--   Worst-case competitive ratio of the general model
-- statement:
--   The **worst-case competitive ratio** of a policy in the general model is
--   $$\mathrm{CR}_n(\tau)=\inf_{D\in\mathcal D}\frac{\mathbb E_D[X_\tau]}{\mathbb E_D[\max_{i\in[n]}X_i]}.$$
--   The policy may choose its rule as a function of the base law; Theorems 18 and 19 restrict this through their hypotheses.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.4; A.7, Eq. (59), p.38

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_Supplement_gamblerG
import Definitions.Def_EffHorizonProphet_Supplement_prophetG

open MeasureTheory

namespace EffHorizonProphet.Supplement

/-- The **worst-case competitive ratio in the general model**
`CR_n(τ) = inf_{D ∈ 𝒟} E_D[X_τ] / E_D[max_i X_i]` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.4; A.7, Eq. (59), p.38).

**Formalization Note** As the base mission's `cr`, with the general scale `Γ`. The rule may depend on
the law (`π : Measure ℝ → Rule`); Theorems 18 and 19 restrict this through their hypotheses. The
infimum is over a nonempty set of nonnegative reals, so the real `⨅` is genuine. -/
noncomputable def crG {S : ℕ} (g : ℕ → ℝ) (L : Fin S → ℕ) (π : Measure ℝ → Rule) : ℝ :=
  ⨅ D : {D : Measure ℝ // IsAdmissible D},
    gamblerG g L D.1 (π D.1) / prophetG g L D.1

end EffHorizonProphet.Supplement


