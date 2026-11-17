-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_generalRatio
-- name    : EffHorizonProphet_Supplement_generalRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:01:15.746324+00:00
-- url     : https://prove2.me/theorems/fffb4ad9-2d48-42ef-aa0e-c090514d83a9
-- title:
--   The effective-horizon ratio of Theorems 18 and 19
-- statement:
--   The right-hand side of Theorems 18 and 19 is
--   $$R(\gamma,\lambda)=\sum_{s=1}^{S}\Gamma_{s-1}\exp\Big(-\frac{\Lambda_{s-1}}{C_S}\Big)\Big(1-\exp\Big(-\frac{\lambda_s}{C_S}\Big)\Big).$$
--   Under the effective-horizon calibration, $\exp(-\Lambda_{s-1}/C_S)$ is the asymptotic probability of reaching phase $s$ and $1-\exp(-\lambda_s/C_S)$ that of accepting within it (p.36). With a common decay factor $\tilde\gamma<1$ and $\lambda_s=1/S$ it equals $U(S,\tilde\gamma)$ of Theorems 1 and 6, and $1-1/e$ at $\tilde\gamma=1$ (both checked in the sanity file).
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 18, p.35; Theorem 19, p.36

import Mathlib
import Definitions.Def_EffHorizonProphet_Supplement_cumScale
import Definitions.Def_EffHorizonProphet_Supplement_cumProp
import Definitions.Def_EffHorizonProphet_Supplement_normEffHorizon

namespace EffHorizonProphet.Supplement

/-- The **effective-horizon ratio of the general model**, the right-hand side of Theorems 18 and
19 (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), pp.35–36):
`∑_{s=1}^{S} Γ_{s−1} exp(−Λ_{s−1}/C_S) (1 − exp(−λ_s/C_S))`.

**Formalization Note** `0`-based phases: Lean phase `s` carries `cumScale g s` (`Γ_{s'−1}`),
`cumProp lam s` (`Λ_{s'−1}`) and `lam s` (`λ_{s'}`), for paper phase `s' = s + 1`. With `g ≡ γ̃` and
`lam ≡ 1/S` it equals the base mission's `optRatio S γ̃` (see the sanity file). -/
noncomputable def generalRatio {S : ℕ} (g : ℕ → ℝ) (lam : Fin S → ℝ) : ℝ :=
  ∑ s : Fin S, cumScale g (s : ℕ) *
    Real.exp (-(cumProp lam s / normEffHorizon g lam)) *
    (1 - Real.exp (-(lam s / normEffHorizon g lam)))

end EffHorizonProphet.Supplement


