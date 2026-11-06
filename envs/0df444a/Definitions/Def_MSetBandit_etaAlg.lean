-- Prove2me | Definitions.Def_MSetBandit_etaAlg
-- name    : MSetBandit_etaAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:01.287507+00:00
-- url     : https://prove2.me/theorems/25e42076-aaed-40fe-b37a-b30f19e0e05b
-- title:
--   Learning rate $\eta$ of Algorithm 1
-- statement:
--   For a horizon $T$ and a confidence parameter $\delta$, Algorithm 1 uses the learning rate
--   $$
--   \eta=\min\left\{\frac1{256d},\ \sqrt{\frac{\log(12K/\delta)}{320\,dT}}\right\},\qquad K=\binom dm,
--   $$
--   with the natural logarithm. The algorithm then sets $\lambda=128\eta d$ and $\varepsilon_{\mathrm p}=\eta/T$.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Algorithm 1, lines 1–2, p.12

import Mathlib

namespace MSetBandit

/-- **The learning rate of Algorithm 1.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Algorithm 1, line 1, p.12:
`η ← min{ 1/(256d), √( log(12K/δ) / (320 d T) ) }`, `K = C(d, m)`.

**Formalization Note.** Natural logarithm; `K` is the real number `Nat.choose d m`. -/
noncomputable def etaAlg (d m T : ℕ) (δ : ℝ) : ℝ :=
  min (1 / (256 * (d : ℝ)))
    (Real.sqrt (Real.log (12 * (Nat.choose d m : ℝ) / δ) / (320 * (d : ℝ) * (T : ℝ))))

end MSetBandit


