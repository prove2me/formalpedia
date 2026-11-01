-- Prove2me | Definitions.Def_SimpleMenus_natureValue
-- name    : SimpleMenus_natureValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:41.033302+00:00
-- url     : https://prove2.me/theorems/cc16dd67-d4e6-45d0-8a4a-2acee077f210
-- title:
--   Nature's problem at price $p$: $\inf_{F\in\mathcal F}\mathrm{Rev}(\pi,F)/(1-F(p-))$
-- statement:
--   For a mechanism $\pi$ and a price $p$, nature's problem in the proof of Proposition 1 is the right-hand side of (EC.1):
--
--   $$\inf_{F\in\mathcal F}\frac{\mathrm{Rev}(\pi,F)}{1-F(p-)} .$$
--
--   **Formalization Note** The value lies in the extended reals. The infimum runs over the laws with $1-F(p-)=F([p,\infty))>0$; a law with no mass at or above $p$ imposes nothing in (EC.1), where the ratio is multiplied out. The infimum is $+\infty$ if there is no such law.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, proof of Proposition 1, p.ec6 (PDF p.40), display (EC.1)

import Mathlib
import Definitions.Def_SimpleMenus_pay
import Definitions.Def_SimpleMenus_rev
import Definitions.Def_SimpleMenus_ambiguitySet

open MeasureTheory Set

namespace SimpleMenus

/-- Nature's problem at the price `p` in the proof of Proposition 1:
`inf_{F ∈ 𝓕} Rev(π, F) / (1 − F(p−))`, the right-hand side of (EC.1)
(Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, proof of Proposition 1, p.ec6 = PDF p.40).

Formalization Note: the value is in `EReal`, and the infimum runs over the laws with
`1 − F(p−) = F([p, ∞)) > 0`; a law with no mass at or above `p` imposes nothing in (EC.1), where
the ratio is multiplied out. The infimum is `⊤` when there is no such law. -/
noncomputable def natureValue (vbar : ℝ) {K n : ℕ} (phi : Fin K → ℝ → ℝ) (v x : Fin n → ℝ)
    (p : ℝ) : EReal :=
  ⨅ F ∈ ambiguitySet vbar phi, ⨅ (_ : 0 < F (Ici p)),
    ((rev v x F : ℝ) : EReal) / (((F (Ici p)).toReal : ℝ) : EReal)

end SimpleMenus


