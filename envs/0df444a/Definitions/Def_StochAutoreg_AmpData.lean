-- Prove2me | Definitions.Def_StochAutoreg_AmpData
-- name    : StochAutoreg_AmpData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:15:40.789413+00:00
-- url     : https://prove2.me/theorems/258b14d0-baa5-470e-8fa5-cd8939c7d5d6
-- title:
--   The data of (7.1)
-- statement:
--   For $J\in\mathbb N$ and $\varepsilon>0$, the numbers $h_\varepsilon,t_G,t_H$ carry the data of (7.1) when $h_\varepsilon\in(0,1/4)$ solves $\mathrm{KL}(1/2+h_\varepsilon\|1/2)=\varepsilon$, $t_G,t_H$ are positive, and
--
--   $$F_J(t_G)=\tfrac12+8\sqrt\varepsilon,\quad F_J(t_H)=\tfrac12+h_\varepsilon,\quad \mathrm{KL}(\tfrac12\pm t_G\|\tfrac12),\ \mathrm{KL}(\tfrac12\pm t_H\|\tfrac12)\le\varepsilon/100.$$
--
--   **Formalization Note** $t_G,t_H<1/2$ is written out; it makes each weak coin a probability, which the paper leaves to small $\varepsilon$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Eq. (7.1), pp.14–15

import Mathlib
import Definitions.Def_StochAutoreg_majF
import Definitions.Def_StochAutoreg_klBernE

namespace StochAutoreg

/-- The data of (7.1) at accuracy `ε`: `h = h_ε ∈ (0, 1/4)` solves `KL(1/2 + h‖1/2) = ε`, and the positive `t_G, t_H`
satisfy `F_J(t_G) = 1/2 + 8√ε`, `F_J(t_H) = 1/2 + h_ε`, `KL(1/2 ± t_G‖1/2), KL(1/2 ± t_H‖1/2) ≤ ε/100`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Eq. (7.1), pp.14–15.

**Formalization Note.** `t_G, t_H < 1/2` is written out: it makes each weak coin a probability, which the paper
leaves to "`ε` small". -/
def AmpData (J : ℕ) (ε h tG tH : ℝ) : Prop :=
  0 < h ∧ h < 1 / 4 ∧ klBernE (1 / 2 + h) (1 / 2) = ENNReal.ofReal ε ∧
  0 < tG ∧ tG < 1 / 2 ∧ 0 < tH ∧ tH < 1 / 2 ∧
  majF J tG = 1 / 2 + 8 * Real.sqrt ε ∧ majF J tH = 1 / 2 + h ∧
  klBernE (1 / 2 + tG) (1 / 2) ≤ ENNReal.ofReal (ε / 100) ∧
  klBernE (1 / 2 - tG) (1 / 2) ≤ ENNReal.ofReal (ε / 100) ∧
  klBernE (1 / 2 + tH) (1 / 2) ≤ ENNReal.ofReal (ε / 100) ∧
  klBernE (1 / 2 - tH) (1 / 2) ≤ ENNReal.ofReal (ε / 100)

end StochAutoreg


