-- Prove2me | Definitions.Def_UCalibDirichlet_Supplement_pot2
-- name    : UCalibDirichlet_Supplement_pot2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:08:55.132414+00:00
-- url     : https://prove2.me/theorems/4379d774-7d82-4af7-bcbb-788247bdd9bb
-- title:
--   Binary potential $F:[0,1]\to\mathbb R$ read on the simplex $\Delta_2$
-- statement:
--   In the binary case ($K=2$) a forecast is a number $p\in[0,1]$, the probability of label $1$, and a potential is a function $F:[0,1]\to\mathbb R$. Identifying $p$ with the simplex point $q=(1-p,\,p)\in\Delta_2$, the potential on the simplex is
--   $$F_2(q)=F(q_1).$$
--
--   With this identification the binary Bernstein gap of display (60),
--   $$L_F(t)=t\sup_{p\in[0,1]}\Big\{\mathbb E_{S\sim\mathrm{Bin}(t,p)}F(S/t)-F(p)\Big\},$$
--   is the multinomial gap $L_{F_2}(t)$ of display (14) at $K=2$.
--
--   **Formalization Note** Simplex points are vectors $q:\{0,1\}\to\mathbb R$ (labels are $0$-based indices), and $p=q_1$. Only the values of $F$ on $[0,1]$ matter.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), §1.1.3, p.8 (binary case K = 2); App. E.1.1, display (60), p.40

import Mathlib

namespace UCalibDirichlet.Supplement

/-- **A binary potential as a potential on `Δ₂`.** Frongillo, Luo, Mehta & Schneider (manuscript,
STOC 2027 submission), §1.1.3, p.8 ("with `K = 2`") and App. E.1.1, p.40: in the binary case a
forecast is a number `p ∈ [0, 1]`, the probability of label `1`, and a potential is a function
`F : [0, 1] → ℝ`.

`pot2 F q = F(q₁)`: the binary potential `F` read on the simplex point `q = (1 − p, p)`.

**Formalization Note.** Binary forecasts are the points `q : Fin 2 → ℝ` of `stdSimplex ℝ (Fin 2)`
with `p = q 1` (label `1` is `Fin` index `1`, label `0` is index `0`). `F` is a total function on
`ℝ`; only its values on `[0, 1]` enter. With this encoding the binary `L_F` of (60) is the base
`LF (pot2 F)` (the multinomial expectation at `K = 2` is the binomial one). -/
def pot2 (F : ℝ → ℝ) (q : Fin 2 → ℝ) : ℝ := F (q 1)

end UCalibDirichlet.Supplement


