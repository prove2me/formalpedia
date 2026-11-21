-- Prove2me | Definitions.Def_LL_Burst9MatrixR3_Xi2
-- name    : LL_Burst9MatrixR3_Xi2
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-21T04:46:54.07625+00:00
-- url     : https://prove2.me/theorems/e88d6545-89d1-412c-acce-1cfbaf027274
-- title:
--   Wu's kernel $\Xi_2$ of display 3.22
-- statement:
--   $\Xi_2(p,t)$ is the sum of ten terms, with $P=(s-1)(s'-1)(\kappa_1-1)(\kappa_2-1)(\kappa_3-1)$: the term $\frac{\sigma_0(t)}{5t}\log\frac{1024}{P}$; five terms $\frac{\mathbf 1_I(t)}{5t}\log L$ for $I=[\alpha_2,3],[\alpha_9,\alpha_1],[\alpha_5,\alpha_2],[\alpha_3,\alpha_2],[\alpha_1,\alpha_2]$ with $L=\frac{(t+1)^5}{P},\frac{t+1}{(\kappa_2-1)(\kappa_1-1-t)},\frac{t+1}{(\kappa_3-1)(s'-1-t)},\frac{t+1}{(s-1)(s'-1-t)},\frac{(t+1)^2}{(\kappa_1-1)(\kappa_2-1)}$; and four terms $\frac{\mathbf 1_I(t)}{5t(1-t/s')}\log L$ for $I=[\alpha_7,\alpha_5],[\alpha_5,\alpha_8],[\alpha_6,\alpha_8],[\alpha_8,\alpha_2]$ with $L=\frac{s'^2}{(\kappa_1s'-s'-\kappa_1t)(\kappa_3s'-s'-\kappa_3t)},\frac{s'(s'-1-t)}{\kappa_1s'-s'-\kappa_1t},\frac{s'}{\kappa_2s'-s'-\kappa_2t},s'-1-t$. Endpoint indices are Wu's, the value alpha $p$ $j$ being $\alpha_{j+1}$, and the indicators are those of closed intervals. Real log and division follow the conventions $\log 0=0$, $\log x=\log|x|$ for $x<0$ and $x/0=0$.

import Mathlib
import Definitions.Def_LL_Burst9MatrixR3_Params
import Definitions.Def_LL_Burst9MatrixR3_alpha
import Definitions.Def_LL_Burst9MatrixR3_ind
import Definitions.Def_LL_Burst9MatrixR3_sigma0

namespace LL_Burst9MatrixR3

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def Xi2 (p : Params) (t : ℝ) : ℝ :=
  let P := (p.s - 1) * (p.sp - 1) * (p.k1 - 1) * (p.k2 - 1) * (p.k3 - 1)
  let a := alpha p
  let q := 5 * t * (1 - t / p.sp)
  sigma0 t / (5 * t) * log (1024 / P) +
  ind (a 1) 3 t / (5 * t) * log ((t + 1) ^ 5 / P) +
  ind (a 8) (a 0) t / (5 * t) * log ((t + 1) / ((p.k2 - 1) * (p.k1 - 1 - t))) +
  ind (a 4) (a 1) t / (5 * t) * log ((t + 1) / ((p.k3 - 1) * (p.sp - 1 - t))) +
  ind (a 2) (a 1) t / (5 * t) * log ((t + 1) / ((p.s - 1) * (p.sp - 1 - t))) +
  ind (a 0) (a 1) t / (5 * t) * log ((t + 1) ^ 2 / ((p.k1 - 1) * (p.k2 - 1))) +
  ind (a 6) (a 4) t / q * log (p.sp ^ 2 /
    ((p.k1 * p.sp - p.sp - p.k1 * t) * (p.k3 * p.sp - p.sp - p.k3 * t))) +
  ind (a 4) (a 7) t / q * log (p.sp * (p.sp - 1 - t) / (p.k1 * p.sp - p.sp - p.k1 * t)) +
  ind (a 5) (a 7) t / q * log (p.sp / (p.k2 * p.sp - p.sp - p.k2 * t)) +
  ind (a 7) (a 1) t / q * log (p.sp - 1 - t)

end

end LL_Burst9MatrixR3


