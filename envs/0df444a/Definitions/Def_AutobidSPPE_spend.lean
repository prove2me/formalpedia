-- Prove2me | Definitions.Def_AutobidSPPE_spend
-- name    : AutobidSPPE_spend
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:52.885863+00:00
-- url     : https://prove2.me/theorems/2e5d0297-52ae-43c1-b648-9a12b3be8114
-- title:
--   Expected spending $s_i(\alpha)=\mathbb E[x_i(\alpha)v_{-i}]$
-- statement:
--   The **expected spending** of bidder $i$ at the multiplier profile $\alpha$ is the expected second-price payment
--   $$
--   s_i(\alpha) = \mathbb E_{v\sim\mathcal D}\Big[x_i(\alpha)\max_{j\ne i}\alpha_j v_j\Big].
--   $$
--   The ex-ante budget constraint of Problem 1.1 is $g_i(\alpha)=s_i(\alpha)-\rho_i\le 0$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §2.2, p.10; Problem 1.1, p.4

import Mathlib
import Definitions.Def_AutobidSPPE_valueLaw
import Definitions.Def_AutobidSPPE_alloc
import Definitions.Def_AutobidSPPE_highestOther
open MeasureTheory

namespace AutobidSPPE

/-- Expected spending `sᵢ(α) = E[xᵢ(α) max_{j≠i} αⱼvⱼ]` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), §2.2, p.10; Problem 1.1, p.4).
The budget constraint of Problem 1.1 is `gᵢ(α) = sᵢ(α) − ρᵢ ≤ 0`. -/
noncomputable def spend {n : ℕ} (vbar : Fin n → ℝ) (tie : TieRule n) (α : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  ∫ v, alloc tie α v i * highestOther α v i ∂(valueLaw vbar)

end AutobidSPPE


