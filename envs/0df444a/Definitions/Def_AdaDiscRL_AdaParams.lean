-- Prove2me | Definitions.Def_AdaDiscRL_AdaParams
-- name    : AdaDiscRL_AdaParams
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:01.567051+00:00
-- url     : https://prove2.me/theorems/82140fe4-aedb-4ba7-8bc5-eeb3c5add1e9
-- title:
--   Inputs, confidence terms and bias terms of AdaMB and AdaQL
-- statement:
--   Both algorithms take the number of episodes $K$, a confidence $\delta$, Lipschitz constants $L_r,L_V,L_T$, the dimension $d_{\mathcal S}$, an absolute constant $c$ (AdaMB) and initial estimates $v_0(h)$. With $\iota=\log(2HK^2/\delta)$ and $n=n_h(B)$:
--
--   - **AdaMB:** $\mathrm{Rucb}=\sqrt{2\iota/n}$, $\mathrm{Tucb}=L_V\big(4\sqrt{\iota/n}+c\,n^{-1/d_{\mathcal S}}\big)$ if $d_{\mathcal S}>2$ and $L_V\big(4\sqrt{\iota/n}+c\log K/\sqrt n\big)$ if $d_{\mathcal S}\le2$, $\mathrm{Bias}(B)=4L_r\,\mathrm{diam}(B)+L_V(5L_T+4)\mathrm{diam}(B)$, $\mathrm{Conf}=4L_Vc\sqrt{\iota/n}$ ($d_{\mathcal S}\le2$) or $4L_Vc\sqrt\iota/n^{1/d_{\mathcal S}}$ ($d_{\mathcal S}>2$).
--   - **AdaQL:** $\mathrm{Rucb}=2\sqrt{H\iota/n}$, $\mathrm{Tucb}=2\sqrt{H^3\iota/n}$, $\mathrm{Bias}(B)=2L_V\,\mathrm{diam}(B)$, $\mathrm{Conf}=4\sqrt{H^3\iota/n}$.
--
--   A selected ball is split when $\mathrm{Conf}\le\mathrm{diam}(B)$.
--
--   **Formalization Note** Algorithm 1 line 2 initializes the estimates to $H-h+1$, Lemma 3.2 to $H$; the parameter $v_0(h)$ covers both, and the theorems require $v_0(h)\in[H-h+1,H]$.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, §3.3.1, p.17; §3.3.2, p.17; §3.4, p.19; Algorithm 1, p.13

import Mathlib

namespace AdaDiscRL

/-- **Inputs of Algorithm 1** (arXiv:2110.15843v3, p.13) and of the bonuses (pp.17–19): the number
of episodes `K`, the confidence `δ`, the Lipschitz constants `L_r, L_V, L_T`, the absolute
constant `c` of AdaMB's transition bonus, the dimension `d_S` and the initial estimates
`v₀ h` (`Q̄_h^0 = V̄_h^0`, line 2).

**Formalization Note.** Line 2 prints `H − h + 1`, while Lemma 3.2 and the proof of D.1 use `H`;
the theorems allow any `v₀(h) ∈ [H − h + 1, H]` (paper step `h`). -/
structure AdaParams (H : ℕ) where
  K : ℕ
  δ : ℝ
  Lr : ℝ
  LV : ℝ
  LT : ℝ
  c : ℝ
  dS : ℕ
  v0 : Fin H → ℝ

namespace AdaParams

variable {H : ℕ}

/-- `log(2HK²/δ)`, the logarithmic factor of every bonus. -/
noncomputable def iota (prm : AdaParams H) : ℝ := Real.log (2 * H * (prm.K : ℝ) ^ 2 / prm.δ)

/-- AdaQL reward bonus `Rucb(B) = 2√(H log(2HK²/δ)/n)` (p.17). -/
noncomputable def rucbQL (prm : AdaParams H) (n : ℕ) : ℝ := 2 * Real.sqrt (H * prm.iota / n)

/-- AdaQL transition bonus `Tucb(B) = 2√(H³ log(2HK²/δ)/n)` (p.17). -/
noncomputable def tucbQL (prm : AdaParams H) (n : ℕ) : ℝ := 2 * Real.sqrt ((H : ℝ) ^ 3 * prm.iota / n)

/-- AdaQL bias `Bias(B) = 2 L_V diam(B)` (p.17), as a function of `diam(B)`. -/
noncomputable def biasQL (prm : AdaParams H) (diam : ℝ) : ℝ := 2 * prm.LV * diam

/-- AdaQL splitting confidence `Conf(B) = 4√(H³ log(2HK²/δ)/n)` (§3.4, p.19). -/
noncomputable def confQL (prm : AdaParams H) (n : ℕ) : ℝ := 4 * Real.sqrt ((H : ℝ) ^ 3 * prm.iota / n)

/-- AdaMB reward bonus `Rucb(B) = √(2 log(2HK²/δ)/n)` (p.17). -/
noncomputable def rucbMB (prm : AdaParams H) (n : ℕ) : ℝ := Real.sqrt (2 * prm.iota / n)

/-- AdaMB transition bonus (p.17): `L_V(4√(log(2HK²/δ)/n) + c n^{−1/d_S})` if `d_S > 2`, and
`L_V(4√(log(2HK²/δ)/n) + c log(K)/√n)` if `d_S ≤ 2`. -/
noncomputable def tucbMB (prm : AdaParams H) (n : ℕ) : ℝ :=
  if 2 < prm.dS then prm.LV * (4 * Real.sqrt (prm.iota / n) + prm.c * (n : ℝ) ^ (-(1 / (prm.dS : ℝ))))
  else prm.LV * (4 * Real.sqrt (prm.iota / n) + prm.c * Real.log prm.K / Real.sqrt n)

/-- AdaMB bias `Bias(B) = 4 L_r diam(B) + L_V(5 L_T + 4) diam(B)` (p.17). -/
noncomputable def biasMB (prm : AdaParams H) (diam : ℝ) : ℝ :=
  4 * prm.Lr * diam + prm.LV * (5 * prm.LT + 4) * diam

/-- AdaMB splitting confidence (§3.4, p.19): `4 L_V c √(log(2HK²/δ)/n)` if `d_S ≤ 2` and
`4 L_V c √(log(2HK²/δ)) / n^{1/d_S}` if `d_S > 2`. -/
noncomputable def confMB (prm : AdaParams H) (n : ℕ) : ℝ :=
  if prm.dS ≤ 2 then 4 * prm.LV * prm.c * Real.sqrt (prm.iota / n)
  else 4 * prm.LV * prm.c * Real.sqrt prm.iota / (n : ℝ) ^ (1 / (prm.dS : ℝ))

end AdaParams

end AdaDiscRL


