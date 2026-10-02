-- Prove2me | Definitions.Def_MDPFinance_TerminalWealth_BinomialPower
-- name    : MDPFinance_TerminalWealth_BinomialPower
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:52:50.212972+00:00
-- url     : https://prove2.me/theorems/560f15bc-410d-49cc-81e6-e88a30cfdfb7
-- title:
--   The binomial-model optimal fraction, Eq. (4.9)
-- statement:
--   In the binomial model (up factor $u$, down factor $d$, one stock), the one-period power-utility
--   objective is $h(\alpha) := p(1+i+\alpha(u-1-i))^\gamma + (1-p)(1+i+\alpha(d-1-i))^\gamma$; its
--   maximizer on $[\alpha_0,\alpha_1]$ (`binomialAlpha0`, `binomialAlpha1`) is `binomialAlphaStar`, the
--   explicit closed form of Eq. (4.9), with $\delta := (1-\gamma)^{-1}$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 86, PDF 100, unnumbered display and Eq. (4.9)

import Mathlib

namespace MDPFinance.TerminalWealth

/-- The binomial-model one-period power-utility objective (Bäuerle–Rieder, p. 86, PDF 100,
unnumbered display, constant `(1+i)^{-γ}` dropped): `h(α) := p(1+i+α(u-1-i))^γ +
(1-p)(1+i+α(d-1-i))^γ`. -/
noncomputable def binomialObjective (i u down γ p α : ℝ) : ℝ :=
  p * (1 + i + α * (u - 1 - i)) ^ γ + (1 - p) * (1 + i + α * (down - 1 - i)) ^ γ

/-- The optimal fraction invested in the stock in the binomial model, Eq. (4.9) (Bäuerle–Rieder,
p. 86, PDF 100), with `δ := (1-γ)⁻¹`. -/
noncomputable def binomialAlphaStar (i u down γ p : ℝ) : ℝ :=
  let δ := (1 - γ)⁻¹
  (1 + i) / ((1 + i - down) * (u - 1 - i)) *
    (((u - 1 - i) ^ δ * p ^ δ - (1 + i - down) ^ δ * (1 - p) ^ δ) /
      ((u - 1 - i) ^ (δ * γ) * p ^ δ + (1 + i - down) ^ (δ * γ) * (1 - p) ^ δ))

/-- The endpoints of the admissible interval `[α_0,α_1]` for the binomial one-period problem
(Bäuerle–Rieder, p. 86, PDF 100). -/
noncomputable def binomialAlpha0 (i u : ℝ) : ℝ := (1 + i) / (1 + i - u)

noncomputable def binomialAlpha1 (i down : ℝ) : ℝ := (1 + i) / (1 + i - down)

end MDPFinance.TerminalWealth


