-- Prove2me | Definitions.Def_AnalystRanking_Revelation_sigmaDot
-- name    : AnalystRanking_Revelation_sigmaDot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:42:48.420365+00:00
-- url     : https://prove2.me/theorems/a4719e4b-87d0-4112-b743-83d26b18a127
-- title:
--   Interior strategy $(\dot\sigma^h(q),\dot\sigma^l(q))$, (B.34)
-- statement:
--   With $\chi=\rho\gamma(1-\gamma)$, $A=q\{\gamma^2+\chi\}+(1-q)\{(1-\gamma)^2+\chi\}$, $B=q\{(1-\gamma)^2+\chi\}+(1-q)\{\gamma^2+\chi\}$ and $C=\gamma(1-\gamma)-\chi$,
--   $$\dot\sigma^h(q)=\frac{[q\gamma\varphi-(1-q)(1-\gamma)]B-[q(1-\gamma)\varphi-(1-q)\gamma]C}{(\varphi-1)[AB-C^2]},$$
--   $$\dot\sigma^l(q)=1-\frac{[q(1-\gamma)\varphi-(1-q)\gamma]A-[q\gamma\varphi-(1-q)(1-\gamma)]C}{(\varphi-1)[AB-C^2]}$$
--   ((B.34a)–(B.34b), p. 47), where $AB-C^2=(2\gamma-1)^2q(1-q)+\chi>0$. It solves $\Delta U^h_i=\Delta U^l_i=0$ simultaneously.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), proof of Proposition 3, (B.34a)–(B.34b), p. 47

import Mathlib

namespace AnalystRanking.Revelation

/-- **The interior strategy `(σ̇ʰ(q), σ̇ˡ(q))`, (B.34).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), proof of Proposition 3, displays (B.34a)–(B.34b), p. 47:
`σ̇ʰ(q) = ([qγφ − (1 − q)(1 − γ)]B − [q(1 − γ)φ − (1 − q)γ]C) / ((φ − 1)[AB − C²])`,
`σ̇ˡ(q) = 1 − ([q(1 − γ)φ − (1 − q)γ]A − [qγφ − (1 − q)(1 − γ)]C) / ((φ − 1)[AB − C²])`, where
`A ≡ q{γ² + χ} + (1 − q){(1 − γ)² + χ}`, `B ≡ q{(1 − γ)² + χ} + (1 − q){γ² + χ}`,
`C ≡ γ(1 − γ) − χ` and `χ = ργ(1 − γ)`.

**Formalization Note.** Transcribed as printed (the `c_g` of (B.42) is the `χ` of (B.34)).
`AB − C² = (2γ − 1)²q(1 − q) + χ > 0`; statements use it with `φ > 1`. -/
noncomputable def sigmaDot (γ ρ φ q : ℝ) : ℝ × ℝ :=
  let χ := ρ * γ * (1 - γ)
  let A := q * (γ ^ 2 + χ) + (1 - q) * ((1 - γ) ^ 2 + χ)
  let B := q * ((1 - γ) ^ 2 + χ) + (1 - q) * (γ ^ 2 + χ)
  let C := γ * (1 - γ) - χ
  (((q * γ * φ - (1 - q) * (1 - γ)) * B - (q * (1 - γ) * φ - (1 - q) * γ) * C) /
      ((φ - 1) * (A * B - C ^ 2)),
    1 - ((q * (1 - γ) * φ - (1 - q) * γ) * A - (q * γ * φ - (1 - q) * (1 - γ)) * C) /
      ((φ - 1) * (A * B - C ^ 2)))

end AnalystRanking.Revelation


