-- Prove2me | Definitions.Def_TeschlODE_Frobenius_charExponents
-- name    : TeschlODE_Frobenius_charExponents
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:15:10.439553+00:00
-- url     : https://prove2.me/theorems/aeca34a7-71c3-47a2-a02d-0d943f678e5d
-- title:
--   Characteristic exponents α₁,₂ of the indicial equation, Eq. (4.37)
-- statement:
--   For $p_0, q_0 \in \mathbb{C}$ the **characteristic exponents** are
--   $$\alpha_{1,2} = \tfrac12\Big(1 - p_0 \pm \sqrt{(p_0 - 1)^2 - 4 q_0}\Big), \qquad (4.37)$$
--   where $\sqrt{\cdot}$ is the standard branch of the square root, with branch cut along the negative real axis. They are the two roots of the **indicial equation** $\alpha^2 + (p_0 - 1)\alpha + q_0 = 0$ (4.36). Since the standard square root has nonnegative real part, $\operatorname{Re}\alpha_1 \ge \operatorname{Re}\alpha_2$, which is the ordering the book prescribes.
--
--   In Fuchs's theorem $p_0$ and $q_0$ are the leading coefficients of $z p(z)$ and $z^2 q(z)$ at the singular point $0$.
--
--   **Formalization Note.** The pair $(\alpha_1, \alpha_2)$ is returned as `ℂ × ℂ`. The square root is `w ^ (1/2 : ℂ)` (`Complex.cpow`), i.e. $\exp(\tfrac12 \log w)$ with the principal logarithm, which is $0$ at $w = 0$. On the negative real axis the principal root is $i\sqrt{|w|}$; there $\operatorname{Re}\alpha_1 = \operatorname{Re}\alpha_2$ and $\alpha_1 - \alpha_2 \notin \mathbb{N}_0$ with either labelling, so the choice on the cut does not affect any statement.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 118, §4.2, Eqs. (4.36)–(4.37)

import Mathlib

namespace TeschlODE.Frobenius

/-- Teschl (4.37), p. 118: the characteristic exponents
`α₁,₂ = ½ (1 − p₀ ± √((p₀ − 1)² − 4 q₀))`, the roots of the indicial equation (4.36)
`α² + (p₀ − 1) α + q₀ = 0`, with the standard (principal) branch of the square root, branch cut
along the negative real axis. The square root is `Complex.cpow · (1/2)`, whose real part is
`≥ 0`, so the labelling satisfies `Re α₁ ≥ Re α₂` as the book requires. The pair is `(α₁, α₂)`. -/
noncomputable def charExponents (p₀ q₀ : ℂ) : ℂ × ℂ :=
  ((1 - p₀ + ((p₀ - 1) ^ 2 - 4 * q₀) ^ (1 / 2 : ℂ)) / 2,
   (1 - p₀ - ((p₀ - 1) ^ 2 - 4 * q₀) ^ (1 / 2 : ℂ)) / 2)

end TeschlODE.Frobenius


