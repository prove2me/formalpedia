-- Prove2me | Definitions.Def_DataTrackComp_Surplus_AppendixC
-- name    : DataTrackComp_Surplus_AppendixC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:30.928287+00:00
-- url     : https://prove2.me/theorems/3b290135-25fe-406e-ba20-cb74fe215f98
-- title:
--   App. C, pp. OA-22–OA-24 — the functions N (C.4), Γ (C.5), J1–J4, Q1, Q2 of the proof of Theorem 2
-- statement:
--   The auxiliary functions of the proof of Theorem 2 (Appendix C, Claims 22 and 23), with $\bar\theta$, $\tilde x$ and $Z$ from the reduced game $\mathbf G(m)$:
--   $$N(x,m)=m^2-4m+20x^2+12mx-10x-\sqrt{2x(2x+m)}\,(1-2x),\qquad(C.4)$$
--   $$\Gamma(x,m)=\tfrac78-\tfrac{m}{144}(27-m)-Z(x,m)-x+\tfrac12x^2+\tfrac12mx\left(1-\bar\theta(x,m)\right)^2,\qquad(C.5)$$
--   $$J_1=2J_3+\sqrt{2x(2x+m)}\,J_4,\qquad J_2=144m\left(2m+6x-\sqrt{2x(2x+m)}\right),$$
--   $$J_3=m^4+3m^3(x-9)+2304x^4+9m^2(24x^2-41x+14)+18mx(84x^2-40x+21),$$
--   $$J_4=27m^2-m^3-2304x^3-18m(44x^2-8x+7),$$
--   $$Q_1(w,z)=17w^7-72w^6z-110w^4z^3-z^2(z^2-21)(z^2-6)(w+2z)+w^5(91z^2+45)+w^3(z^4+216z^2-126)+w^2z^3(4z^2+234),$$
--   $$Q_2(w,z)=-w^2-wz+w^3z-4z^2+4w^2z^2+z^4.$$
--
--   $N(\cdot,m)$ vanishes at the equilibrium price dispersion of the forward-looking setting. $\Gamma$ evaluated there is the lower bound $F(m)$ on the surplus gap $CS^{FL}-CS^M$. The $J_i$ and $Q_i$ turn the system $\{\Gamma=0,N=0\}$ into a polynomial system.
--
--   **Formalization Note.** In (C.4), the square root covers $2x(2x+m)$ only; the factor $(1-2x)$ is outside it, as on the page.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-22 (PDF 57), (C.4); p. OA-23 (PDF 58), (C.5); p. OA-24 (PDF 59), J1–J4, Q1, Q2

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

namespace DataTrackComp.Surplus

/-- (C.4): `N(x,m) = m² − 4m + 20x² + 12mx − 10x − √(2x(2x+m)) (1 − 2x)`. -/
noncomputable def N (x m : ℝ) : ℝ :=
  m ^ 2 - 4 * m + 20 * x ^ 2 + 12 * m * x - 10 * x - Real.sqrt (2 * x * (2 * x + m)) * (1 - 2 * x)

/-- (C.5): `Γ(x,m) = 7/8 − (m/144)(27 − m) − Z(x,m) − x + x²/2 + (1/2) m x (1 − θ̄(x,m))²`. -/
noncomputable def Gam (x m : ℝ) : ℝ :=
  7 / 8 - m / 144 * (27 - m) - Z x m - x + (1 / 2) * x ^ 2 +
    (1 / 2) * m * x * (1 - thetaBar x m) ^ 2

/-- `J3(x,m)`, p. OA-24. -/
def J3 (x m : ℝ) : ℝ :=
  m ^ 4 + 3 * m ^ 3 * (x - 9) + 2304 * x ^ 4 + 9 * m ^ 2 * (24 * x ^ 2 - 41 * x + 14) +
    18 * m * x * (84 * x ^ 2 - 40 * x + 21)

/-- `J4(x,m)`, p. OA-24. -/
def J4 (x m : ℝ) : ℝ := 27 * m ^ 2 - m ^ 3 - 2304 * x ^ 3 - 18 * m * (44 * x ^ 2 - 8 * x + 7)

/-- `J1(x,m) = 2 J3(x,m) + √(2x(2x+m)) J4(x,m)`, p. OA-24. -/
noncomputable def J1 (x m : ℝ) : ℝ := 2 * J3 x m + Real.sqrt (2 * x * (2 * x + m)) * J4 x m

/-- `J2(x,m) = 144 m (2m + 6x − √(2x(2x+m)))`, p. OA-24. -/
noncomputable def J2 (x m : ℝ) : ℝ := 144 * m * (2 * m + 6 * x - Real.sqrt (2 * x * (2 * x + m)))

/-- `Q1(w,z)`, p. OA-24. -/
def Q1 (w z : ℝ) : ℝ :=
  17 * w ^ 7 - 72 * w ^ 6 * z - 110 * w ^ 4 * z ^ 3 - z ^ 2 * (z ^ 2 - 21) * (z ^ 2 - 6) * (w + 2 * z) +
    w ^ 5 * (91 * z ^ 2 + 45) + w ^ 3 * (z ^ 4 + 216 * z ^ 2 - 126) + w ^ 2 * z ^ 3 * (4 * z ^ 2 + 234)

/-- `Q2(w,z)`, p. OA-24. -/
def Q2 (w z : ℝ) : ℝ := -w ^ 2 - w * z + w ^ 3 * z - 4 * z ^ 2 + 4 * w ^ 2 * z ^ 2 + z ^ 4

end DataTrackComp.Surplus


