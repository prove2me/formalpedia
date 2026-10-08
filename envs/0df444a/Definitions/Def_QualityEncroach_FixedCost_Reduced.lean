-- Prove2me | Definitions.Def_QualityEncroach_FixedCost_Reduced
-- name    : QualityEncroach_FixedCost_Reduced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:59.728992+00:00
-- url     : https://prove2.me/theorems/9641a328-49aa-4014-b139-b8ee6688fa50
-- title:
--   E-Companion, pp. 36–37 — reduced profits, subgame actions, and footnote 2 polynomial
-- statement:
--   The e-Companion gives the manufacturer’s reduced profits after backward induction. With $0<t\le1$ and positive direct sales, it is
--
--   $$\Pi_{\mathrm{Hi}}(k,c,t,u)=\frac14\left(u+\frac{(8-t)c^2}{(8-5t)u}-2c\right)-ku^2.$$
--
--   With $t\ge1$ and positive direct sales, equation (22) gives
--
--   $$\Pi_{\mathrm{Lo}}(k,c,t,u)=\frac{(4t^2-1)u}{4(8t-5)}+\frac{(1-4t)c}{2(8t-5)}+\frac{(8t-1)c^2}{4(8t-5)u}-kt^2u^2.$$
--
--   The module also records the displayed wholesale prices and quantities for each branch and the exact polynomials $h_{11},h_{12}$ in footnote 2, where $h_1(t)=h_{11}(t)+h_{12}(t)\sqrt{20t^2-16t+1}$. These definitions let the subgame and optimization milestones use one common set of formulas.
--
--   **Formalization Note** The profit formulas are used only with positive quality and the branch-specific strict encroachment bounds. Lean's division and square root are total outside those domains, but those values are not economic outcomes.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, pp. 36–37, proof of Claim 3, equation (22), footnote 2

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Game

namespace QualityEncroach.FixedCost
noncomputable section

/-- Interior direct-quantity reply for `0 < t ≤ 1`, p. 36. -/
def qMReplyHi (c t u qR : ℝ) : ℝ := max 0 ((1 - t * qR - c / u) / 2)

/-- Interior retailer reply for `0 < t ≤ 1`, p. 36. -/
def qRHiAt (c w t u : ℝ) : ℝ :=
  (1 + c / u - 2 * w / (t * u)) / (2 * (2 - t))

/-- Optimal wholesale price in the encroaching high-direct-quality branch, p. 36. -/
def wHi (c t u : ℝ) : ℝ := t * u / 2 - c * t ^ 2 / (2 * (8 - 5 * t))

def qRHi (c t u : ℝ) : ℝ := 2 * c / ((8 - 5 * t) * u)
def qMHi (c t u : ℝ) : ℝ :=
  1 / 2 - c * (8 - 3 * t) / (2 * (8 - 5 * t) * u)

/-- Manufacturer's reduced profit on the encroaching branch, proof of Claim 3,
p. 36. Its meaningful domain is `0 < t ≤ 1`, `u > (8-3t)c/(8-5t)`. -/
def PiHi (k c t u : ℝ) : ℝ :=
  (u + (8 - t) * c ^ 2 / ((8 - 5 * t) * u) - 2 * c) / 4 - k * u ^ 2

/-- Interior direct-quantity reply for `1 ≤ t`, p. 36. -/
def qMReplyLo (c u qR : ℝ) : ℝ := max 0 ((1 - qR - c / u) / 2)

/-- Interior retailer reply for `1 ≤ t`, p. 36. -/
def qRLoAt (c w t u : ℝ) : ℝ :=
  1 / 2 + (c - 2 * w) / (2 * (2 * t - 1) * u)

/-- Optimal wholesale price in the encroaching low-direct-quality branch, p. 36. -/
def wLo (c t u : ℝ) : ℝ :=
  ((8 * t ^ 2 - 6 * t + 1) * u - c) / (2 * (8 * t - 5))

def qRLo (c t u : ℝ) : ℝ :=
  2 * c / ((8 * t - 5) * u) + 2 * (t - 1) / (8 * t - 5)
def qMLo (c t u : ℝ) : ℝ :=
  -(8 * t - 3) * c / (2 * (8 * t - 5) * u) + (6 * t - 3) / (2 * (8 * t - 5))

/-- Manufacturer's reduced profit, equation (22), p. 36. Its meaningful
encroaching domain is `1 ≤ t`, `(8t-3)c < (6t-3)u`. -/
def PiLo (k c t u : ℝ) : ℝ :=
  (4 * t ^ 2 - 1) * u / (4 * (8 * t - 5)) +
    (1 - 4 * t) * c / (2 * (8 * t - 5)) +
    (8 * t - 1) * c ^ 2 / (4 * (8 * t - 5) * u) - k * t ^ 2 * u ^ 2

/-- Footnote 2, p. 37: polynomial part of the Hessian numerator. -/
def h11 (t : ℝ) : ℝ :=
  -256000 * t ^ 9 + 1036800 * t ^ 8 - 1600960 * t ^ 7 +
    1345728 * t ^ 6 - 614112 * t ^ 5 + 50896 * t ^ 4 +
    88612 * t ^ 3 - 36540 * t ^ 2 + 4200 * t - 75

/-- Footnote 2, p. 37: coefficient of the square-root part. -/
def h12 (t : ℝ) : ℝ :=
  -3 * (12800 * t ^ 7 - 14720 * t ^ 6 + 3584 * t ^ 5 +
    9616 * t ^ 4 - 13664 * t ^ 3 + 6880 * t ^ 2 - 1200 * t + 25)

/-- Numerator `h₁(t)` of the Hessian determinant at its critical points,
footnote 2, p. 37. -/
def h1 (t : ℝ) : ℝ :=
  h11 t + h12 t * Real.sqrt (20 * t ^ 2 - 16 * t + 1)

end
end QualityEncroach.FixedCost


