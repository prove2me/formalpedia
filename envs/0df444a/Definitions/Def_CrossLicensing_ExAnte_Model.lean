-- Prove2me | Definitions.Def_CrossLicensing_ExAnte_Model
-- name    : CrossLicensing_ExAnte_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T14:38:56.327413+00:00
-- url     : https://prove2.me/theorems/0e182d8f-d4e5-4f59-923f-b5eceb534290
-- title:
--   §3 and proof of Proposition 2 — the quantity market, supplier optimization, and equilibrium innovation levels
-- statement:
--   Two manufacturers invest in quality improvements $T_1,T_2\ge 0$, with unit investment costs $k_iT_i^2$. Cross-licensing effectiveness is $\beta\in[0,1]$; manufacturer 2 has the lower cost coefficient, $49/144<k_2<k_1$. Its product-quality intercepts are $1+T_1+\beta T_2$ and $1+T_2+\beta T_1$. At wholesale price $r\ge0$, the manufacturers compete in nonnegative quantities, with manufacturer $i$ earning $(1+T_i+\beta T_j-q_i-q_j-r)q_i$.
--
--   The model records the quantity equilibrium of display (2), for the paper's ordering $T_2\ge T_1$, and the supplier's revenue $r(q_1+q_2)$. Its optimal revenue is defined by optimizing that revenue over $r\ge0$:
--
--   $$\pi_s^*(\beta,T_1,T_2)=\sup_{r\ge0}r\bigl(q_1(\beta,T_1,T_2,r)+q_2(\beta,T_1,T_2,r)\bigr).$$
--
--   The appendix's printed rational expressions define the interior innovations $T_i^I$, the boundary innovations $T_i^B$, and the threshold $\hat k_2(k_1\mid\beta)$. The named outcome $T_i^*$ equals $T_i^B$ below that threshold and $T_i^I$ otherwise. The model also records the printed supplier-profit expressions $\pi_s^I$ and $\pi_s^B$ for later comparison. These objects isolate the market and investment conventions used in Proposition 4.
--
--   **Formalization Note** The model uses explicit real pairs ordered as $M_1,M_2$, and displayed formula (2) under $T_2\ge T_1$. Nonnegative wholesale prices are the paper's implicit economic domain. The optimal supplier profit is defined from the price choice, not from either printed closed form. The claim that the named innovations are a Nash equilibrium is the target of the series' separate Proposition 2 mission.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), pp. 9–10, (1)–(3); p. A.1 (PDF 33) and p. A.2 (PDF 34), proof of Proposition 2

import Mathlib
import Definitions.Def_CrossLicensing_Innovation_Model

namespace CrossLicensing.ExAnte

noncomputable section

/-- The two quality adjusted intercepts in the inverse demands of Section 3. -/
def quality1 (β T1 T2 : ℝ) : ℝ := 1 + T1 + β * T2
def quality2 (β T1 T2 : ℝ) : ℝ := 1 + T2 + β * T1

/-- The first wholesale price at which the lower quality manufacturer leaves. -/
def r1 (β T1 T2 : ℝ) : ℝ := 1 + T1 * (2 - β) - T2 * (1 - 2 * β)
/-- The wholesale price at which the remaining manufacturer leaves. -/
def r2 (β T1 T2 : ℝ) : ℝ := 1 + T1 * β + T2

/-- Manufacturer 1's equilibrium quantity, display (2), in the paper's
ordering `T₂ ≥ T₁`. -/
def q1 (β T1 T2 r : ℝ) : ℝ :=
  if r ≤ r1 β T1 T2 then
    (1 - r + T1 * (2 - β) + T2 * (-1 + 2 * β)) / 3
  else 0

/-- Manufacturer 2's equilibrium quantity, display (2). -/
def q2 (β T1 T2 r : ℝ) : ℝ :=
  if r ≤ r1 β T1 T2 then
    (1 - r + T1 * (-1 + 2 * β) + T2 * (2 - β)) / 3
  else if r ≤ r2 β T1 T2 then
    (1 - r + β * T1 + T2) / 2
  else 0

/-- The supplier's wholesale revenue, display (3). -/
def supplierProfit (β T1 T2 r : ℝ) : ℝ := r * (q1 β T1 T2 r + q2 β T1 T2 r)

/-- The supplier's optimal value over admissible wholesale prices. On the
standing domain the set of values is nonempty and bounded above; the closed
form is a theorem, not part of this definition. -/
def supplierOpt (β T1 T2 : ℝ) : ℝ :=
  sSup ((fun r : ℝ => supplierProfit β T1 T2 r) '' Set.Ici (0 : ℝ))

/-- Interior duopoly innovation for the firm of cost `ki`, facing a firm of
cost `kj`, from the proof of Proposition 2, page A.1. -/
def interiorT (β ki kj : ℝ) : ℝ :=
  (5 * β - 7) * (-5 * β ^ 2 + 12 * β + 12 * kj - 7) /
    (6 * kj * ((7 - 5 * β) ^ 2 - 144 * ki) +
      (7 - 5 * β) ^ 2 * (β ^ 2 + 6 * ki - 1))

/-- Common denominator of the two boundary-duopoly innovation levels. -/
def boundaryDenom (β k1 : ℝ) : ℝ :=
  (4 * Real.sqrt 3 - 7) * (β - 1) * (β + 1) * (5 * β - 7) -
    48 * (Real.sqrt 3 * β + Real.sqrt 3 - 3) * k1

/-- Inferior manufacturer's boundary-duopoly innovation, page A.1. -/
def boundaryT1 (β k1 : ℝ) : ℝ :=
  -((4 * Real.sqrt 3 - 7) * (β - 1) * (5 * β - 7)) / boundaryDenom β k1

/-- Superior manufacturer's boundary-duopoly innovation, page A.1. -/
def boundaryT2 (β k1 : ℝ) : ℝ :=
  (48 * (2 * Real.sqrt 3 - 3) * k1 -
      (4 * Real.sqrt 3 - 7) * (β - 1) * (5 * β - 7)) / boundaryDenom β k1

/-- The cost threshold separating boundary and interior duopoly, page A.2. -/
def khat2 (k1 β : ℝ) : ℝ :=
  -((4 * Real.sqrt 3 - 5) * (β - 1) * (5 * β - 7) * k1) /
    ((4 * Real.sqrt 3 - 7) * (β - 1) * (5 * β - 7) +
      48 * (3 - 2 * Real.sqrt 3) * k1)

/-- The equilibrium innovation levels named in the proof of Proposition 2,
page A.2. The lower-cost firm is manufacturer 2. -/
def equilibriumT1 (β k1 k2 : ℝ) : ℝ :=
  if k2 < khat2 k1 β then boundaryT1 β k1 else interiorT β k1 k2
def equilibriumT2 (β k1 k2 : ℝ) : ℝ :=
  if k2 < khat2 k1 β then boundaryT2 β k1 else interiorT β k2 k1

/-- Supplier profit after the innovation outcome, determined by an actual
optimization over wholesale prices. -/
def equilibriumProfit (k1 k2 β : ℝ) : ℝ :=
  supplierOpt β (equilibriumT1 β k1 k2) (equilibriumT2 β k1 k2)

/-- The interior-duopoly closed form for supplier profit, page A.1. -/
def piInterior (β k1 k2 : ℝ) : ℝ :=
  216 * (((β - 1) * (5 * β - 7) * k2 +
    k1 * ((β - 1) * (5 * β - 7) - 24 * k2)) ^ 2) /
    (((7 - 5 * β) ^ 2 * (β ^ 2 + 6 * k2 - 1) +
      6 * k1 * ((7 - 5 * β) ^ 2 - 144 * k2)) ^ 2)

/-- The boundary-duopoly closed form for supplier profit, page A.1. -/
def piBoundary (β k1 : ℝ) : ℝ :=
  864 * (β - 1) ^ 2 * k1 ^ 2 / (boundaryDenom β k1) ^ 2

end
end CrossLicensing.ExAnte


