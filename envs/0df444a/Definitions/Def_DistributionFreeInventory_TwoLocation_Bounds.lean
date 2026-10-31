-- Prove2me | Definitions.Def_DistributionFreeInventory_TwoLocation_Bounds
-- name    : DistributionFreeInventory_TwoLocation_Bounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:29:58.014359+00:00
-- url     : https://prove2.me/theorems/e0920e0b-0fc0-43fd-939a-0e507344753e
-- title:
--   Bivariate shortage, Phi, Condition 1 and the exact cost bound
-- statement:
--   Write $a=m_1-y_1$, $b=m_2-y_2$, $A=a^2+\sigma_1^2$, $B=b^2+\sigma_2^2$, and $T=ab+\rho\sigma_1\sigma_2$. Define
--   $$H_\zeta(y,d)=(d_1-y_1)^++(d_2-y_2)^++\zeta(d_1+d_2-y_1-y_2)^+,$$
--   $$\Phi(y;\nu)=\sqrt{\frac{A+B+(\nu-1)T}{\nu+1}},\qquad \nu=\frac{3\zeta+1}{\zeta+1}.$$
--   For $F=\Phi(y;\nu)$, the five coefficients are
--   $$\alpha_1=\frac{(b+\nu a)/F-(B+\nu T)/F^2}{2(\nu^2-1)},\quad
--   \alpha_2=\frac{A/F^2-1}{\nu^2-1},$$
--   $$\alpha_3=\frac{(A+B)/F^2-2}{2(\nu^2-1)}+\frac{a/F-b/F}{2(\nu+1)},$$
--   $$\alpha_4=\frac{\frac{2-\nu}{\nu-1}(1-A/F^2)+\frac1{\nu-1}(\nu^2-B/F^2)+(b+\nu a)/F}{2(\nu^2-1)},$$
--   $$\alpha_5=\frac{A/F^2-B/F^2}{2(\nu^2-1)}+\frac{a/F-b/F}{2(\nu+1)}.$$
--   Condition 1 requires $\zeta>0$, $F>0$, and $\max(0,\alpha_1,\alpha_5)\le\min(\alpha_2,\alpha_3,\alpha_4)$. Positivity of $F$ states the domain of the printed quotients; it does not restrict the unconditional bounds.
--
--   The shortage bound is $(\zeta+1)(a+b)/2+(\zeta+1)\Phi(y;\nu)$. The two-location shipment matrix has diagonal $s_0$ and off-diagonal $s$. The expected original recourse cost is its nonnegative extended integral, embedded into extended reals, and worst cost is its supremum over $\mathcal F$. The finite comparison value is
--   $$B_C=s_0(m_1+m_2)-\tfrac12(p-h-s_0)(y_1+y_2-m_1-m_2)+(p+h-s_0)\Phi\!\left(y;\frac{3(p+h-s)+s-s_0}{p+h-s_0}\right).$$
--   The finite right side keeps its sign; it is not clipped to a positive part. No equality between unrestricted recourse and the shortage formula is imposed.
-- source:
--   Govindarajan, Sinha & Uichanco, Distribution-Free Inventory Risk Pooling in a Multilocation Newsvendor, DOI 10.1287/mnsc.2020.3719, held source.pdf, (UDFL-2), equation (8), Condition 1, equations (9)–(10), printed pp. 12, 14–15 (PDF 12, 14–15)

import Definitions.Def_DistributionFreeInventory_TwoLocation_Flow
import Definitions.Def_DistributionFreeInventory_TwoLocation_Moments
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace DistributionFreeInventory.TwoLocation

/-- The loss in (UDFL-2), on the whole real plane. -/
def shortage (zeta : ℝ) (y d : Demand) : ℝ :=
  max (d 0 - y 0) 0 + max (d 1 - y 1) 0 +
    zeta * max (d 0 + d 1 - y 0 - y 1) 0

def phi (M : Moments) (y : Demand) (nu : ℝ) : ℝ :=
  Real.sqrt (((M.mean 0 - y 0)^2 + M.sigma 0^2 +
    (M.mean 1 - y 1)^2 + M.sigma 1^2 +
    (nu - 1) * ((M.mean 0 - y 0) * (M.mean 1 - y 1) +
      M.rho * M.sigma 0 * M.sigma 1)) / (nu + 1))

/-- The five coefficients in Condition 1, in their printed order. -/
def alphas (M : Moments) (y : Demand) (nu : ℝ) : Fin 5 → ℝ :=
  let a := M.mean 0 - y 0
  let b := M.mean 1 - y 1
  let A := a^2 + M.sigma 0^2
  let B := b^2 + M.sigma 1^2
  let T := a*b + M.rho * M.sigma 0 * M.sigma 1
  let F := phi M y nu
  ![1 / (2 * (nu^2 - 1)) * ((b + nu*a) / F - (B + nu*T) / F^2),
    1 / (nu^2 - 1) * (A / F^2 - 1),
    1 / (2 * (nu^2 - 1)) * ((A+B) / F^2 - 2) +
      1 / (2 * (nu+1)) * (a/F - b/F),
    1 / (2 * (nu^2 - 1)) * ((2-nu)/(nu-1) * (1-A/F^2) +
      1/(nu-1) * (nu^2-B/F^2) + (b+nu*a)/F),
    1 / (2 * (nu^2 - 1)) * (A/F^2 - B/F^2) +
      1 / (2 * (nu+1)) * (a/F - b/F)]

/-- The nonempty interval condition, only where its displayed quotients are defined. -/
def conditionOne (M : Moments) (y : Demand) (zeta : ℝ) : Prop :=
  let nu := (3*zeta+1)/(zeta+1)
  let a := alphas M y nu
  0 < zeta ∧ 0 < phi M y nu ∧ max (max 0 (a 0)) (a 4) ≤ min (min (a 1) (a 2)) (a 3)

def shortageBound (M : Moments) (y : Demand) (zeta : ℝ) : ℝ :=
  (1/2 : ℝ) * (zeta+1) * (M.mean 0 - y 0 + M.mean 1 - y 1) +
    (zeta+1) * phi M y ((3*zeta+1)/(zeta+1))

def twoMatrix (s0 s : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then s0 else s

/-- Genuine nonnegative extended expectation of the original recourse (2). -/
def expectedCost (h p s0 s : ℝ) (y : Demand) (μ : Measure Demand) : EReal :=
  (∫⁻ d, recourse h p (twoMatrix s0 s) (fun i => y i) (fun i => d i) ∂μ : ℝ≥0∞)

def worstCost (M : Moments) (h p s0 s : ℝ) (y : Demand) : EReal :=
  ⨆ μ ∈ ambiguity M, expectedCost h p s0 s y μ

/-- Exact finite right side of (10); no positive-part clipping. -/
def costBound (M : Moments) (h p s0 s : ℝ) (y : Demand) : ℝ :=
  s0 * (M.mean 0 + M.mean 1) -
    (1/2 : ℝ) * (p-h-s0) * (y 0 + y 1 - M.mean 0 - M.mean 1) +
    (p+h-s0) * phi M y ((3*(p+h-s)+s-s0)/(p+h-s0))

end DistributionFreeInventory.TwoLocation


