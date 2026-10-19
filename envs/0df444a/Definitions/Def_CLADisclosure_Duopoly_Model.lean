-- Prove2me | Definitions.Def_CLADisclosure_Duopoly_Model
-- name    : CLADisclosure_Duopoly_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:09.158746+00:00
-- url     : https://prove2.me/theorems/999ea7ec-10cf-40b5-b560-53e9f502f3ae
-- title:
--   §3.1–§3.3 — quality, consumer utility, Bertrand profits, and symmetric disclosure threshold
-- statement:
--   Two firms draw independent qualities from the same distribution on $[0,1]$. Its density $f$ is continuous and strictly positive, and its cumulative distribution $F$ is normalized by $F(1)=1$. For an interior disclosure threshold $\hat q$, consumers assign an undisclosed product the conditional mean $\bar q=E[q\mid q\le\hat q]$. Define
--
--   $$G(x)=\frac{\int_0^x F(q)\,dq}{F(x)},\qquad H(x)=\frac{\int_0^{x-G(x)}F(q)\,dq}{F(x)}.$$
--
--   If a product is undisclosed, its consumer utility at price $p$ is $q-p+g\max\{q-\bar q,0\}-l\max\{\bar q-q,0\}$. A disclosed product gives utility $q-p$. The gross expected utility of nondisclosure averages the former expression over $q\le\hat q$.
--
--   After the two firms choose disclosure, the homogeneous-consumer Bertrand outcome gives a firm with gross utility $u$ facing a rival with $v$ revenue $\max\{u-v,0\}$. Disclosure costs $c$. Each firm's conditional profits average this revenue over the rival's independent quality. A symmetric disclosure threshold satisfies the consumer participation bound and makes each firm's disclosure decision a best response at every quality, given the rival's identical threshold and the resulting consumer belief. Ex ante profit averages the chosen conditional profit over the firm's own quality.
--
--   This model connects the paper's utility equation (1) and game timing to the comparative-statics result. The separate function $L(x)$ is the double integral introduced in the proof of Proposition 2.
--
--   **Formalization Note** All expectations are interval integrals against $f(q)\,dq$; $G$, $H$, and conditional means are only used at positive thresholds. Bertrand margins represent the stated pricing outcome under the paper's participation bound.
-- source:
--   Zhang & Li, Quality Disclosure under Consumer Loss Aversion, SSRN 3544738 (version of 2020-01-20), pp. 9–18, §3.1–§3.3, eq. (1), (2), (6); p. A7, L(x)

import Mathlib

open MeasureTheory intervalIntegral

namespace CLADisclosure.Duopoly

/-- The continuous positive density and its normalized CDF on the quality interval. -/
structure QualityDist (F f : ℝ → ℝ) : Prop where
  cont : ContinuousOn f (Set.Icc 0 1)
  pos : ∀ q ∈ Set.Icc (0 : ℝ) 1, 0 < f q
  cdf : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x = ∫ q in (0 : ℝ)..x, f q
  total : F 1 = 1

/-- The normalized integral of the CDF, p. 11. -/
noncomputable def Gfun (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ q in (0 : ℝ)..x, F q) / F x

/-- The normalized CDF integral up to the nondisclosure mean, p. 11. -/
noncomputable def Hfun (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ q in (0 : ℝ)..(x - Gfun F x), F q) / F x

/-- The conditional mean quality under nondisclosure, p. 12. -/
noncomputable def condMean (F f : ℝ → ℝ) (qh : ℝ) : ℝ :=
  (∫ q in (0 : ℝ)..qh, q * f q) / F qh

/-- Equation (1), gross of the price. -/
def claUtility (g l qbar q : ℝ) : ℝ :=
  q + g * max (q - qbar) 0 - l * max (qbar - q) 0

/-- Expected gross utility of the undisclosed product. -/
noncomputable def nondiscUtility (F f : ℝ → ℝ) (g l qh : ℝ) : ℝ :=
  (∫ q in (0 : ℝ)..qh, claUtility g l (condMean F f qh) q * f q) / F qh

/-- The Bertrand revenue of one firm when consumers value its product at `u` and the rival at `v`. -/
def margin (u v : ℝ) : ℝ := max (u - v) 0

/-- Gross utility offered by the rival under a disclosure threshold. -/
noncomputable def rivalUtility (F f : ℝ → ℝ) (g l qh qb : ℝ) : ℝ :=
  if qb ≤ qh then nondiscUtility F f g l qh else qb

/-- Expected profit from withholding quality when the rival follows the threshold. -/
noncomputable def nondiscProfit (F f : ℝ → ℝ) (g l qh : ℝ) : ℝ :=
  ∫ qb in (0 : ℝ)..1, margin (nondiscUtility F f g l qh)
    (rivalUtility F f g l qh qb) * f qb

/-- Expected profit from disclosing quality `qa`, after disclosure cost. -/
noncomputable def discProfit (F f : ℝ → ℝ) (g l c qh qa : ℝ) : ℝ :=
  (∫ qb in (0 : ℝ)..1, margin qa (rivalUtility F f g l qh qb) * f qb) - c

/-- A symmetric threshold is a best response to the same threshold used by the rival. -/
def IsSymEqThreshold (F f : ℝ → ℝ) (g l c qh : ℝ) : Prop :=
  qh ∈ Set.Ioc (0 : ℝ) 1 ∧
  0 ≤ nondiscUtility F f g l qh ∧
  ∀ qa ∈ Set.Icc (0 : ℝ) 1,
    (qh < qa → nondiscProfit F f g l qh ≤ discProfit F f g l c qh qa) ∧
    (qa ≤ qh → discProfit F f g l c qh qa ≤ nondiscProfit F f g l qh)

/-- The ex ante profit of either symmetric firm. -/
noncomputable def exAnteProfit (F f : ℝ → ℝ) (g l c qh : ℝ) : ℝ :=
  ∫ qa in (0 : ℝ)..1,
    (if qa ≤ qh then nondiscProfit F f g l qh else discProfit F f g l c qh qa) * f qa

/-- The integral called `L(x)` in the proof of Proposition 2, p. A7. -/
noncomputable def Lfun (F f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ qa in x..1, (∫ qb in x..qa, F qb) * f qa

end CLADisclosure.Duopoly


