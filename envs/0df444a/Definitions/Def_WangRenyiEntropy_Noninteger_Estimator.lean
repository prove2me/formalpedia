-- Prove2me | Definitions.Def_WangRenyiEntropy_Noninteger_Estimator
-- name    : WangRenyiEntropy_Noninteger_Estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:14.275867+00:00
-- url     : https://prove2.me/theorems/5356398c-2597-4bb0-bdc8-8215dead41f7
-- title:
--   The exact two-batch estimator (20)–(22), clipping, and constants
-- statement:
--   Put $L=\log(ed)$, $J=\lceil4\alpha\rceil+3$, and $K=\max\{\lfloor L/(32\log2)\rfloor,1\}$. For a polynomial $Q(x)=\sum_j a_jx^j$ chosen independently of the unknown law and samples, let $x^{\underline j}=\prod_{\ell=0}^{j-1}(x-\ell)$ and $\binom\alpha j=\alpha^{\underline j}/j!$. The exact scalar estimates are
--   $$L_n(x)=(40L/n)^\alpha\mathbf1_{x\le80L}\sum_{j=0}^K\frac{a_jx^{\underline j}}{(40L)^j},$$
--   $$H_n(x,y)=n^{-\alpha}\sum_{j=0}^J\binom\alpha j\sum_{r=0}^j\binom jr(-1)^{j-r}y^{\alpha-r}x^{\underline r}.$$
--   The coordinate estimate uses $L_n(X)$ when $Y\le10L$ and $H_n(X,Y)$ otherwise. Sum these coordinates to obtain $\widehat F$. Clip to $I_\alpha=[1,d^{1-\alpha}]$ for $\alpha<1$, and $I_\alpha=[d^{1-\alpha},1]$ for $\alpha>1$, then set
--   $$\widehat H=\frac{\log(\operatorname{clip}_{I_\alpha}(\widehat F))}{1-\alpha}.$$
--
--   For the uniform constant $c$ of Lemma 2.2, define $C_\alpha=c(256J)^{32J}$ and $\mathcal C=24C_\alpha^4/\min\{1,|1-\alpha|^2\}$. The budget is exactly the ceiling from printed page 17: $\mathcal C^{1/(2\alpha)}d^{\max\{1,1/\alpha\}}/(\varepsilon^{1/\alpha}L)+\mathcal C\mathbf1_{\alpha>1/2}B_\alpha$. Actual scalar and two-batch Poisson laws supply the expectations and variance. The zero-power convention is the paper's $0^0=1$, $0^t=0$ for $t\ne0$; the negative powers are used only in the positive large-count branch. No formula accesses $p$ except through observations.
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 12,13,17 / PDF 14, 15, 19, §4.1, Eqs. (20)–(22), proof of Theorem 4.1

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_SamplingExperiment
import Definitions.Def_WangRenyiEntropy_Noninteger_Approximation

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

namespace WangRenyiEntropy.Noninteger

/-- Printed p.12 / PDF p.14: exact cutoffs, independent of p and the observations. -/
def logScale (d : ℕ) : ℝ := Real.log (Real.exp 1 * d)
def taylorDegree (α : ℝ) : ℕ := Nat.ceil (4 * α) + 3
def approximationDegree (d : ℕ) : ℕ := max (Nat.floor (logScale d / (32 * Real.log 2))) 1

/-- Real polynomial falling factorial; no truncated natural subtraction. -/
def falling (x : ℝ) (j : ℕ) : ℝ := ∏ l ∈ Finset.range j, (x - (l : ℝ))
def realBinomial (α : ℝ) (j : ℕ) : ℝ := falling α j / (j.factorial : ℝ)

/-- Eq. (21), including the cutoff on X. -/
def smallEstimate (α n : ℝ) (d : ℕ) (Q : Polynomial ℝ) (x : ℕ) : ℝ :=
  if (x : ℝ) ≤ 80 * logScale d then
    Real.rpow (40 * logScale d / n) α *
      ∑ j ∈ Finset.range (approximationDegree d + 1),
        Q.coeff j * falling x j / (40 * logScale d) ^ j
  else 0

/-- Eq. (22). Real.rpow has 0^0=1 and 0^t=0 for t≠0, as on printed p.13.
Only Y>10L enters this function in the actual estimator. -/
def largeEstimate (α n : ℝ) (x y : ℕ) : ℝ :=
  Real.rpow n (-α) * ∑ j ∈ Finset.range (taylorDegree α + 1),
    realBinomial α j * ∑ r ∈ Finset.range (j + 1),
      (j.choose r : ℝ) * (-1 : ℝ) ^ (j - r) * Real.rpow y (α - r) * falling x r

/-- Eq. (20), coordinate summand: branch before evaluating negative powers. -/
def coordinateEstimate (α n : ℝ) (d : ℕ) (Q : Polynomial ℝ) (xy : ℕ × ℕ) : ℝ :=
  if (xy.2 : ℝ) ≤ 10 * logScale d then smallEstimate α n d Q xy.1
  else largeEstimate α n xy.1 xy.2

/-- The UNCLIPPED power-sum estimator in Eq. (20). -/
def powerEstimate (α n : ℝ) (d : ℕ) (Q : Polynomial ℝ)
    (xy : (Fin d → ℕ) × (Fin d → ℕ)) : ℝ :=
  ∑ i, coordinateEstimate α n d Q (xy.1 i, xy.2 i)

/-- Endpoints of Iα, with d≥1 in all uses. -/
def clipLower (α : ℝ) (d : ℕ) : ℝ := if α < 1 then 1 else Real.rpow d (1 - α)
def clipUpper (α : ℝ) (d : ℕ) : ℝ := if α < 1 then Real.rpow d (1 - α) else 1

def clippedPowerEstimate (α n : ℝ) (d : ℕ) (Q : Polynomial ℝ)
    (xy : (Fin d → ℕ) × (Fin d → ℕ)) : ℝ :=
  max (clipLower α d) (min (clipUpper α d) (powerEstimate α n d Q xy))

/-- Exactly the entropy estimator in Eq. (20); Q is selected independently of p. -/
def entropyEstimate (α n : ℝ) (d : ℕ) (Q : Polynomial ℝ)
    (xy : (Fin d → ℕ) × (Fin d → ℕ)) : ℝ :=
  Real.log (clippedPowerEstimate α n d Q xy) / (1 - α)

/-- Lemma 4.2's Cα, from any ONE uniform approximation constant of Lemma 2.2. -/
def estimatorConstant (α c : ℝ) : ℝ :=
  c * (256 * (taylorDegree α : ℝ)) ^ (32 * taylorDegree α)

/-- Printed p.17 / PDF p.19; the power 1/(2α) affects only the first term. -/
def successConstant (α c : ℝ) : ℝ :=
  24 * (estimatorConstant α c) ^ 4 / min 1 (|1 - α| ^ 2)

def upperBudget (α c : ℝ) (d : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil (Real.rpow (successConstant α c) (1 / (2 * α)) *
      Real.rpow d (max 1 (1 / α)) / (Real.rpow ε (1 / α) * logScale d) +
    successConstant α c * (if 1 / 2 < α then rateB α d ε else 0))

/-- The actual independent scalar counts used in Lemma 4.2. -/
def coordinateLaw (n p : ℝ) : Measure (ℕ × ℕ) :=
  (poissonMeasure (Real.toNNReal (n * p))).prod (poissonMeasure (Real.toNNReal (n * p)))

/-- Ordinary real variance; theorem conclusions also establish square integrability. -/
def estimatorVariance {S : Type} [MeasurableSpace S] (μ : Measure S) (f : S → ℝ) : ℝ :=
  ∫ z, (f z - ∫ w, f w ∂μ) ^ 2 ∂μ

end WangRenyiEntropy.Noninteger


