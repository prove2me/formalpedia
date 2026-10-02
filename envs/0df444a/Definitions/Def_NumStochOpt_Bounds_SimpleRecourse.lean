-- Prove2me | Definitions.Def_NumStochOpt_Bounds_SimpleRecourse
-- name    : NumStochOpt_Bounds_SimpleRecourse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T18:55:28.544346+00:00
-- url     : https://prove2.me/theorems/4d722c98-bb9c-45d8-bcba-faa85ba2b1bc
-- title:
--   Simple recourse: the costs $Q_j(\chi_j,h_j)$, the matrix $W=[I,-I]$, and the tail probabilities and conditional means of (2.51)
-- statement:
--   In the problem with **simple recourse** (§2.2.5) the recourse matrix is $W=[I,-I]$, where $I$ is the $m_2\times m_2$ identity, the recourse decision is $y=[y^+,y^-]$ and the cost is $q=[q^+,q^-]$.
--
--   1. The $j$-th **simple-recourse cost** (the closed form (2.49) of the optimal value of the one-row problem (2.47), as written on p. 53) is
--   $$
--   Q_j(\chi_j,h_j)=\begin{cases} q_j^+(h_j-\chi_j) & \text{if } h_j\ge\chi_j,\\ q_j^-(\chi_j-h_j) & \text{if } h_j<\chi_j.\end{cases}
--   $$
--   2. The matrix $W=[I,-I]$, with the $y^+$ block first.
--   3. For a real random variable $h_j$ on $(\Omega,P)$ and a threshold $\chi_j$, the probabilities of (2.51),
--   $$
--   p_j^+(\chi_j)=P\{h_j\ge\chi_j\},\qquad p_j^-(\chi_j)=P\{h_j<\chi_j\},
--   $$
--   and the conditional means
--   $$
--   h_j^+(\chi_j)=E\{h_j\mid h_j\ge\chi_j\}=\frac{1}{p_j^+(\chi_j)}\int_{\{h_j\ge\chi_j\}}h_j\,dP,\qquad h_j^-(\chi_j)=E\{h_j\mid h_j<\chi_j\}=\frac{1}{p_j^-(\chi_j)}\int_{\{h_j<\chi_j\}}h_j\,dP .
--   $$
--
--   These are the ingredients of the exact formula (2.51) for the expected simple-recourse cost and of the bounds (2.55)–(2.56).
--
--   **Formalization Note** When $p_j^\pm(\chi_j)=0$ the conditional mean is undefined in the book; Lean's division returns $0$, and in (2.51) it is always multiplied by $p_j^\pm(\chi_j)=0$, so the formula is unaffected. That $Q_j$ is the optimal value of (2.47) is not built into this definition: it is the separate theorem for (2.48)–(2.49).
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, p. 52, W = [I,-I] and (2.46)-(2.47); p. 53, Q_j and Eq. (2.51)

import Mathlib

open MeasureTheory

namespace NumStochOpt.Bounds

/-- The `j`-th simple-recourse cost `Q_j(χ_j, h_j)` of §2.2.5, p. 53 (the closed form (2.49) of
the optimal value of the one-row problem (2.47)): `q⁺(h − χ)` if `h ≥ χ`, and `q⁻(χ − h)` if
`h < χ`. -/
noncomputable def simpleRecourseCost (qp qm χ h : ℝ) : ℝ :=
  if χ ≤ h then qp * (h - χ) else qm * (χ - h)

/-- The simple-recourse matrix `W = [I, −I]` of §2.2.5, p. 52, with columns indexed by
`ι ⊕ ι` (first the `y⁺` block, then the `y⁻` block). -/
def simpleRecourseMatrix (ι : Type*) [DecidableEq ι] : Matrix ι (ι ⊕ ι) ℝ :=
  Matrix.fromCols (1 : Matrix ι ι ℝ) (-1 : Matrix ι ι ℝ)

/-- The probability `p⁺_j(χ) = P{h_j(ω) ≥ χ}` of (2.51), p. 53, as a real number. -/
noncomputable def probAbove {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → ℝ)
    (χ : ℝ) : ℝ :=
  (P {ω | χ ≤ h ω}).toReal

/-- The probability `p⁻_j(χ) = P{h_j(ω) < χ}` of (2.51), p. 53, as a real number. -/
noncomputable def probBelow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → ℝ)
    (χ : ℝ) : ℝ :=
  (P {ω | h ω < χ}).toReal

/-- The conditional expectation `h⁺_j(χ) = E{h_j(ω) | h_j(ω) ≥ χ}` of (2.51), p. 53:
`(∫_{h ≥ χ} h dP) / P{h ≥ χ}`. When `P{h ≥ χ} = 0` Lean's division returns `0`. -/
noncomputable def condMeanAbove {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → ℝ)
    (χ : ℝ) : ℝ :=
  (∫ ω in {ω | χ ≤ h ω}, h ω ∂P) / probAbove P h χ

/-- The conditional expectation `h⁻_j(χ) = E{h_j(ω) | h_j(ω) < χ}` of (2.51), p. 53:
`(∫_{h < χ} h dP) / P{h < χ}`. When `P{h < χ} = 0` Lean's division returns `0`. -/
noncomputable def condMeanBelow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → ℝ)
    (χ : ℝ) : ℝ :=
  (∫ ω in {ω | h ω < χ}, h ω ∂P) / probBelow P h χ

end NumStochOpt.Bounds


