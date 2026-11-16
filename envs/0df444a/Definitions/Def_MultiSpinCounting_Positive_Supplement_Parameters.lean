-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_Supplement_Parameters
-- name    : MultiSpinCounting_Positive_Supplement_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:23:36.88275+00:00
-- url     : https://prove2.me/theorems/bbe34d06-f097-4bc2-af2a-07309fa9d7aa
-- title:
--   Parameters and explicit estimates for sparse random-graph colorings
-- statement:
--   For real $d$, integer palette size $q$, and $\eta\in(0,1)$, the parameters of §5 are
--   $$D=\left\lfloor\frac{d+q}{3}\right\rfloor,\quad\gamma=\frac1{q-D-1},\quad h(x)=(1+x)\log(1+x)-x,$$
--   $$\delta=\frac{q/d-2}{6},\quad r=e^{-d h(\delta)},\quad\lambda_0=\frac{3+\eta/2}{3+\eta},\quad\rho=\frac{1+\lambda_0}{2},$$
--   $$K=200,\quad J=(q-1)\log2-d,\quad y=4dq^K e^{-J/2}.$$
--   The predicate of parameter estimates means exactly the conjunction
--   $$D-3>(1+\delta)d,\quad D<q-1,\quad d(\gamma+\sqrt r)\le\lambda_0<\rho<1,\quad edr^{1/4}\le\tfrac14.$$
--   Lemma B.1 proves these estimates together with $ey\le1/4$; no estimate is supplied as a field of the parameter data. The volume constants are
--   $$C_d=2+d(e-1)+d(e^2-1)/4,\quad C_{\rm vol}=4C_d+4\log d+14.$$
--   The floor is integer-valued; subtractions in inequalities are real. These $D,K,\rho$ are independent of the names in the positive-interaction graph bound.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 23–26, 35–36, (5.10)–(5.17); Lemmas 5.10 and B.1

import Mathlib

noncomputable section

namespace MultiSpinCounting.Positive.Supplement

/-- §5.3, (5.10): floor, kept integer-valued without truncated subtraction. -/
def Dcut (d : ℝ) (q : ℕ) : ℤ := ⌊(d + q) / 3⌋
def gamma5 (d : ℝ) (q : ℕ) : ℝ := 1 / ((q : ℝ) - Dcut d q - 1)
def tailH (x : ℝ) : ℝ := (1 + x) * Real.log (1 + x) - x
def delta5 (d : ℝ) (q : ℕ) : ℝ := ((q : ℝ) / d - 2) / 6
def tailR (d : ℝ) (q : ℕ) : ℝ := Real.exp (-d * tailH (delta5 d q))
def lambda0 (η : ℝ) : ℝ := (3 + η / 2) / (3 + η)
def rho5 (η : ℝ) : ℝ := (1 + lambda0 η) / 2
/-- §5.3.3, (5.16): unrelated to the K of (1.4). -/
def Ksec5 : ℕ := 200
def J5 (d : ℝ) (q : ℕ) : ℝ := ((q : ℝ) - 1) * Real.log 2 - d
def y5 (d : ℝ) (q : ℕ) : ℝ := 4 * d * (q : ℝ) ^ Ksec5 * Real.exp (-J5 d q / 2)

/-- Explicit estimates (5.13)–(5.15); these are proved, not bundled into data. -/
def ParameterEstimates (η d : ℝ) (q : ℕ) : Prop :=
  (1 + delta5 d q) * d < (Dcut d q : ℝ) - 3 ∧
  (Dcut d q : ℝ) < (q : ℝ) - 1 ∧
  d * (gamma5 d q + Real.sqrt (tailR d q)) ≤ lambda0 η ∧
  lambda0 η < rho5 η ∧ rho5 η < 1 ∧
  Real.exp 1 * d * (tailR d q) ^ (1 / 4 : ℝ) ≤ 1 / 4

/-- Constants of Lemma 5.10, p. 26. -/
def Cd (d : ℝ) : ℝ := 2 + d * (Real.exp 1 - 1) + d * (Real.exp 2 - 1) / 4
def Cvol (d : ℝ) : ℝ := 4 * Cd d + 4 * Real.log d + 14

end MultiSpinCounting.Positive.Supplement


