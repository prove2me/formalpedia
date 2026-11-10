-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_Weights
-- name    : EzeunalaJiangKS_Signing_Weights
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:01:00.930051+00:00
-- url     : https://prove2.me/theorems/17b2c5e6-3a7c-4eff-8f44-835b7e29d212
-- title:
--   Cube-root weights, coupling, and parameter choices
-- statement:
--   For real coordinates in the cube define
--   $$\psi(u)=(1-u^2)^{1/3},\quad\Phi(x)=\sum_i\psi(x_i),\quad\eta_x(Z)=40\sum_i\psi(x_i)A_iZA_i.$$
--   The first and second derivatives are the actual real derivatives of $\psi$. The analytic parameter is $\lambda=\sqrt\nu/(100N)$; the allowed interval is $[\sqrt\nu/(200N),\sqrt\nu/(100N)]$. A separate rational variance proxy lies in $[\nu,1.001\nu]$.
--
--   These definitions retain the source's exact analytic values and permitted implementation parameters. Real power is used only on nonnegative bases in valid cube states, with a real exponent $1/3$. Off the cube Mathlib's total real-power convention applies and has no asserted analytic interpretation.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), §3.1, (4)–(6) and rationality footnotes, printed p. 4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_MatrixData

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

def couplingConstant : ℝ := 40
/-- The domain of analytic uses is [-1,1]; Real.rpow is given its usual total extension. -/
def psi (u : ℝ) : ℝ := (1 - u^2) ^ (1 / 3 : ℝ)
def psiPrime (u : ℝ) : ℝ := deriv psi u
def psiSecond (u : ℝ) : ℝ := deriv psiPrime u

def fractionality {N : ℕ} (x : State N) : ℝ := ∑ i, psi (x i)
def eta {N d : ℕ} (A : Fin N → CMat d) (x : State N) (Z : CMat d) : CMat d :=
  couplingConstant • ∑ i, psi (x i) • (A i * Z * A i)

def analyticLambda {N d : ℕ} (A : Fin N → CMat d) : ℝ :=
  Real.sqrt (variance A) / (100 * N)
def allowedLambda {N d : ℕ} (A : Fin N → CMat d) (l : ℝ) : Prop :=
  Real.sqrt (variance A) / (200 * N) ≤ l ∧ l ≤ analyticLambda A
/-- Permitted rational implementation proxy, distinct from the exact norm. -/
def varianceProxy {N d : ℕ} (A : Fin N → CMat d) (v : ℚ) : Prop :=
  variance A ≤ (v : ℝ) ∧ (v : ℝ) ≤ (1001 / 1000 : ℝ) * variance A

end EzeunalaJiangKS.Signing


