-- Prove2me | Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_UpperModel
-- name    : RandomCNFDeficiency_LowerBound_Supplement_UpperModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:56:46.68422+00:00
-- url     : https://prove2.me/theorems/c74e1f2f-1e45-4e5d-b0f7-28d443359c49
-- title:
--   The radius $r=n/2-(n/2k)\ln(k/32)$ and the upper-bound event
-- statement:
--   For integers $n,k$ put, as in Equation (33),
--
--   $$r(n,k)=\frac n2-\frac{n}{2k}\ln\frac{k}{32}.$$
--
--   The **upper-bound event** for a CNF $F$ on $n$ variables is that $F$ is unsatisfiable and, simultaneously over every field, $F$ has a polynomial calculus refutation of degree at most $r(n,k)+1$. The failure bound of Equation (43) is $e^{-(1-\ln 2)n}+2^{-n}$, and the explicit right side of Equation (35) with constant $C$ in the $O(n/k)$ term is
--
--   $$\frac n2-\frac{n\ln k}{2k}+C\frac nk.$$
--
--   These quantities state Theorem 4.1 and Lemma 4.6 without rounding the real radius $r$.
--
--   **Formalization Note** Real division by $k=0$ returns $0$ in Lean; every statement using these quantities is asymptotic along sequences with $k\to\infty$.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Theorem 4.1, Equations (33), (35), (43), printed pp. 15, 19, PDF pp. 17, 21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_RandomModel
import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_PCDerivation
import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_Covering
set_option autoImplicit false
universe uUpper

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound

/-- Equation (33): the exact real radius `r = n/2 - (n/(2k)) ln(k/32)`. -/
noncomputable def upperRadius (n k : ℕ) : ℝ :=
  (n : ℝ) / 2 - (n : ℝ) / (2 * (k : ℝ)) * Real.log ((k : ℝ) / 32)

/-- Theorem 4.1's good event: `F` is unsatisfiable and, simultaneously over every field, has a
PC refutation of degree at most `r + 1`. -/
def UpperEvent (n k : ℕ) (F : CNF n) : Prop :=
  ¬ Satisfiable F ∧ AllFieldsEasy.{uUpper} F (upperRadius n k + 1)

/-- The failure bound of Equation (43): `exp(-(1 - ln 2) n) + 2^(-n)`. -/
noncomputable def upperFailureBound (n : ℕ) : ℝ :=
  Real.exp (-(1 - Real.log 2) * (n : ℝ)) + (2 : ℝ)⁻¹ ^ n

/-- The right side of Equation (35) with an explicit constant `C` in the `O(n/k)` term:
`n/2 - n ln k/(2k) + C n/k`. -/
noncomputable def upperAsymptoticBound (C : ℝ) (n k : ℕ) : ℝ :=
  (n : ℝ) / 2 - (n : ℝ) * Real.log (k : ℝ) / (2 * (k : ℝ)) + C * (n : ℝ) / (k : ℝ)

end RandomCNFDeficiency.LowerBound.Supplement


