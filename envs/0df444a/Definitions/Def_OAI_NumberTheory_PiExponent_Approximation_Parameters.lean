-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters
-- name    : OAI_NumberTheory_PiExponent_Approximation_Parameters
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T14:46:52.917211+00:00
-- url     : https://prove2.me/theorems/fc417d07-f2ff-44a4-9f9b-c476904bc720
-- title:
--   Parameter record for exponent-gapped rational approximants
-- statement:
--   For a real parameter $\nu$, the structure $\mathrm{Parameters}(\nu)$ stores rational numbers $\theta,A,B,C$ and a real number $\eta$ satisfying $0<\theta<A<B<1$, $1-\theta<\nu(A-\theta)$, $1<C$, $B<1/C$, $B<C\theta$, $C\theta<1$, $0<\eta<1$, and $0<\nu(A(1-\eta)-\theta)-(1-\theta)$. The staged bundle includes the structure and its generated constructor and recursors, together with the theorem that every $p : \mathrm{Parameters}(\nu)$ has $0<(p.A : \mathbb{R})$. This statement describes the contents of an existing record; it does not assert that such a record exists for every $\nu$.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Parameters.lean#L93-L124

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

namespace OAI

namespace PiExponent





structure Parameters (ν : ℝ) where
  theta : ℚ
  A : ℚ
  B : ℚ
  C : ℚ
  eta : ℝ
  theta_pos : 0 < (theta : ℝ)
  theta_lt_A : (theta : ℝ) < A
  A_lt_B : (A : ℝ) < B
  B_lt_one : (B : ℝ) < 1
  approximation_gap : 1 - (theta : ℝ) < ν * ((A : ℝ) - theta)
  one_lt_C : 1 < (C : ℝ)
  B_lt_inv_C : (B : ℝ) < 1 / C
  B_lt_C_theta : (B : ℝ) < (C : ℝ) * theta
  C_theta_lt_one : (C : ℝ) * theta < 1
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  gap_pos : 0 < ν * ((A : ℝ) * (1 - eta) - theta) - (1 - theta)



namespace Parameters

variable {ν : ℝ} (p : Parameters ν)

theorem A_pos : 0 < (p.A : ℝ) := lt_trans p.theta_pos p.theta_lt_A















end Parameters

end PiExponent

end OAI


