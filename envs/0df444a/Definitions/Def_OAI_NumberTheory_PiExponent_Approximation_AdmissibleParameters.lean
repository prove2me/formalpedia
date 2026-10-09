-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters
-- name    : OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:46:56.992043+00:00
-- url     : https://prove2.me/theorems/9a1363ab-9f46-43e5-8f21-ce4ab0379046
-- title:
--   Admissible data for the approximation argument
-- statement:
--   Fix real parameters $\nu,\Lambda,c$. An element of $\mathrm{AdmissibleParameters}(\nu,\Lambda,c)$ consists of a base record $P:\mathrm{Parameters}(\nu)$, real numbers $\epsilon,F_0,w_\star$, natural numbers $m,K$, rational numbers $w_0,v_0,\sigma$, integer and natural sequences $p_n,q_n$, and a real sequence $x_n$, subject to the following conditions. The base parameters obey $0<\theta<A<B<1$, $1<C$, $B<1/C$, $B<C\theta$, $C\theta<1$, $0<\eta<1$, and $1-\theta<\nu(A-\theta)$, where $\theta,A,B,C,\eta$ are the fields of $P$. The additional gap is $g=\nu(A(1-\eta)-\theta)-(1-\theta)$; the record requires $0<\epsilon<g$ and $\epsilon\le 1/2$.
--
--   The scale and dimension data satisfy $0<F_0$, $2/\theta<F_0$, $\nu/F_0<\epsilon/3$, $1\le m$, and $K=\mathrm{dimensionK}(C,m)\ge1$. The rational weights satisfy $w_0=\mathrm{dimensionW}(B,m)$ and $v_0=\mathrm{dimensionV}(\theta,B,C,m)$ after casting to $\mathbb{R}$, with both positive, and
--
--   $$
--   K\frac{w_0}{v_0}\theta^m=\frac12,\qquad K\theta^m<1.
--   $$
--
--   They also satisfy the dimension margin $(\Lambda F_0m+2\log 2)/v_0+100K/w_0<\epsilon/3$ and the collision bound $2<c\,\eta^2K\theta^m/((m+1)v_0A^m)$. The rational $\sigma$ is positive and obeys
--
--   $$
--   (1+3\sigma)^{m+1}K(w_0/v_0)\theta^m<1,\quad (1+3\sigma)^mK\theta^m<1,\quad (1+\sigma)\theta<1.
--   $$
--
--   The sequences satisfy $x_0=1$, $x_{n+1}=\lceil\log q_n\rceil$, $2\le q_n$, $p_n\ne0$, and $|\pi-p_n/q_n|\le q_n^{-\nu}$ for every $n$, as well as $1\le x_i$ for every $i$. Their growth satisfies $\mathrm{SeparatedWeightGrowth}(m,D,x)$ with $D$ the separation factor formed from $m$, the interpolation separation constant at $(m,\sigma)$, $w_0,v_0,\theta$. Finally, $w_\star>0$ is a minimum attained among $x_1,\ldots,x_m$, and the weight margin is $\Lambda\sum_{i=1}^m1/x_i+(\theta+\log4+\log(2K)+\nu+\log(200K))/w_\star<\epsilon/3$.
--
--   The bundle contains the structure command and its 49 declarations generated from that structure command, plus nine additional declarations: the interpolation-separation constant, the weight-error coefficient, the rational-weight sequence and its cast/positivity lemmas, and four error definitions. It packages admissible data and derived quantities; it does not assert that such data exist for arbitrary $\nu,\Lambda,c$.
--
--   The nine declarations outside the structure also specify the following derived quantities. The interpolation separation constant is $2(m+2)^{m+2}(1+(m+2)/\sigma)^{m+2}$, and the weight-error coefficient is $\theta+\log4+\log(2K)+\nu+\log(200K)$. The rational weight is $1$ at index zero and $\lceil\log q_n\rceil$ at index $n+1$; its real cast equals $x_i$, and it is positive. The four error definitions are
--   $$
--   E_{\rm arith}=\frac{\Lambda F_0m}{v_0}+\Lambda\sum_{i=1}^m\frac1{x_i}+\frac{\theta}{w_\star},\qquad
--   E_{\rm trans}=\frac{\nu}{F_0}+\frac{\log2}{v_0}+\frac{\log4+\log(2K)+\nu}{w_\star},
--   $$
--   $$
--   E_{\rm holo}=\frac{100K}{w_0}+\frac{\log2}{v_0}+\frac{\log(200K)}{w_\star},\qquad
--   E_{\rm analytic}=E_{\rm trans}+E_{\rm holo}.
--   $$
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleParameters.lean#L14-L307

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_WeightSeparation
import Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring








namespace OAI

namespace PiExponent

noncomputable def interpolationSeparationConstant (m : ℕ) (sigma : ℚ) : ℝ :=
  2 * ((m : ℝ) + 2) ^ (m + 2) *
    (1 + ((m : ℝ) + 2) / (sigma : ℝ)) ^ (m + 2)



noncomputable def weightErrorCoefficient (nu theta : ℝ) (K : ℕ) : ℝ :=
  theta + Real.log 4 + Real.log (2 * (K : ℝ)) + nu + Real.log (200 * (K : ℝ))





structure AdmissibleParameters (nu Lambda c : ℝ) where
  base : Parameters nu
  epsilon : ℝ
  F0 : ℝ
  m : ℕ
  K : ℕ
  w0 : ℚ
  v0 : ℚ
  sigma : ℚ
  p : ℕ → ℤ
  q : ℕ → ℕ
  x : ℕ → ℝ
  wstar : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_gap : epsilon <
    nu * ((base.A : ℝ) * (1 - base.eta) - base.theta) - (1 - base.theta)
  epsilon_le_half : epsilon ≤ 1 / 2
  F0_pos : 0 < F0
  F0_large : 2 / (base.theta : ℝ) < F0
  initial_margin : nu / F0 < epsilon / 3
  m_pos : 1 ≤ m
  K_eq : K = dimensionK (base.C : ℝ) m
  K_pos : 1 ≤ K
  w0_eq : (w0 : ℝ) = dimensionW (base.B : ℝ) m
  v0_eq : (v0 : ℝ) = dimensionV (base.theta : ℝ) base.B base.C m
  w0_pos : 0 < (w0 : ℝ)
  v0_pos : 0 < (v0 : ℝ)
  volume_eq : (K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m = 1 / 2
  volume_lt_one : (K : ℝ) * (base.theta : ℝ) ^ m < 1
  dimension_margin :
    (Lambda * F0 * (m : ℝ) + 2 * Real.log 2) / (v0 : ℝ) +
      100 * (K : ℝ) / (w0 : ℝ) < epsilon / 3
  collision_margin : 2 < c *
    (base.eta ^ 2 * (K : ℝ) * (base.theta : ℝ) ^ m /
      (((m : ℝ) + 1) * (v0 : ℝ) * (base.A : ℝ) ^ m))
  sigma_pos : 0 < (sigma : ℝ)
  sigma_volume : (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
    ((K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m) < 1
  sigma_centers : (1 + 3 * (sigma : ℝ)) ^ m *
    ((K : ℝ) * (base.theta : ℝ) ^ m) < 1
  sigma_theta : (1 + (sigma : ℝ)) * (base.theta : ℝ) < 1
  x_zero : x 0 = 1
  x_log : ∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)
  approximations : ∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
    |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu)
  x_one_le : ∀ i, 1 ≤ x i
  weight_growth : PiExponentApprox.SeparatedWeightGrowth m
    (PiExponentApprox.weightSeparationFactor m (interpolationSeparationConstant m sigma)
      w0 v0 base.theta) x
  wstar_pos : 0 < wstar
  wstar_lower : ∀ i : Fin m, wstar ≤ x (i.val + 1)
  wstar_attained : ∃ i : Fin m, wstar = x (i.val + 1)
  weight_margin : Lambda * (∑ i : Fin m, 1 / x (i.val + 1)) +
    weightErrorCoefficient nu base.theta K / wstar < epsilon / 3



namespace AdmissibleParameters

variable {nu Lambda c : ℝ} (d : AdmissibleParameters nu Lambda c)

noncomputable def rationalWeight : ℕ → ℚ
  | 0 => 1
  | n + 1 => (Nat.ceil (Real.log (d.q n)) : ℚ)

theorem cast_rationalWeight (i : ℕ) : (d.rationalWeight i : ℝ) = d.x i := by
  cases i with
  | zero => simpa [rationalWeight] using d.x_zero.symm
  | succ n => simpa [rationalWeight] using (d.x_log n).symm

theorem rationalWeight_pos (i : ℕ) : 0 < d.rationalWeight i := by
  have h : (0 : ℝ) < (d.rationalWeight i : ℝ) := by
    rw [d.cast_rationalWeight]
    exact zero_lt_one.trans_le (d.x_one_le i)
  exact_mod_cast h











noncomputable def arithmeticError : ℝ :=
  Lambda * d.F0 * (d.m : ℝ) / (d.v0 : ℝ) +
    Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) + (d.base.theta : ℝ) / d.wstar

noncomputable def translationError : ℝ :=
  nu / d.F0 + Real.log 2 / (d.v0 : ℝ) +
    (Real.log 4 + Real.log (2 * (d.K : ℝ)) + nu) / d.wstar

noncomputable def holomorphicError : ℝ :=
  100 * (d.K : ℝ) / (d.w0 : ℝ) + Real.log 2 / (d.v0 : ℝ) +
    Real.log (200 * (d.K : ℝ)) / d.wstar

noncomputable def analyticError : ℝ := d.translationError + d.holomorphicError







end AdmissibleParameters

end PiExponent

end OAI


