-- Prove2me | Definitions.Def_ForwardRM_Cutoffs_Supplement_ContinuousModel
-- name    : ForwardRM_Cutoffs_Supplement_ContinuousModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:21:50.550497+00:00
-- url     : https://prove2.me/theorems/2c125d17-0c3e-4659-ab92-6dce0c6b592f
-- title:
--   §5.1 — continuous-time model, its discretization with period h = T/n, the optimal profit Π*(h), and the hypotheses of Theorem 3
-- statement:
--   The **continuous-time model** of §5.1 has the buyer side of the discrete model: values are i.i.d. with a continuous density $f$ that is positive on $[\underline v,\bar v]$ and zero outside, and the marginal revenue
--
--   $$m(v)=v-\frac{1-F(v)}{f(v)}$$
--
--   is strictly increasing and continuously differentiable on $[\underline v,\bar v]$, with $m(\underline v)<0<m(\bar v)$. Time runs continuously over $[0,T]$ with $T>0$. The instantaneous discount rate is $r>0$. Buyers enter according to a non-homogeneous Poisson process with rate $\lambda_t\ge 0$, and $\lambda$ is integrable on $[0,T]$.
--
--   For $n\ge1$ the **discretized problem** has sale dates $h,2h,\dots,nh=T$ with $h=T/n$. It is the discrete model of §2 with periods $1,\dots,n$ and discount factor $\delta=e^{-rh}$. The entrants of period $i$ are the buyers who arrive in $((i-1)h,ih]$, so their number is Poisson with mean
--
--   $$\Lambda_i=\int_{(i-1)h}^{ih}\lambda_s\,ds .$$
--
--   Its optimal cutoffs $x^k_{ih}$ and the functions $\Pi$, $\Delta\Pi$ and $D\Pi$ are those of the published discrete model. With $K$ units, the **optimal discretized profit** is
--
--   $$\Pi^*(h)=e^{-rh}\,\tilde\Pi^K_1(\emptyset),$$
--
--   which is the §4.1 optimum measured at time $0$.
--
--   The definition also names the Lipschitz hypothesis of Theorem 3 and Lemmas 5–6, and the additional slope hypothesis used only in the corrected Lemmas 5–6. The first is that $\lambda$ is Lipschitz continuous on $[0,T]$. The second is the Appendix A.3 bound $\underline m'=\inf_{[\underline v,\bar v]}m'>0$, written as $m(y)-m(x)\ge c\,(y-x)$ for some $c>0$ and all $\underline v\le x\le y\le\bar v$.
--
--   These objects carry Section 5's implementation result: Lemmas 5 and 6 bound the drops of the discretized cutoffs, and Theorem 3 compares posted-price revenue with $\Pi^*=\lim_{h\to0}\Pi^*(h)$.
--
--   **Formalization Note** Each discretization is a value of the published structure `ForwardRM.Cutoffs.Model`, so the cutoffs are the published `cutoff i k`. The value-side fields restate the published model's assumptions so that the construction can produce one. Mathlib's Poisson law is used with the nonnegative part of $\Lambda_i$, and $\Lambda_i\ge0$ for $1\le i\le n$ because $\lambda\ge0$ on $[0,T]$. In the difference form of $\underline m'>0$, the bound is equivalent to $m'\ge c$ on the interior, with one-sided endpoint derivatives for a $C^1$ function on the closed interval. This does not use Lean's total derivative of the extension outside the support.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 19, §5.1 (discretized problem, Π*(h), Π*); p. 20, Theorem 3 (Lipschitz λ); p. 36, Appendix A.3 (Λ_{t+h}, m̲′)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction

namespace ForwardRM.Cutoffs.Supplement

open MeasureTheory ProbabilityTheory

/-- The continuous-time model of §5.1 (Board–Skrzypacz, p. 19).

* Buyer values: the same primitives and standing assumptions as the discrete model
  `ForwardRM.Cutoffs.Model` (§2, pp. 6–7; §2.1, p. 9): i.i.d. values with continuous density `f`,
  positive on `[v̲, v̄]` and zero outside, total mass one; the marginal revenue
  `m = marginalRevenueOf f` strictly increasing and `C¹` on `[v̲, v̄]`, `m(v̲) < 0 < m(v̄)`.
* Time is continuous on `[0, T]`, `T > 0`, with instantaneous discount rate `r > 0`.
* Buyers enter by a non-homogeneous Poisson process of rate `λ_t ≥ 0`; the rate is integrable on
  `[0, T]`, so that the mean number of entrants `∫_a^b λ` of every subinterval is finite. -/
structure ContinuousModel where
  vlo : ℝ
  vhi : ℝ
  vlo_lt_vhi : vlo < vhi
  f : ℝ → ℝ
  f_continuousOn : ContinuousOn f (Set.Icc vlo vhi)
  f_pos : ∀ v ∈ Set.Icc vlo vhi, 0 < f v
  f_eq_zero : ∀ v, v ∉ Set.Icc vlo vhi → f v = 0
  f_total : ∫⁻ v, ENNReal.ofReal (f v) = 1
  m_strictMonoOn : StrictMonoOn (marginalRevenueOf f) (Set.Icc vlo vhi)
  m_contDiffOn : ContDiffOn ℝ 1 (marginalRevenueOf f) (Set.Icc vlo vhi)
  m_vlo_neg : marginalRevenueOf f vlo < 0
  m_vhi_pos : 0 < marginalRevenueOf f vhi
  /-- The horizon `T > 0` (real time). -/
  T : ℝ
  T_pos : 0 < T
  /-- The instantaneous discount rate `r > 0`. -/
  r : ℝ
  r_pos : 0 < r
  /-- The arrival rate `λ_t` of the Poisson entry process. -/
  lam : ℝ → ℝ
  lam_nonneg : ∀ s ∈ Set.Icc 0 T, 0 ≤ lam s
  lam_intervalIntegrable : IntervalIntegrable lam volume 0 T

namespace ContinuousModel

variable (C : ContinuousModel)

/-- The marginal revenue `m(v) = v − (1 − F(v))/f(v)`. -/
noncomputable def m (v : ℝ) : ℝ := marginalRevenueOf C.f v

/-- The period length `h = T / n` of the discretization with `n` sale dates `h, 2h, …, nh = T`. -/
noncomputable def step (n : ℕ) : ℝ := C.T / n

/-- The mean number of entrants of period `i` of the `n`-period discretization:
`Λ_i = ∫_{(i−1)h}^{ih} λ_s ds`, the Poisson mass of `((i−1)h, ih]` (p. 19, p. 36). -/
noncomputable def arrivalMass (n i : ℕ) : ℝ :=
  ∫ s in ((i : ℝ) - 1) * C.step n..(i : ℝ) * C.step n, C.lam s

theorem step_pos {n : ℕ} (hn : 1 ≤ n) : 0 < C.step n :=
  div_pos C.T_pos (by exact_mod_cast hn)

/-- The discretized problem of §5.1 (p. 19) with `n ≥ 1` sale dates `h, 2h, …, nh = T`, `h = T/n`,
as a discrete model of §2: periods `1, …, n`; discount factor `δ = e^{−rh}`; the entrants of period
`i` are those of `((i−1)h, ih]`, whose number is Poisson with mean `Λ_i = ∫_{(i−1)h}^{ih} λ`; the
same value distribution. -/
noncomputable def discretize (n : ℕ) (hn : 1 ≤ n) : ForwardRM.Cutoffs.Model where
  T := n
  one_le_T := hn
  δ := Real.exp (-(C.r * C.step n))
  δ_pos := Real.exp_pos _
  δ_lt_one := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos C.r_pos (C.step_pos hn)))
  vlo := C.vlo
  vhi := C.vhi
  vlo_lt_vhi := C.vlo_lt_vhi
  f := C.f
  f_continuousOn := C.f_continuousOn
  f_pos := C.f_pos
  f_eq_zero := C.f_eq_zero
  f_total := C.f_total
  arrivals := fun i => poissonPMF (C.arrivalMass n i).toNNReal
  m_strictMonoOn := C.m_strictMonoOn
  m_contDiffOn := C.m_contDiffOn
  m_vlo_neg := C.m_vlo_neg
  m_vhi_pos := C.m_vhi_pos

/-- `Π*(h)` for `h = T/n` (p. 19): the optimal profit of §4.1 in the discretized problem with `K`
units, at time `0`. The value `Π̃^K_1(∅)` of the dynamic program is measured at the first sale date
`h`; one factor `δ = e^{−rh}` discounts it to time `0`. -/
noncomputable def optProfit (K n : ℕ) (hn : 1 ≤ n) : ℝ :=
  (C.discretize n hn).δ * (C.discretize n hn).piTilde 1 K 0

/-- The A.3 hypothesis `m̲′ := inf_{[v̲, v̄]} m′ > 0` (p. 36), in difference form: some `c > 0` with
`m(y) − m(x) ≥ c (y − x)` for `v̲ ≤ x ≤ y ≤ v̄`. Since `m` is `C¹` on `[v̲, v̄]`, this is equivalent
to `m′ ≥ c` on the interior, with one-sided derivatives at the endpoints. It does not assert
a bound on Lean's total `deriv` of the extension outside the support. -/
def MarginalRevenueSlopeBounded : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Set.Icc C.vlo C.vhi, ∀ y ∈ Set.Icc C.vlo C.vhi, x ≤ y →
    c * (y - x) ≤ C.m y - C.m x

/-- The arrival rate is Lipschitz continuous on `[0, T]` (hypothesis of Theorem 3, p. 20). -/
def LipschitzRate : Prop :=
  ∃ L : NNReal, LipschitzOnWith L C.lam (Set.Icc 0 C.T)

end ContinuousModel

end ForwardRM.Cutoffs.Supplement


