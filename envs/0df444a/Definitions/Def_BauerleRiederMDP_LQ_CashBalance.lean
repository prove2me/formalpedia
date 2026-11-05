-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_CashBalance
-- name    : BauerleRiederMDP_LQ_CashBalance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:34.356059+00:00
-- url     : https://prove2.me/theorems/282a661d-47f6-4d23-a42e-e19199d6fce4
-- title:
--   The cash balance problem, its minimal cost $J_n$ and the critical-level rule (2.5)
-- statement:
--   The **cash balance problem** is a stationary Markov Decision Model with state $x\in\mathbb R$ (the cash level of a firm) and action $a\in\mathbb R$ (the new cash level after a transfer); every action is admissible. Its data are:
--
--   1. the transfer cost $c(z)=c_uz^++c_dz^-$ with $c_u,c_d>0$;
--   2. a holding cost $L:\mathbb R\to\mathbb R_+$ with $L(0)=0$, $L$ convex and $\lim_{|x|\to\infty}L(x)/|x|=\infty$;
--   3. i.i.d. cash changes $Z_1,Z_2,\dots$ with finite expectation and law $\mu_Z$; the next state is $a-Z_{n+1}$;
--   4. a discount factor $\beta\in(0,1]$, and no terminal cost.
--
--   The one-stage reward is $r(x,a)=-c(a-x)-L(a)$. The **minimal expected discounted cost over $n$ stages** is
--   $$
--   J_n(x)=\inf_{\pi}\ \mathbb E^\pi_x\Big[\sum_{k=0}^{n-1}\beta^k\big(c(A_k-X_k)+L(A_k)\big)\Big],\qquad J_0\equiv0,
--   $$
--   the infimum over all $n$-stage policies of measurable decision rules, and $J_{n\pi}$ is the expected discounted cost of a fixed policy $\pi$. The **critical-level rule** with levels $S_-,S_+$ is
--   $$
--   f(x)=\begin{cases}S_-&x<S_-\\ x&S_-\le x\le S_+\\ S_+&x>S_+.\end{cases}
--   $$
--
--   **Formalization Note** The model is an instance of the published stationary Markov Decision Model `MDPFinance.Stationary.StationaryMarkovDecisionModel` (§2.5); by Remark 2.3.15, $J_n$ and $J_{n\pi}$ are minus its published reward value functions `J` and `Jpi`, valued in extended reals. $\lim_{|x|\to\infty}$ is the limit along the cocompact filter of $\mathbb R$; "finite expectation" is integrability of the identity under $\mu_Z$. Measurability of $L$ is derived from convexity.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §2.6.2, pp.46–49 (PDF 61–64), model, data list and (2.5); §2.5, p.39 (PDF 54), J_n and J_{nπ}; Remark 2.3.15, pp.27–28 (PDF 42–43)

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_ValueFunction
import Definitions.Def_BauerleRiederMDP_LQ_DisturbanceKernel

open MeasureTheory ProbabilityTheory Filter

namespace BauerleRiederMDP.LQ

/-- **The cash balance problem** (Bäuerle & Rieder 2011, §2.6.2, pp.46–47, PDF 61–62), with its
assumptions:

* the transfer cost `c(z) := c_u z^+ + c_d z^−` with `c_u, c_d > 0`;
* the holding cost `L : ℝ → ℝ_+` with `L(0) = 0`, `x ↦ L(x)` convex and
  `lim_{|x|→∞} L(x)/|x| = ∞`;
* the cash changes `(Z_n)` are i.i.d. "with finite expectation", with common law `μZ`;
* the discount factor `β ∈ (0, 1]`.

**Formalization Note.** `lim_{|x|→∞}` is the limit along `Filter.cocompact ℝ` (both `x → +∞` and
`x → −∞`). "Finite expectation" is `Integrable id μZ`. -/
structure CashBalanceData where
  cu : ℝ
  cd : ℝ
  hcu : 0 < cu
  hcd : 0 < cd
  L : ℝ → ℝ
  hL_nonneg : ∀ x, 0 ≤ L x
  hL0 : L 0 = 0
  hL_convex : ConvexOn ℝ Set.univ L
  hL_coercive : Tendsto (fun x => L x / |x|) (cocompact ℝ) atTop
  μZ : ProbabilityMeasure ℝ
  hZ_int : Integrable id (μZ : Measure ℝ)
  β : ℝ
  hβ_pos : 0 < β
  hβ_le_one : β ≤ 1

namespace CashBalanceData

/-- The transfer cost `c(z) := c_u z^+ + c_d z^−` (Bäuerle & Rieder 2011, §2.6.2, p.46, PDF 61). -/
def c (M : CashBalanceData) (z : ℝ) : ℝ :=
  M.cu * max z 0 + M.cd * max (-z) 0

lemma continuous_L (M : CashBalanceData) : Continuous M.L :=
  continuousOn_univ.mp (M.hL_convex.continuousOn isOpen_univ)

lemma measurable_reward (M : CashBalanceData) :
    Measurable (fun xa : ℝ × ℝ => -(M.c (xa.2 - xa.1) + M.L xa.2)) := by
  have hL := M.continuous_L
  have : Continuous (fun xa : ℝ × ℝ => -(M.c (xa.2 - xa.1) + M.L xa.2)) := by
    unfold c
    fun_prop
  exact this.measurable

lemma measurable_cashTransition :
    Measurable (fun p : (ℝ × ℝ) × ℝ => p.1.2 - p.2) := by
  fun_prop

/-- **The cash balance problem as a stationary Markov Decision Model** (Bäuerle & Rieder 2011,
§2.6.2, p.47, PDF 62, data list): `E := ℝ` (cash level), `A := ℝ` (new cash level after transfer),
`D(x) := A`, `T(x, a, z) := a − z`, `Q^Z(·|x,a)` := distribution of `Z_{n+1}`,
`r(x, a) := −c(a − x) − L(a)`, `g ≡ 0`, discount factor `β`. An instance of the published stationary
Markov Decision Model `MDPFinance.Stationary.StationaryMarkovDecisionModel` (§2.5). -/
noncomputable def toSMDP (M : CashBalanceData) :
    MDPFinance.Stationary.StationaryMarkovDecisionModel ℝ ℝ where
  D := Set.univ
  hD_meas := MeasurableSet.univ
  hD_sel := ⟨fun _ => 0, measurable_const, fun _ => Set.mem_univ _⟩
  Q := disturbanceKernel (E := ℝ) (A := ℝ) (M.μZ : Measure ℝ) (fun _ a z => a - z)
  hQ_prob := fun xa =>
    isProbabilityMeasure_disturbanceKernel (M.μZ : Measure ℝ) measurable_cashTransition xa
  r := fun xa => -(M.c (xa.2 - xa.1) + M.L xa.2)
  hr_meas := M.measurable_reward
  g := fun _ => 0
  hg_meas := measurable_const
  β := M.β
  hβ_pos := M.hβ_pos
  hβ_le_one := M.hβ_le_one

/-- **The minimal expected discounted cost over `n` stages**, `J_n(x)` (Bäuerle & Rieder 2011,
§2.6.2, p.47, PDF 62: "we will treat this problem as one of minimizing cost"; §2.5, p.39, PDF 54,
`J_0 := g`, `J_n := sup_{π ∈ F^n} J_{nπ}`; Remark 2.3.15).

**Formalization Note.** Minus the maximal expected discounted reward `MDPFinance.Stationary.J`
of `toSMDP` (cost = −reward, Remark 2.3.15), i.e. the infimum over all `n`-stage policies of
measurable decision rules of `𝔼_x[Σ_{k<n} β^k (c(A_k − X_k) + L(A_k))]`, valued in `[0, ∞]`. -/
noncomputable def Jcost (M : CashBalanceData) (n : ℕ) (x : ℝ) : EReal :=
  -MDPFinance.Stationary.J M.toSMDP n x

/-- The expected discounted cost `J_{nπ}(x)` over `n` stages of the policy `π = (f_0, …, f_{n−1})`
(Bäuerle & Rieder 2011, §2.5, p.39, PDF 54, as a cost; Remark 2.3.15). -/
noncomputable def JcostPi (M : CashBalanceData) (π : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : EReal :=
  -MDPFinance.Stationary.Jpi M.toSMDP π n x

end CashBalanceData

/-- The decision rule of the form (2.5)/(2.6) with critical levels `S_−`, `S_+` (Bäuerle & Rieder
2011, §2.6.2, pp.48–49, PDF 63–64): `S_−` if `x < S_−`, `x` if `S_− ≤ x ≤ S_+`, `S_+` if `x > S_+`. -/
noncomputable def cbRule (Sm Sp : ℝ) (x : ℝ) : ℝ :=
  if x < Sm then Sm else if x ≤ Sp then x else Sp

end BauerleRiederMDP.LQ


