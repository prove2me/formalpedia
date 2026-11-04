-- Prove2me | Definitions.Def_LostSalesConstantOrder_LargeLeadTime_ConstantOrder
-- name    : LostSalesConstantOrder_LargeLeadTime_ConstantOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:41.258989+00:00
-- url     : https://prove2.me/theorems/a09fb939-6f98-4405-a059-76bb6a5c7448
-- title:
--   The constant-order policy $\pi_r$, the best constant $z$, and the constants $m$ and $y(\epsilon)$ (with $\mathbb E[D]$ restored)
-- statement:
--   **The constant-order policy.** For $r\in[0,\mathbb E[D])$, $\pi_r$ orders the random amount $I^r_\infty+r$ in the first period (an amount drawn from the law of $I^r_\infty$, plus $r$, independently of all demands) and the constant $r$ in every later period. It is realized as an admissible policy whose first order is $F^{-1}(U)+r$, where $U$ is the policy's private uniform seed on $[0,1]$ and $F^{-1}(u)=\inf\{x\ge0: u\le\mathbb P(I^r_\infty\le x)\}$ is the quantile function of $I^r_\infty$.
--
--   **The best constant.**
--   $$
--   z=\operatorname*{arg\,min}_{v\ge0}\big(h\,\mathbb E[I^v_\infty]-cv\big),
--   $$
--   the infimum of all minimizers when the minimizer is not unique.
--
--   **The constants.**
--   $$
--   m=\Big\lceil\big(26(3\zeta+c(h\sigma)^{-1}\mathbb E[D]+1)\big)^2\Big\rceil,
--   $$
--   $$
--   y(\epsilon)=\max\Big(2^{14}h(Q+2^{3/2}\mathbb E[D])(\mathbb E^2[D]+\mathbb E[D^2])^3\sigma^{-6}m^3g^{-1}\epsilon^{-1},\ \big(12c\,\mathbb E[D]\,g^{-1}((2ch^{-1})^{1/2}+3)\big)^2\epsilon^{-2}\Big).
--   $$
--
--   $y(\epsilon)$ is the lead time beyond which the constant-order policy $\pi_z$ is within a factor $1+\epsilon$ of optimal (Theorem 1).
--
--   **Formalization Note** The second term of $y(\epsilon)$ is printed on p. 5 as $(12cg^{-1}((2ch^{-1})^{1/2}+3))^2\epsilon^{-2}$, without the factor $\mathbb E[D]$. The proof of Theorem 1 (p. 15) uses that term to bound $c(\lceil(2ch^{-1}L)^{1/2}\rceil+2)(gL)^{-1}$, which comes from Corollary 12, whose proof establishes $\mathcal I^*\le(\lceil(2ch^{-1}L)^{1/2}\rceil+2)\mathbb E[D]$ (p. 14). With the factor restored, $y(\epsilon)$ is invariant under rescaling the demand $D\mapsto\lambda D$, as it must be; the printed term is not. The minimized objective of $z$ is $h\mathbb E[I^v_\infty]+c(\mathbb E[D]-v)$ in $[0,\infty]$: it differs from the paper's by the constant $c\mathbb E[D]$ where $\mathbb E[I^v_\infty]<\infty$ and is $+\infty$ where $\mathbb E[I^v_\infty]=\infty$ (in particular for $v\ge\mathbb E[D]$), so the minimizers are the paper's; if there were none, $z$ would be $0$. $\pi_r$ is defined for every $r\ge0$; for $r\ge\mathbb E[D]$ its first order is a junk value, and every statement using $\pi_r$ assumes $r<\mathbb E[D]$ or takes $r=z$. $2^{3/2}$ is written $2\sqrt2$. $m$ is a natural number.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 5 (§3.1, m, z, y(ϵ) and Remarks), p. 6 (§3.2, π_r); E[D] restored in y(ϵ) per the proofs on pp. 14–15

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_RandomWalk

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-!
Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, arXiv:1211.4063v2, §3.1 (p. 5) and §3.2
(p. 6): the constant-order policy `π_r`, the best constant `z`, and the constants `m` and `y(ϵ)`.
-/

/-- The generalized inverse of the distribution function of `μ`:
`F⁻¹(u) = inf{x ≥ 0 : u ≤ μ([0, x])}`, in `[0, ∞]` (`∞` when no `x` qualifies). For `U` uniform on
`[0, 1]`, `F⁻¹(U)` has law `μ` when `μ` is a probability measure (the value `∞` occurs at most at
`u = 1`, a null event). -/
def quantile (μ : Measure ℝ≥0) (u : ℝ) : ℝ≥0∞ :=
  ⨅ (x : ℝ≥0) (_ : ENNReal.ofReal u ≤ μ (Set.Iic x)), (x : ℝ≥0∞)

lemma quantile_mono (μ : Measure ℝ≥0) : Monotone (quantile μ) := by
  intro u u' huu'
  unfold quantile
  exact le_iInf₂ fun x hx =>
    iInf₂_le (f := fun (y : ℝ≥0) (_ : ENNReal.ofReal u ≤ μ (Set.Iic y)) => (y : ℝ≥0∞)) x
      (le_trans (ENNReal.ofReal_le_ofReal huu') hx)

/-- The order rule of `π_r`: in the first period (Lean `t = 0`) the random amount
`F⁻¹(U) + r`, with `F⁻¹` the quantile function of the law of `I^r_∞` and `U` the policy's private
uniform seed; in every later period the constant `r`. -/
def constantOrderDecision (P : CappedBaseStock.DemandLaw) (r : ℝ≥0) (t : ℕ)
    (a : (Fin t → ℝ≥0) × ℝ) : ℝ≥0 :=
  if t = 0 then (quantile (lawSupWalk P r) a.2).toNNReal + r else r

/-- `π_r` (p. 6): "orders the random amount `I^r_∞ + r` … in the first time period, and then
orders the constant `r` in all subsequent time periods", realized as an admissible policy of the
`CappedBaseStock` model. The first order depends only on the private seed, so it is independent of
all demands and has the law of `I^r_∞ + r`. -/
def constantOrderPolicy (P : CappedBaseStock.DemandLaw) (r : ℝ≥0) :
    CappedBaseStock.AdmissiblePolicy where
  decision := constantOrderDecision P r
  measurable_decision t := by
    unfold constantOrderDecision
    by_cases ht : t = 0
    · simp only [ht, if_true]
      exact (((quantile_mono _).measurable.comp measurable_snd).ennreal_toNNReal).add_const _
    · simp only [ht, if_false]
      exact measurable_const

/-- The objective of `z` up to the additive constant `c E[D]`: `h E[I^v_∞] + c(E[D] − v)` in
`[0, ∞]`. It equals `h E[I^v_∞] − c v + c E[D]` for `v < E[D]` and is `∞` whenever
`E[I^v_∞] = ∞`. -/
def zObjective (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters) (v : ℝ≥0) :
    ℝ≥0∞ :=
  ENNReal.ofReal prm.h * ∫⁻ d, supWalk v d ∂CappedBaseStock.demandPathLaw P +
    ENNReal.ofReal (prm.p * (CappedBaseStock.mean P - v))

/-- `z = argmin_{v ≥ 0} (h E[I^v_∞] − c v)` (p. 5), the infimum of all minimizers when the minimizer
is not unique. (`0` if there were no minimizer.) -/
def zStar (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters) : ℝ≥0 :=
  sInf {v : ℝ≥0 | ∀ w : ℝ≥0, zObjective P prm v ≤ zObjective P prm w}

/-- `m = ⌈(26(3ζ + c(hσ)⁻¹E[D] + 1))²⌉` (p. 5), a natural number. -/
def mConst (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters) : ℕ :=
  ⌈(26 * (3 * skew P + prm.p / (prm.h * sigma P) * CappedBaseStock.mean P + 1)) ^ 2⌉₊

/-- `y(ϵ)` of p. 5 **with the factor `E[D]` of its second term restored**:
`max(2¹⁴ h (Q + 2^{3/2} E[D]) (E²[D] + E[D²])³ σ⁻⁶ m³ g⁻¹ ϵ⁻¹,
     (12 c E[D] g⁻¹ ((2 c h⁻¹)^{1/2} + 3))² ϵ⁻²)`.
The page prints `12 c g⁻¹` in the second term; the proof on p. 15 needs `12 c E[D] g⁻¹` (the
page's version is not invariant under rescaling demand). `2^{3/2}` is written `2 √2`. -/
def yEps (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters) (ε : ℝ) : ℝ :=
  max
    (2 ^ 14 * prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * CappedBaseStock.mean P) *
      (CappedBaseStock.mean P ^ 2 + secondMoment P) ^ 3 / sigma P ^ 6 *
      (mConst P prm : ℝ) ^ 3 / gConst P prm / ε)
    ((12 * prm.p * CappedBaseStock.mean P / gConst P prm *
      (Real.sqrt (2 * prm.p / prm.h) + 3)) ^ 2 / ε ^ 2)

end LostSalesConstantOrder.LargeLeadTime


