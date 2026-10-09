-- Prove2me | Definitions.Def_MultiItemRev_MultiBuyer_BN
-- name    : MultiItemRev_MultiBuyer_BN
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:08.542796+00:00
-- url     : https://prove2.me/theorems/a9c2b317-156a-457a-9108-bfa0356ad247
-- title:
--   §A.7, p. 47 — Bayesian Nash implementation with independent buyers: interim payoffs, IC-BN, IR-BN, Rev^BN
-- statement:
--   Consider $n$ buyers whose valuation vectors $X^1, \dots, X^n \in \mathbb R^k_+$ are **independent**, buyer $j$'s with law $\rho_j$, so that the profile $X$ has the product law $\rho_1 \otimes \dots \otimes \rho_n$. Mechanisms, feasibility $\sum_j q^j_i \le 1$ (ex post) and the seller's revenue $S = \sum_j s^j$ are those of the $n$-buyer model.
--
--   1. The **interim payoff** of buyer $j$ with values $x^j$ who reports $\tilde x^j$ is
--   $$\mathbb E\big[q^j(\tilde x^j, X^{-j})\cdot x^j - s^j(\tilde x^j, X^{-j}) \,\big|\, X^j = x^j\big] = \mathbb E\big[q^j(\tilde x^j, X^{-j})\cdot x^j - s^j(\tilde x^j, X^{-j})\big],$$
--   the equality holding because the buyers are independent; its value at $\tilde x^j = x^j$ is $\bar b^j(x^j) = \mathbb E[b^j(X) \mid X^j = x^j]$.
--   2. **IC-BN**: for every buyer $j$ and every $x^j \in \mathbb R^k_+$, $\bar b^j(x^j)$ is the maximum over $\tilde x^j \in \mathbb R^k_+$ of the interim payoff of reporting $\tilde x^j$. **IR-BN**: $\bar b^j(x^j) \ge 0$ for every $j$ and every $x^j \in \mathbb R^k_+$.
--   3. $\mathrm{Rev}^{BN}(X)$ is the supremum of $R(\mu; X) = \mathbb E[S(X)]$ over feasible, IC-BN and IR-BN mechanisms (with measurable allocations and payments).
--   4. For laws $\nu_1, \nu_2$ on $\mathbb R_+$, a buyer's law for two goods with independent values of laws $\nu_1$ and $\nu_2$ is $\nu_1 \otimes \nu_2$; a buyer's law for one good of value law $\nu$ is $\nu$ itself.
--
--   These are the objects of Theorem 34.
--
--   **Formalization Note** Buyer $j$'s law is `ρ j : Measure (ι → ℝ≥0)` and the profile law is `Measure.pi ρ`. The interim payoff integrates over the whole profile law with buyer $j$'s coordinate overwritten (`Function.update x j r`), which, for probability laws, is integration over the others' product law. Interim payoffs and revenues are `EReal` differences of the integrals of the positive and negative parts. Allocations as well as payments are required measurable, so that the interim expectations of $q^j\cdot x^j$ are defined (the paper takes this for granted). The instances record that `oneGoodBuyer ν` and `twoGoodsBuyer ν₁ ν₂` are probability laws when `ν`, `ν₁`, `ν₂` are.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 47, Appendix A.7 (IC-BN, IR-BN, Rev^BN) and footnote 41; p. 48, footnote 42 (feasibility stays ex post); p. 29, footnote 27

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.MultiBuyer

/-!
# Bayesian Nash implementation with independent buyers (Hart–Nisan, Appendix A.7, p. 47)

The buyers' valuation vectors `X^1, …, X^n` are independent, buyer `j`'s with law
`ρ j : Measure (ι → ℝ≥0)`, so the profile `X` has the product law `Measure.pi ρ`.
-/

/-- The law of the profile `X = (X^1, …, X^n)` of independent buyers. -/
noncomputable def profileLaw {n : ℕ} {ι : Type*} [Fintype ι] (ρ : Fin n → Measure (ι → ℝ≥0))
    [∀ j, SigmaFinite (ρ j)] : Measure (Fin n → ι → ℝ≥0) :=
  Measure.pi ρ

/-- The interim payoff of buyer `j` with true values `t` who reports `r`:
`E[q^j(r, X^{-j}) · t - s^j(r, X^{-j})]`, which for independent buyers is
`E[q^j(r, X^{-j}) · X^j - s^j(r, X^{-j}) | X^j = t]` (p. 47). The others' reports `X^{-j}` are drawn
from the product law and buyer `j`'s coordinate is overwritten by `r`. Computed in `EReal` as the
difference of the integrals of the positive and negative parts. -/
noncomputable def interimPayoff {n : ℕ} {ι : Type*} [Fintype ι] (M : MechanismN n ι)
    (ρ : Fin n → Measure (ι → ℝ≥0)) [∀ j, SigmaFinite (ρ j)] (j : Fin n) (r t : ι → ℝ≥0) :
    EReal :=
  ((∫⁻ x, ENNReal.ofReal (∑ i, M.q (Function.update x j r) j i * (t i : ℝ) -
      M.s (Function.update x j r) j) ∂(profileLaw ρ) : ℝ≥0∞) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-(∑ i, M.q (Function.update x j r) j i * (t i : ℝ) -
      M.s (Function.update x j r) j)) ∂(profileLaw ρ) : ℝ≥0∞) : EReal)

/-- IC-BN (p. 47): `b̄^j(x^j) = max_{x̃^j} E[q^j(x̃^j, X^{-j}) · x^j - s^j(x̃^j, X^{-j}) | X^j = x^j]`
for every buyer `j` and every `x^j ∈ ℝ^k_+`. -/
def IsICBN {n : ℕ} {ι : Type*} [Fintype ι] (M : MechanismN n ι)
    (ρ : Fin n → Measure (ι → ℝ≥0)) [∀ j, SigmaFinite (ρ j)] : Prop :=
  ∀ (j : Fin n) (t r : ι → ℝ≥0), interimPayoff M ρ j r t ≤ interimPayoff M ρ j t t

/-- IR-BN (p. 47): `b̄^j(x^j) ≥ 0` for every buyer `j` and every `x^j ∈ ℝ^k_+`. -/
def IsIRBN {n : ℕ} {ι : Type*} [Fintype ι] (M : MechanismN n ι)
    (ρ : Fin n → Measure (ι → ℝ≥0)) [∀ j, SigmaFinite (ρ j)] : Prop :=
  ∀ (j : Fin n) (t : ι → ℝ≥0), 0 ≤ interimPayoff M ρ j t t

/-- Feasible (ex post, footnote 42), IC-BN and IR-BN mechanisms whose payments and allocations are
measurable (so that the conditional expectations in IC-BN are defined). -/
def IsAdmissibleBN {n : ℕ} {ι : Type*} [Fintype ι] (M : MechanismN n ι)
    (ρ : Fin n → Measure (ι → ℝ≥0)) [∀ j, SigmaFinite (ρ j)] : Prop :=
  IsFeasibleN M ∧ IsICBN M ρ ∧ IsIRBN M ρ ∧ (∀ j, Measurable (fun x => M.s x j)) ∧
    ∀ j i, Measurable (fun x => M.q x j i)

/-- `Rev^{BN}(X)` (p. 47) for independent buyers with laws `ρ j`: the supremum of
`R(µ; X) = E[∑_j s^j(X)]` over IC-BN and IR-BN mechanisms. -/
noncomputable def RevBN {n : ℕ} {ι : Type*} [Fintype ι] (ρ : Fin n → Measure (ι → ℝ≥0))
    [∀ j, SigmaFinite (ρ j)] : ℝ≥0∞ :=
  ⨆ (M : MechanismN n ι) (_ : IsAdmissibleBN M ρ), (expRevenueN (profileLaw ρ) M).toENNReal

/-- One buyer's law for a single good with value law `ν`. -/
noncomputable def oneGoodBuyer (ν : Measure ℝ≥0) : Measure (Unit → ℝ≥0) :=
  ν.map (fun t _ => t)

/-- One buyer's law for two goods with independent values of laws `ν₁` (good 1, index `0`) and
`ν₂` (good 2, index `1`). -/
noncomputable def twoGoodsBuyer (ν₁ ν₂ : Measure ℝ≥0) : Measure (Fin 2 → ℝ≥0) :=
  (ν₁.prod ν₂).map (fun p => ![p.1, p.2])

instance (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] : IsProbabilityMeasure (oneGoodBuyer ν) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

instance (ν₁ ν₂ : Measure ℝ≥0) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    IsProbabilityMeasure (twoGoodsBuyer ν₁ ν₂) :=
  Measure.isProbabilityMeasure_map (by
    refine Measurable.aemeasurable ?_
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i
    · exact measurable_fst
    · exact measurable_snd)

end MultiItemRev.MultiBuyer


