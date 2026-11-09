-- Prove2me | Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
-- name    : BudgetedAuctionLearning_Robustness_DualPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:22.467916+00:00
-- url     : https://prove2.me/theorems/8f33af0c-4f8e-41d8-a25c-b76377171ba3
-- title:
--   §5 — Bellman value $R_\tau$, dual function $f$, threshold $g^\star$, smoothing $g^\star_\sigma$, potential $G_\sigma$, criterion of Lemma 5.1
-- statement:
--   Fix $\mu$ and let $R^\star=R^\star(\mu)$. For multiplier $\lambda\ge0$ the next multiplier is $\lambda+\eta(\rho_L-\lambda P_L(\hat v_O,v_L,v_O))$. The Bellman value is $R_0=0$ and
--
--   $$R_\tau(\lambda)=\sup_{\hat v_O}\ E\big[U_O-\mu\lambda P_O+R_{\tau-1}\big(\lambda+\eta(\rho_L-\lambda P_L)\big)\big].$$
--
--   The dual function and threshold, Eq. (14), are
--
--   $$f(\lambda,g)=\sup_{\hat v_O}\big(U_O(\hat v_O)-\mu\lambda P_O(\hat v_O)+g(\rho_L-\lambda P_L(\hat v_O))\big),\qquad g^\star(\lambda)=\sup\{g\le0: f(\lambda,g)\le R^\star\}.$$
--
--   For $\sigma>0$, Eqs. (17) and (18) give
--
--   $$g^\star_\sigma(\lambda)=\frac1\sigma\int_\lambda^{\lambda+\sigma}g^\star(x)\,dx,\qquad G_\sigma(\lambda)=-\int_\lambda^\infty g^\star_\sigma(x)\,dx.$$
--
--   The criterion of Lemma 5.1 for a pair $(G,A)$ is that $G\ge0$ on $[0,\infty)$ and that for all $\lambda\ge0$
--
--   $$A\ge\sup_{\hat v_O}\Big(U_O(\hat v_O)-\mu\lambda P_O(\hat v_O)+\frac1\eta E\big[G(\lambda+\eta(\rho_L-\lambda P_L))-G(\lambda)\big]\Big).$$
--
--   These objects carry the Lagrangian analysis behind the main theorem.
--
--   **Formalization Note.** $\lambda$ is real and every statement restricts to $\lambda\ge0$. An empty threshold set gives $-\infty$. The Lean name `sig` stands for $\sigma$. `bellmanValue` integrates `toENNReal` of the previous value, which is exact since $R_\tau\in[0,\tau]$ on $\lambda\ge0$; each $R_\tau$ is lower semicontinuous on $(0,\infty)$ and hence Borel, so this is a genuine integral. $G_\sigma$ uses a Bochner integral whose tail integrability follows in Lemma 5.8 from $g^\star(\bar\lambda)=0$. The criterion also records measurability of $G$ on $[0,\infty)$, so that the expectation in (11) is well defined.
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), §5.1, printed p. 13 (PDF p. 14); Eq. (11), printed p. 14 (PDF p. 15); Eq. (14), printed p. 15 (PDF p. 16); Eqs. (17), (18), printed pp. 18–19 (PDF pp. 19–20)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_Benchmark
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- The dual function of §5.2 at multiplier `lam` and real `g`:
`f(λ,g) = sup_{v̂_O} [U_O(v̂_O) - μ λ P_O(v̂_O) + g (ρ_L - λ P_L(v̂_O))]`. The physical domain is
`λ ≥ 0`. `P_L(v̂_O) ≤ 1` is finite, so its `toReal` is exact. -/
noncomputable def dualFunction (fmt : AuctionFormat) (D : Measure ValuePair) (ρL μ lam g : ℝ) : EReal :=
  ⨆ a : FakeValue,
    (((expValue D a : ℝ≥0∞) : EReal) - ((ENNReal.ofReal (μ * lam) * expPayO fmt D a : ℝ≥0∞) : EReal)) +
      ((g * (ρL - lam * (expPayL fmt D a).toReal) : ℝ) : EReal)

/-- The threshold of Eq. (14): `g★(λ) = sup {g ≤ 0 : f(λ,g) ≤ R★}`, valued in `EReal`, so an empty
set gives `⊥ = -∞`, as the source says. -/
noncomputable def dualThreshold (fmt : AuctionFormat) (D : Measure ValuePair) (ρL μ lam : ℝ) : EReal :=
  ⨆ (g : ℝ) (_ : g ≤ 0 ∧ dualFunction fmt D ρL μ lam g ≤ lagrangianBenchmark fmt D ρL μ), (g : EReal)

/-- The average of Eq. (17): `g★_σ(λ) = (1/σ) ∫_λ^{λ+sig} g★(x) dx`. `g★` is finite and monotone on
`[0,∞)` when `E[v_L] > 0` (Lemmas 5.3, 5.4), so `toReal` is exact and the integrand integrable on
`[λ, λ+sig]`, `λ ≥ 0`, in that situation. -/
noncomputable def smoothedThreshold (fmt : AuctionFormat) (D : Measure ValuePair) (ρL μ sig lam : ℝ) : ℝ :=
  (1 / sig) * ∫ x in lam..(lam + sig), (dualThreshold fmt D ρL μ x).toReal

/-- The potential of Eq. (18): `G_σ(λ) = - ∫_λ^∞ g★_σ(x) dx`. Integrability of the tail is proved
from `g★(λ̄) = 0`, not assumed here. -/
noncomputable def smoothedPotential (fmt : AuctionFormat) (D : Measure ValuePair) (ρL μ sig lam : ℝ) : ℝ :=
  -∫ x in Set.Ici lam, smoothedThreshold fmt D ρL μ sig x

/-- The controller's transition in fake-value form, `λ + η (ρ_L - λ p)` with `p` the unscaled learner
payment. For `0 < η < 1`, `λ ≥ 0`, `ρ_L > 0`, `p ≤ 1` it stays nonnegative: no projection. -/
noncomputable def nextPacing (ρL η lam p : ℝ) : ℝ := lam + η * (ρL - lam * p)

/-- The Bellman value `R_τ(λ)` of §5.1, printed p. 13: `R_0 = 0`, and `R_τ(λ)` is the supremum over
measurable fake-value maps of the expected current Lagrangian reward plus `R_{τ-1}` at the next
multiplier. `R_{τ-1}` takes values in `[0, τ-1]` on `λ ≥ 0`, so `toENNReal` is exact there. -/
noncomputable def bellmanValue (fmt : AuctionFormat) (D : Measure ValuePair) (ρL η μ : ℝ) : ℕ → ℝ → EReal
  | 0, _ => 0
  | τ + 1, lam =>
    ⨆ a : FakeValue,
      (((expValue D a : ℝ≥0∞) : EReal) -
          ((ENNReal.ofReal (μ * lam) * expPayO fmt D a : ℝ≥0∞) : EReal)) +
        ((∫⁻ v, (bellmanValue fmt D ρL η μ τ
            (nextPacing ρL η lam (roundPayL fmt (a.toFun v.2) v))).toENNReal ∂D : ℝ≥0∞) : EReal)

/-- The term maximized in Eq. (11):
`U_O(v̂_O) - μ λ P_O(v̂_O) + (1/η) E[G(λ + η (ρ_L - λ P_L(v̂_O, v_L, v_O))) - G(λ)]`. -/
noncomputable def potentialStep (fmt : AuctionFormat) (D : Measure ValuePair) (ρL η μ : ℝ) (G : ℝ → ℝ)
    (lam : ℝ) (a : FakeValue) : EReal :=
  (((expValue D a : ℝ≥0∞) : EReal) - ((ENNReal.ofReal (μ * lam) * expPayO fmt D a : ℝ≥0∞) : EReal)) +
    ((η⁻¹ : ℝ) : EReal) *
      (((∫⁻ v, ENNReal.ofReal (G (nextPacing ρL η lam (roundPayL fmt (a.toFun v.2) v))) ∂D : ℝ≥0∞) :
          EReal) - ((G lam : ℝ) : EReal))

/-- The two conditions of Lemma 5.1 for a potential `G` and a constant `A`, together with the
measurability of `G` on `[0,∞)` that makes the expectation in Eq. (11) well defined. -/
structure PotentialCriterion (fmt : AuctionFormat) (D : Measure ValuePair) (ρL η μ : ℝ) (G : ℝ → ℝ)
    (A : ℝ) : Prop where
  measurable : Measurable (fun x : Set.Ici (0 : ℝ) => G x)
  nonneg : ∀ lam, 0 ≤ lam → 0 ≤ G lam
  step : ∀ lam, 0 ≤ lam → (⨆ a : FakeValue, potentialStep fmt D ρL η μ G lam a) ≤ (A : EReal)

end BudgetedAuctionLearning.Robustness


