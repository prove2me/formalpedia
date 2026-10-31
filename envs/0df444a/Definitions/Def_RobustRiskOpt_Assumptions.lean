-- Prove2me | Definitions.Def_RobustRiskOpt_Assumptions
-- name    : RobustRiskOpt_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:59.328135+00:00
-- url     : https://prove2.me/theorems/5406bc05-d649-423e-8d5e-3203a312e7c3
-- title:
--   $\rho=\mathrm{VaR}_p$, Assumption G and Assumption V
-- statement:
--   The objective is the **Value-at-Risk** at level $p\in(0,1)$, $\rho=\mathrm{VaR}_p$, where $\mathrm{VaR}_p(Y)=\inf\{x\in\mathbb R:\mathbb P(Y\le x)\ge p\}$.
--
--   **Assumption G.** $\mathcal G$ is given by (7), where $\mathbb E[\gamma(X)]<\infty$ and $\mathcal G\ne\emptyset$; the distribution measure $\mu_X$ of $X$ has a positive density on its support, which is a convex subset of $\mathbb R^n$; and $(\mathcal Z,\pi)$ is one of the uncertainty models.
--
--   **Assumption V.** With $\rho=\mathrm{VaR}_p$,
--
--   $$
--   \operatorname{ess\,sup}(v)<\rho(X;\mathcal G)<\rho(w(X)),
--   $$
--
--   and $\gamma$ is bounded from above. The essential supremum is taken under $\mu_X$.
--
--   The first inequality says that the lower bound $v$ is not too large. The second says that the problem is not solved by the largest position $g=w$.
--
--   **Formalization Note** The positive density on a convex support is encoded as the existence of a convex set $S$ such that $\mu_X$ and Lebesgue measure restricted to $S$ are mutually absolutely continuous. The choice of $(\mathcal Z,\pi)$ is an argument of Theorem 1 and not a field of `AssumptionG`. The atomlessness of §2.1 is not assumed, since the density implies it. The bound on $\gamma$ is required only $\mu_X$-a.e. `VaR` is the published `ESAxioms.Characterization.VaR`, cast to `EReal`.
-- source:
--   Embrechts–Schied–Wang, Robustness in the Optimization of Risk Measures, arXiv:1809.09268v3, 11 Feb 2021, p.11 (VaR); Assumption G and Assumption V, p.13; the proof of Theorem 1, p.28 (essential suprema under μ_X)

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting
import Definitions.Def_RobustRiskOpt_Admissible

open MeasureTheory
open scoped ENNReal

namespace RobustRiskOpt

open ESAxioms.Characterization

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- The clause of Assumption G, p.13 (Embrechts–Schied–Wang, arXiv:1809.09268v3): "the distribution
measure of `X` has a positive density on its support, which is a convex subset of `ℝⁿ`".

**Formalization Note** The positive density on `S` is the mutual absolute continuity of `μ` and
the restriction of Lebesgue measure to `S`: the density `dμ/dx` exists, vanishes a.e. off `S` and
is positive a.e. on `S`. A convex `S` differs from its closure by a Lebesgue-null set, so it does
not matter whether "support" means the closed support or the set where the density is positive. -/
def HasConvexSupportDensity (μ : Measure (E n)) : Prop :=
  ∃ S : Set (E n), Convex ℝ S ∧ μ ≪ volume.restrict S ∧ volume.restrict S ≪ μ

/-- The objective functional `ρ = VaR_p`, p.11 (Embrechts–Schied–Wang, arXiv:1809.09268v3), with
values in `EReal`. `VaR` is the published `ESAxioms.Characterization.VaR`, which is
`inf {x ∈ ℝ : ℙ(Y ≤ x) ≥ p}`. For `p ∈ (0, 1)` and measurable `Y` this set is nonempty and
bounded below, so the real infimum is the true quantile. -/
noncomputable def varObj (P : Measure Ω) (p : ℝ) : (Ω → ℝ) → EReal :=
  fun Y => ((VaR P p Y : ℝ) : EReal)

/-- Assumption G, p.13 (Embrechts–Schied–Wang, arXiv:1809.09268v3): `𝒢` is given by (7), where
`𝔼[γ(X)] < ∞` and `𝒢 ≠ ∅`, and `μ_X` has a positive density on its convex support. The fourth
clause of Assumption G, the choice of `(𝒵, π)`, is the `UncertaintyModel` argument of Theorem 1.

**Formalization Note** The atomlessness of `(Ω, ℱ, ℙ)` (§2.1, p.5) is not assumed separately: it
follows from the density of `X`. -/
structure AssumptionG (P : Measure Ω) (X : Ω → E n) (v : E n → EReal) (w γ : E n → ℝ) (x₀ : ℝ) :
    Prop where
  /-- `𝔼[γ(X)] < ∞`. -/
  lintegral_lt_top : ∫⁻ x, ENNReal.ofReal (γ x) ∂(P.map X) < ⊤
  /-- `𝒢 ≠ ∅`. -/
  nonempty : (admissible P X v w γ x₀).Nonempty
  /-- `μ_X` has a positive density on its convex support. -/
  density : HasConvexSupportDensity (P.map X)

/-- Assumption V, p.13 (Embrechts–Schied–Wang, arXiv:1809.09268v3), for `ρ = VaR_p`:
`ess-sup(v) < ρ(X; 𝒢) < ρ(w(X))` and `γ` is bounded from above.

**Formalization Note** The essential supremum of `v` is taken under `μ_X`, as stated in the proof
of Theorem 1, p.28; it is an `EReal`, `⊥` when `v = −∞` a.e. The bound on `γ` is required only
`μ_X`-a.e., which is implied by the printed pointwise bound. -/
structure AssumptionV (P : Measure Ω) (p : ℝ) (X : Ω → E n) (v : E n → EReal) (w γ : E n → ℝ)
    (x₀ : ℝ) : Prop where
  /-- `ess-sup(v) < ρ(X; 𝒢)`. -/
  essSup_lt : essSup v (P.map X) < rhoInf (varObj P p) X (admissible P X v w γ x₀)
  /-- `ρ(X; 𝒢) < ρ(w(X))`. -/
  lt_var_w : rhoInf (varObj P p) X (admissible P X v w γ x₀) < varObj P p (w ∘ X)
  /-- `γ` is bounded from above. -/
  bddAbove : ∃ u : ℝ, ∀ᵐ x ∂(P.map X), γ x ≤ u

end RobustRiskOpt


