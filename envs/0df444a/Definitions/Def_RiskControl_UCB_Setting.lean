-- Prove2me | Definitions.Def_RiskControl_UCB_Setting
-- name    : RiskControl_UCB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:56.277989+00:00
-- url     : https://prove2.me/theorems/eb7d98eb-74f9-4d41-a95c-ee982207f012
-- title:
--   §2.1–2.2, p. 4 — the risk R(λ) of a nested family of set-valued predictors, the calibration set of (4) and λ̂
-- statement:
--   These are the objects of §2.1–2.2 of Bates, Angelopoulos, Lei, Malik and Jordan.
--
--   Let $(X, Y)$ take values in $\mathcal X \times \mathcal Y$ with law $P$, and let $\mathcal Z$ be a set of possible labels, so that a **set-valued predictor** is a map $\mathcal T : \mathcal X \to 2^{\mathcal Z}$. A family $\{\mathcal T_\lambda\}$ is indexed by $\lambda \in \overline{\mathbb R} = \mathbb R \cup \{\pm\infty\}$, and $L(y, S)$ is a loss on prediction sets.
--
--   1. **Risk.** The risk of $\mathcal T_\lambda$ is the expected loss
--   $$R(\lambda) = R(\mathcal T_\lambda) = \mathbb E\big[L(Y, \mathcal T_\lambda(X))\big] = \int L\big(y, \mathcal T_\lambda(x)\big)\, dP(x, y).$$
--   2. **Calibration set.** Given a closed index set $\Lambda \subseteq \overline{\mathbb R}$, a target level $\alpha \in \mathbb R$ and one realization $r(\lambda) = \widehat R^+(\lambda)$ of an upper confidence bound for the risk, the calibration set is
--   $$\mathcal C(\Lambda, r, \alpha) = \{\lambda \in \Lambda : r(\lambda') < \alpha \text{ for every } \lambda' \in \Lambda \text{ with } \lambda' \ge \lambda\}.$$
--   3. **Calibrated parameter.** $\hat\lambda = \inf \mathcal C(\Lambda, r, \alpha)$, the infimum taken in $\overline{\mathbb R}$, as in display (4) of the paper.
--
--   These are the objects about which Theorem 1 and Theorem A.1 are stated: UCB calibration returns $\mathcal T_{\hat\lambda}$.
--
--   **Formalization Note** The space of set-valued predictions $\mathcal Y'$ is taken to be $2^{\mathcal Z}$ (the paper uses $2^{\mathcal Y}$ for most of the work). The risk is the published `WassersteinDRO.Duality.nominalRisk`, a Bochner integral, which is $0$ for a non-integrable integrand; every statement about the risk therefore assumes the loss $(x,y) \mapsto L(y, \mathcal T_\lambda(x))$ is $P$-integrable for every $\lambda \in \Lambda$. The infimum is taken in the extended reals, so $\inf \emptyset = +\infty$ as on the page; $+\infty$ need not belong to $\Lambda$, so statements about $R(\hat\lambda)$ restrict to the event that the calibration set is nonempty, in which case $\hat\lambda \in \Lambda$ because $\Lambda$ is closed. The quantifier "$\forall \lambda' \ge \lambda$" of (4) ranges over $\Lambda$.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, §2.1–2.2, p. 4, (1)–(4)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_nominalRisk

open MeasureTheory

namespace RiskControl.UCB

/-- The risk `R(λ) = R(𝒯_λ) = 𝔼[L(Y, 𝒯_λ(X))]` of the set-valued predictor `𝒯_λ : 𝒳 → 2^𝒵`
under the law `P` of `(X, Y)` (Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3,
§2.1, p. 4). The space of set-valued predictions `𝒴′` is `Set 𝒵 = 2^𝒵`; the parameter `λ` lives
in `EReal = ℝ ∪ {±∞}`. It is the Bochner expectation `nominalRisk`, which is `0` for a
non-integrable integrand: every statement using `risk` assumes
`Integrable (fun p => L p.2 (T lam p.1)) P` for every `lam ∈ Λ`. -/
noncomputable def risk {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (P : Measure (𝒳 × 𝒴)) (L : 𝒴 → Set 𝒵 → ℝ) (T : EReal → 𝒳 → Set 𝒵) (lam : EReal) : ℝ :=
  WassersteinDRO.Duality.nominalRisk P (fun p => L p.2 (T lam p.1))

/-- The set in (4) (arXiv:2101.02703v3, §2.2, p. 4) for one realization `r : λ ↦ R̂⁺(λ)` of
the upper confidence bound: the `λ ∈ Λ` such that `R̂⁺(λ′) < α` for every `λ′ ∈ Λ` with
`λ′ ≥ λ`. -/
def calSet (Λ : Set EReal) (r : EReal → ℝ) (α : ℝ) : Set EReal :=
  {lam ∈ Λ | ∀ lam' ∈ Λ, lam ≤ lam' → r lam' < α}

/-- The calibrated parameter `λ̂ = inf {λ ∈ Λ : R̂⁺(λ′) < α, ∀ λ′ ≥ λ}` of (4)
(arXiv:2101.02703v3, §2.2, p. 4), an infimum in `EReal`. When `calSet Λ r α` is nonempty and
`Λ` is closed, `lambdaHat Λ r α ∈ Λ`. When it is empty, `sInf ∅ = ⊤` (the paper's
`inf ∅ = +∞`), which need not lie in `Λ`; statements about `R(λ̂)` therefore restrict to the
event that the set is nonempty. -/
noncomputable def lambdaHat (Λ : Set EReal) (r : EReal → ℝ) (α : ℝ) : EReal :=
  sInf (calSet Λ r α)

end RiskControl.UCB


