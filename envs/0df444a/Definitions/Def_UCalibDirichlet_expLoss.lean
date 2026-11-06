-- Prove2me | Definitions.Def_UCalibDirichlet_expLoss
-- name    : UCalibDirichlet_expLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:15.026095+00:00
-- url     : https://prove2.me/theorems/b8185420-c40a-4cec-be05-2f5e44faa2e3
-- title:
--   Expected loss $\mathbb E_{P\sim\mu}[\ell(P,i)]$ of a random forecast
-- statement:
--   For a law $\mu$ of a random forecast $P\in\Delta_K$ and an outcome $i$, the expected loss is
--   $$\mathbb E_{P\sim\mu}[\ell(P,i)]=\mathbb E_\mu\big[\ell(\cdot,i)^+\big]-\mathbb E_\mu\big[\ell(\cdot,i)^-\big]\in[-\infty,+\infty],$$
--   the expectation of the extended-real random variable $p\mapsto\ell(p,i)$. For a proper loss with finite Bayes risk, $\ell(e_i,i)$ is a real number and $\ell(p,i)\ge\ell(e_i,i)$ for every $p\in\Delta_K$ (propriety with $q=e_i$), so for a probability law on $\Delta_K$ the negative part has finite expectation and the expected loss lies in $\mathbb R\cup\{+\infty\}$.
--
--   **Formalization Note** This is the published extended-real expectation `BauerleRiederMDP.TransactionCosts.eexp` applied to $p\mapsto\ell(p,i)$; both parts are lower Lebesgue integrals, so the value $+\infty$ is kept (a Bochner integral would replace it by $0$) and no integrability hypothesis is needed.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), display (2), p.1; Lemmas 1.3–1.4, p.4

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_eexp

open MeasureTheory

namespace UCalibDirichlet

/-- **Expected loss of a random forecast, `E_{P∼μ}[ℓ(P, i)]`.** Frongillo, Luo, Mehta & Schneider
(manuscript, STOC 2027 submission), display (2), p.1, and Lemmas 1.3–1.4, p.4: the expected loss
of a forecast `P` drawn from a law `μ` on `Δ_K` when the outcome is `i`.

`expLoss ℓ μ i = E_μ[ℓ(·, i)⁺] − E_μ[ℓ(·, i)⁻] ∈ [−∞, +∞]`, the published expectation `eexp` of the
extended-real random variable `p ↦ ℓ(p, i)`.

**Formalization Note.** `eexp` integrates the positive and negative parts as lower Lebesgue
integrals, so the value `+∞` is kept (a Bochner integral of `(ℓ p i).toReal` would turn it into
`0`) and no integrability side condition is needed. For a proper loss with finite Bayes risk and a
probability law `μ` carried by `Δ_K`, propriety at `q = e_i` gives `ℓ(p, i) ≥ ℓ(e_i, i) ∈ ℝ` on
`Δ_K`, so the negative part is bounded and the difference is never `⊤ − ⊤`. Lower integrals are
unchanged when the integrand is changed on a `μ`-null set. -/
noncomputable def expLoss {K : ℕ} (ℓ : (Fin K → ℝ) → Fin K → EReal) (μ : Measure (Fin K → ℝ))
    (i : Fin K) : EReal :=
  BauerleRiederMDP.TransactionCosts.eexp μ (fun p => ℓ p i)

end UCalibDirichlet


