-- Prove2me | Definitions.Def_UCalibDirichlet_IsProperLoss
-- name    : UCalibDirichlet_IsProperLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:08.729591+00:00
-- url     : https://prove2.me/theorems/326f68e4-7fd0-489c-8c92-3601ef1ac3bf
-- title:
--   Proper loss $\ell:\Delta_K\times[K]\to\mathbb R\cup\{+\infty\}$
-- statement:
--   A loss $\ell:\Delta_K\times[K]\to\mathbb R\cup\{+\infty\}$ is **proper** if truthfully reporting the distribution of the outcome minimizes the expected loss:
--   $$\mathbb E_{i\sim q}[\ell(q,i)]\le\mathbb E_{i\sim q}[\ell(p,i)]\qquad\text{for all }p,q\in\Delta_K,$$
--   where $\mathbb E_{i\sim q}[\ell(p,i)]=\sum_{i=1}^K q_i\,\ell(p,i)$.
--
--   Proper losses are the losses for which U-calibration asks for low regret simultaneously.
--
--   **Formalization Note** Losses take values in `EReal`; the predicate also requires that $\ell$ never takes the value $-\infty$ on the simplex. In the expected loss an outcome of probability $0$ contributes $0\cdot(+\infty)=0$. The loss is a function on all of $\mathbb R^K$, and only its values on $\Delta_K$ are constrained.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), §1, display (1), p.1

import Mathlib

namespace UCalibDirichlet

/-- **Proper loss, display (1).** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), §1, p.1: "Given a *proper* loss `ℓ : Δ_K × [K] → ℝ ∪ {+∞}`, that is, a loss such that
truthfully reporting the ground truth minimizes the expected loss:
`E_{i∼q}[ℓ(q, i)] ≤ E_{i∼q}[ℓ(p, i)]`, `∀ p, q ∈ Δ_K`. (1)"

`IsProperLoss ℓ` says that on the simplex `Δ_K = stdSimplex ℝ (Fin K)`
1. `ℓ` never takes the value `−∞` (its values lie in `ℝ ∪ {+∞}`), and
2. for all `p, q ∈ Δ_K`, `∑_i q_i ℓ(q, i) ≤ ∑_i q_i ℓ(p, i)`.

**Formalization Note.** Losses are `EReal`-valued; `E_{i∼q}[ℓ(p, i)]` is the finite sum
`∑_i q_i ℓ(p, i)` in `EReal`, where `0 · (+∞) = 0` (an outcome of probability zero contributes
nothing). `ℓ` is a total function on `Fin K → ℝ`; its values off the simplex are irrelevant and
constrained by nothing. Labels `[K]` are `Fin K` (0-based). -/
def IsProperLoss {K : ℕ} (ℓ : (Fin K → ℝ) → Fin K → EReal) : Prop :=
  (∀ p ∈ stdSimplex ℝ (Fin K), ∀ i, ℓ p i ≠ ⊥) ∧
    ∀ p ∈ stdSimplex ℝ (Fin K), ∀ q ∈ stdSimplex ℝ (Fin K),
      ∑ i, (q i : EReal) * ℓ q i ≤ ∑ i, (q i : EReal) * ℓ p i

end UCalibDirichlet


