-- Prove2me | Definitions.Def_MomentSearch_correctionNorm
-- name    : MomentSearch_correctionNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:09:55.125359+00:00
-- url     : https://prove2.me/theorems/0689976c-4565-48d0-8fc4-2d6acff2e40a
-- title:
--   Value $\gamma^*(m,m_0)$ of the correction problem
-- statement:
--   The **value of the correction problem** for peak positions $m,m_0\in[n]_0$ is
--
--   $$
--   \gamma^*(m,m_0) := \inf\bigl\{\|a\|_1 : a\in\mathbb R^n \text{ satisfies Equation (7)}\bigr\},
--   $$
--
--   the smallest $\ell_1$-norm of a signed correction. Small values of $\gamma^*$ yield two distributions with the same first $k$ moments and large, separated peaks.
--
--   **Formalization Note** A real infimum over the set of norms $\sum_t|a_t|$ of solutions. The set is bounded below by $0$ and, for $m,m_0\in[n]_0$, nonempty ($\delta_m-\delta_{m_0}$ is a solution), so this is the true infimum and lies in $[0,2]$.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, eq. (8), p.22 (PDF p.24); = eq. (4), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_MomentSearch_SolvesCorrection

namespace MomentSearch

/-- The value of the correction problem
`γ*(m, m₀) := inf { ‖a‖₁ : a ∈ ℝ^n satisfies Equation (7) }`
(Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, eq. (8), p.22 (PDF p.24); = eq. (4), p.11 (PDF p.13)).

**Formalization Note.** A real `sInf` over the set of `ℓ₁`-norms `∑_t |a_t|` of solutions. The
set is bounded below by `0`, and for `m, m₀ ∈ [n]₀` it is nonempty (`a = δ_m − δ_{m₀}` is a
solution), so this is the true infimum and lies in `[0, 2]`; Lemma 12 states that it is attained. -/
noncomputable def correctionNorm (n k m m₀ : ℕ) : ℝ :=
  sInf {s : ℝ | ∃ a : Fin n → ℝ, SolvesCorrection n k m m₀ a ∧ s = ∑ t : Fin n, |a t|}

end MomentSearch


