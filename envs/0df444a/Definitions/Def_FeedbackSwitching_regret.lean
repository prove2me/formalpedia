-- Prove2me | Definitions.Def_FeedbackSwitching_regret
-- name    : FeedbackSwitching_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:12.597313+00:00
-- url     : https://prove2.me/theorems/5f11a946-7a7a-4e09-ae79-c396168d2069
-- title:
--   Expected regret with switching costs $\mathrm{Reg}_T$ (Eq. (12))
-- statement:
--   Let a policy with coins $\omega\sim\mu$ play against the loss sequence $\ell$ on the feedback graph $G$, producing actions $I_1,\dots,I_T$. The **number of switches** and the **expected regret** are
--   $$
--   N_T=\sum_{t=2}^{T}\mathbf 1\{I_t\neq I_{t-1}\},\qquad
--   \mathrm{Reg}_T=\mathbb E\Big[\sum_{t=1}^{T}\ell_t(I_t)+N_T\Big]-\min_{i\in[K]}\sum_{t=1}^{T}\ell_t(i).
--   $$
--   The expectation is over the learner's internal randomization only, because the adversary is oblivious. Each switch costs one unit of loss; the first action is free.
--
--   **Formalization Note** The play is defined by recursion on the history: round $t$'s action is the policy's rule applied to the history of rounds $<t$, whose feedback entries are the masked loss vectors. The minimum is an infimum over the finite type `Fin K`, attained for $K\ge1$. The expectation is a Bochner integral; every algorithm statement of the mission asserts integrability of the integrand, and for a `Learner` it holds automatically.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Eq. (12), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_FeedbackSwitching_Policy

open MeasureTheory
open scoped Classical

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

The loss vector of round `t` of a sequence of `T` rounds, `0` after the horizon. -/
noncomputable def lossAt {K T : ℕ} (ℓ : Fin T → Fin K → ℝ) (t : ℕ) : Fin K → ℝ :=
  if h : t < T then ℓ ⟨t, h⟩ else 0

/-- The history of the first `t` rounds when policy `L` with coins `ω` plays against `ℓ` on the
feedback graph `G`: round `s` records the action `I_s` and its feedback `reveal G ℓ_s I_s`. -/
noncomputable def history {K T : ℕ} (G : FeedbackGraph K) (L : Policy K) (ℓ : Fin T → Fin K → ℝ)
    (ω : L.Ω) : (t : ℕ) → Hist K t
  | 0 => Fin.elim0
  | t + 1 =>
      Fin.snoc (α := fun _ => Fin K × (Fin K → ℝ)) (history G L ℓ ω t)
        (L.act t (history G L ℓ ω t) ω,
          reveal G (lossAt ℓ t) (L.act t (history G L ℓ ω t) ω))

/-- The action `I_t` of round `t` (0-based). -/
noncomputable def action {K T : ℕ} (G : FeedbackGraph K) (L : Policy K) (ℓ : Fin T → Fin K → ℝ)
    (ω : L.Ω) (t : ℕ) : Fin K :=
  L.act t (history G L ℓ ω t) ω

/-- Loss of an action path over `T` rounds: `∑_{t=1}^T ℓ_t(X_t)`. -/
def pathLoss {K T : ℕ} (ℓ : Fin T → Fin K → ℝ) (X : ℕ → Fin K) : ℝ :=
  ∑ t : Fin T, ℓ t (X t)

/-- Number of switches of an action path over `T` rounds, `N_T = ∑_{t=2}^T 1{X_t ≠ X_{t−1}}`
(Eq. (12)); 0-based, the pairs `(t, t + 1)` with `t + 1 < T`. The first action is free. -/
noncomputable def pathSwitches (T : ℕ) {K : ℕ} (X : ℕ → Fin K) : ℝ :=
  ∑ t ∈ Finset.range (T - 1), if X (t + 1) ≠ X t then (1 : ℝ) else 0

/-- **Expected regret with switching costs** (Eq. (12), p.13 = PDF p.15):
`Reg_T = E[∑_{t=1}^T ℓ_t(I_t) + N_T] − min_{i∈[K]} ∑_{t=1}^T ℓ_t(i)`; the expectation is over the
learner's internal randomization only (the adversary is oblivious).

**Formalization Note.** The minimum over `i ∈ [K]` is `⨅ i`, a minimum over the finite type
`Fin K` (attained when `K ≥ 1`). The expectation is the Bochner integral over the coins; it is
the true expectation when the cost is integrable, which holds for every `Learner` and is
asserted for every algorithm of the mission. -/
noncomputable def regret {K T : ℕ} (G : FeedbackGraph K) (L : Policy K)
    (ℓ : Fin T → Fin K → ℝ) : ℝ :=
  (∫ ω, (pathLoss ℓ (action G L ℓ ω) + pathSwitches T (action G L ℓ ω)) ∂L.μ)
    - ⨅ i : Fin K, ∑ t : Fin T, ℓ t i

end FeedbackSwitching


