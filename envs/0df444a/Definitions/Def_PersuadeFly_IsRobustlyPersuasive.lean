-- Prove2me | Definitions.Def_PersuadeFly_IsRobustlyPersuasive
-- name    : PersuadeFly_IsRobustlyPersuasive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:30:56.601278+00:00
-- url     : https://prove2.me/theorems/61895698-2232-4741-96fd-db951de002e5
-- title:
--   $\beta$-robust persuasiveness (Definition 2)
-- statement:
--   Given $\beta\ge0$, a signaling algorithm is **$\beta$-robustly persuasive** if there are history-dependent sets $\mathcal C_t\subseteq\mathcal B_0$ such that
--
--   1. **Robustness:** $\sigma[h_t]\in\mathsf{Pers}(\mathcal C_t)$ for each $t\in[T]$ and every history $h_t$;
--   2. **Coverage:** for every $\mu^*\in\mathcal B_0$,
--   $$
--   \mathbf P_{\mu^*}\Big(\bigcap_{t\in[T]}\mathcal C_t\ni\mu^*\Big)\ge1-\beta .
--   $$
--
--   **Formalization Note** The true distribution is unknown, so coverage is required for every $\mu^*\in\mathcal B_0$, as in the supremum of Theorem 1 and the proof of Theorem 3 (p.41).
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Definition 2, p.17

import Mathlib
import Definitions.Def_PersuadeFly_persSet
import Definitions.Def_PersuadeFly_pathEventProb

namespace PersuadeFly

/-- **β-robust persuasiveness**, Definition 2. Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Definition 2, p.17: given `β ≥ 0`, a signaling
algorithm is β-robustly persuasive if there are history-dependent sets `C_t ⊆ B₀` with
1. (robustness) `σ[h_t] ∈ Pers(C_t)` for each `t ∈ [T]`;
2. (coverage) `P_{μ*}(∩_{t ∈ [T]} C_t ∋ μ*) ≥ 1 − β`.

**Formalization Note** `μ*` is unknown, so coverage is required for every `μ* ∈ B₀`, as the supremum
over `B₀` in Theorem 1 and the proof of Theorem 3 ("for all μ ∈ B₀", p.41) read it. Robustness is
required after every history. -/
def IsRobustlyPersuasive {Ω A : Type} [Fintype Ω] [Fintype A] (I : Instance Ω A) (T : ℕ)
    (alg : (t : ℕ) → (Fin t → Ω × A) → Ω → A → ℝ) (β : ℝ) : Prop :=
  0 ≤ β ∧ ∃ C : (t : ℕ) → (Fin t → Ω × A) → Set (Ω → ℝ),
    (∀ t h, C t h ⊆ I.B0) ∧
    (∀ t < T, ∀ h : Fin t → Ω × A, alg t h ∈ persSet I (C t h)) ∧
    ∀ μ ∈ I.B0, 1 - β ≤ pathEventProb μ alg T {path | ∀ t : Fin T, μ ∈ C t (historyAt path t)}

end PersuadeFly


