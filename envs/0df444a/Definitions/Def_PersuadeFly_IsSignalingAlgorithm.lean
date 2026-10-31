-- Prove2me | Definitions.Def_PersuadeFly_IsSignalingAlgorithm
-- name    : PersuadeFly_IsSignalingAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:06.619562+00:00
-- url     : https://prove2.me/theorems/0ff561bc-234a-4c80-b175-c52e7684ef83
-- title:
--   Signaling algorithm
-- statement:
--   A **signaling algorithm** with horizon $T$ specifies, at each time $t\in[T]$ and after each history $h_t$, a mechanism $\sigma[h_t]\in\mathcal S$: given the state $\omega_t$, the recommendation is drawn from $\sigma[h_t](\omega_t,\cdot)\in\Delta(A)$.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §2, p.13

import Mathlib
import Definitions.Def_PersuadeFly_IsMechanism

namespace PersuadeFly

/-- **Signaling algorithm.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §2, p.13: at each `t ∈ [T]`, after any history `h_t` and state
`ω_t`, the algorithm specifies a distribution `σ(h_t, ω_t, ·) ∈ Δ(A)` over recommendations. -/
def IsSignalingAlgorithm {Ω A : Type} [Fintype A] (T : ℕ)
    (alg : (t : ℕ) → (Fin t → Ω × A) → Ω → A → ℝ) : Prop :=
  ∀ t < T, ∀ h : Fin t → Ω × A, IsMechanism (alg t h)

end PersuadeFly


