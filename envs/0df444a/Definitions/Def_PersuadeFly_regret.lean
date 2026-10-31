-- Prove2me | Definitions.Def_PersuadeFly_regret
-- name    : PersuadeFly_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:30:54.971959+00:00
-- url     : https://prove2.me/theorems/7bc2be4e-1492-46e4-9ac0-b87201b2b898
-- title:
--   Regret $\mathsf{Reg}_{\mathcal I}(\mathfrak a,T,\mu^*)$, (3)
-- statement:
--   The **regret** of a run along the realized path $(\omega_t,a_t)_{t\in[T]}$:
--   $$
--   \mathsf{Reg}_{\mathcal I}(\mathfrak a,T,\mu^*)=T\cdot\mathsf{OPT}(\mu^*)-\sum_{t\in[T]}v(\omega_t,a_t).
--   $$
--   It compares the sender's realized utility with the benchmark of a sender who knows $\mu^*$.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §2.3, eq. (3), p.19

import Mathlib
import Definitions.Def_PersuadeFly_opt

namespace PersuadeFly

/-- **Regret**, (3). Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §2.3, eq. (3), p.19:
`Reg(a, T, μ*) = T · OPT(μ*) − ∑_{t ∈ [T]} v(ω_t, a_t)`, a function of the realized path
`(ω_t, a_t)_{t ∈ [T]}`. -/
noncomputable def regret {Ω A : Type} [Fintype Ω] [Fintype A] (I : Instance Ω A) (μ : Ω → ℝ)
    (T : ℕ) (path : Fin T → Ω × A) : ℝ :=
  T * opt I μ - ∑ t : Fin T, I.v (path t).1 (path t).2

end PersuadeFly


