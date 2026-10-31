-- Prove2me | Definitions.Def_PersuadeFly_opt
-- name    : PersuadeFly_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:30:06.967632+00:00
-- url     : https://prove2.me/theorems/7da6aee1-2f07-4853-9f8b-414fc80916c3
-- title:
--   The benchmark $\mathsf{OPT}(\mu)$, (2)
-- statement:
--   The optimal value of the persuasion linear program (2):
--   $$
--   \mathsf{OPT}(\mu)=\max_\sigma V(\mu,\sigma)\quad\text{subject to }\sigma\in\mathsf{Pers}(\mu).
--   $$
--   This is the sender's per-round utility when $\mu$ is known, and $T\cdot\mathsf{OPT}(\mu^*)$ is the benchmark of the regret.
--
--   **Formalization Note** Written as a supremum, as on p.23. For $\mu\in\Delta(\Omega)$ the set $\mathsf{Pers}(\mu)$ is a nonempty compact polytope (it contains the full-information mechanism) and $V(\mu,\cdot)$ takes values in $[0,1]$ there, so the supremum is a maximum.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §2.1, eq. (2), p.15; §4, p.23

import Mathlib
import Definitions.Def_PersuadeFly_pers
import Definitions.Def_PersuadeFly_value

namespace PersuadeFly

/-- **The benchmark `OPT(μ)`**, (2). Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §2.1, eq. (2), p.15, and §4, p.23:
`OPT(μ) = max_σ V(μ, σ)` subject to `σ ∈ Pers(μ)`, written on p.23 as `sup_{σ ∈ Pers(μ)} V(μ, σ)`.

**Formalization Note** A real `sSup` over the persuasive mechanisms only. For `μ ∈ Δ(Ω)` this set
contains the full-information mechanism and `V` takes values in `[0, 1]` on it, so the supremum is of
a nonempty bounded set (and it is attained, `Pers(μ)` being a compact polytope). -/
noncomputable def opt {Ω A : Type} [Fintype Ω] [Fintype A] (I : Instance Ω A) (μ : Ω → ℝ) : ℝ :=
  sSup (value I μ '' pers I μ)

end PersuadeFly


