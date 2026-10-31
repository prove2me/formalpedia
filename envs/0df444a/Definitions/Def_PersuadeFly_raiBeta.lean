-- Prove2me | Definitions.Def_PersuadeFly_raiBeta
-- name    : PersuadeFly_raiBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:30:55.086158+00:00
-- url     : https://prove2.me/theorems/9adadd55-e9b9-4636-b8a5-569725cddae8
-- title:
--   The coverage failure $\beta$ of Rai
-- statement:
--   The worst-case probability that some confidence set of Rai misses the true distribution:
--   $$
--   \beta=\sup_{\mu^*\in\mathcal B_0}\mathbf P_{\mu^*}\Big(\bigcap_{t\in[T]}\mathcal B_t\not\ni\mu^*\Big).
--   $$
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Theorem 1, p.22

import Mathlib
import Definitions.Def_PersuadeFly_Instance
import Definitions.Def_PersuadeFly_raiSet
import Definitions.Def_PersuadeFly_pathEventProb

namespace PersuadeFly

/-- **The coverage failure `β` of Theorem 1.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Theorem 1, p.22:
`β = sup_{μ* ∈ B₀} P_{μ*}(∩_{t ∈ [T]} B_t ∌ μ*)`, the largest probability that some confidence set
`B_t` of Rai misses `μ*`.

**Formalization Note** A real `sSup` over `B₀`; the probabilities lie in `[0, 1]`, so the set is
bounded, and it is nonempty since `γ₀ ∈ B₀`. -/
noncomputable def raiBeta {Ω A : Type} [Fintype Ω] [DecidableEq Ω] [Fintype A]
    (I : Instance Ω A) (γ0 : Ω → ℝ) (C0 : Set (Ω → ℝ)) (ε : ℕ → ℝ) (T : ℕ)
    (alg : (t : ℕ) → (Fin t → Ω × A) → Ω → A → ℝ) : ℝ :=
  sSup ((fun μ => pathEventProb μ alg T
    {path | ∃ t : Fin T, μ ∉ raiSet γ0 C0 ε t (historyAt path t)}) '' I.B0)

end PersuadeFly


