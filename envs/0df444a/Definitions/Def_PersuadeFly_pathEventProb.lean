-- Prove2me | Definitions.Def_PersuadeFly_pathEventProb
-- name    : PersuadeFly_pathEventProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:30:05.556112+00:00
-- url     : https://prove2.me/theorems/056273af-b3ea-4d52-9fc9-361508ba0bc5
-- title:
--   The probability $\mathbf P_{\mu^*}(E)$ of an event of paths
-- statement:
--   For a set $E$ of paths of length $T$, $\mathbf P_{\mu^*}(E)$ is the sum of the path law over the paths in $E$.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Definition 2, p.17; Theorems 1–2, pp.22, 27

import Mathlib
import Definitions.Def_PersuadeFly_pathProb

namespace PersuadeFly

/-- **`P_{μ*}(E)` for an event `E` of paths.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Definition 2, p.17, and Theorems 1–2: the probability
of a set `E` of paths `(ω_t, a_t)_{t ∈ [T]}` under the law `pathProb`, i.e. the sum of `pathProb` over `E`. -/
noncomputable def pathEventProb {Ω A : Type} [Fintype Ω] [Fintype A] (μ : Ω → ℝ)
    (alg : (t : ℕ) → (Fin t → Ω × A) → Ω → A → ℝ) (T : ℕ) (E : Set (Fin T → Ω × A)) : ℝ :=
  ∑ path : Fin T → Ω × A, E.indicator (pathProb μ alg T) path

end PersuadeFly


