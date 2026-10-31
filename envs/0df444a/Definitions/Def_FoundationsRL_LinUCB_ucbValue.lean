-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_ucbValue
-- name    : FoundationsRL_LinUCB_ucbValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:57.817016+00:00
-- url     : https://prove2.me/theorems/6b477d54-96ec-4e3e-9ddc-665f180957ae
-- title:
--   Optimistic value over an ellipsoid
-- statement:
--   The **optimistic value** of a feature vector $v$ over the ellipsoid with center $\widehat\theta$, shape $S$ and squared radius $\rho^2$ is
--
--   $$
--   \max_{\theta\in\mathbb R^d:\ \|\theta-\widehat\theta\|_S^2\le\rho^2}\ \langle\theta,v\rangle.
--   $$
--
--   The maximum runs over all of $\mathbb R^d$, not over the parameter set $\Theta$. LinUCB selects the action that maximizes this value.
--
--   **Formalization Note** It is written as a real supremum. For $S=\widetilde\Sigma^t\succeq I$ and $\rho^2=16\beta+4>0$ the ellipsoid is nonempty and compact, so the supremum is a maximum.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, LinUCB algorithm box, p. 43

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_ellipNormSq

open Matrix

namespace FoundationsRL.LinUCB

/-- The optimistic value `max {⟨θ, v⟩ : θ ∈ ℝ^d, ∥θ − θ̂∥²_S ≤ ρ²}` of the feature vector `v`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, algorithm box, p. 43). The maximum runs over all of `ℝ^d`, not over `Θ`.

**Formalization Note.** Real `sSup`. LinUCB uses it with `S = Σ̃^t ⪰ I` and `ρ² = 16β + 4 > 0`:
the ellipsoid is then nonempty and compact, so the supremum is the book's maximum. -/
noncomputable def ucbValue {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (θhat : Fin d → ℝ) (ρsq : ℝ)
    (v : Fin d → ℝ) : ℝ :=
  sSup ((fun θ : Fin d → ℝ => θ ⬝ᵥ v) '' {θ | ellipNormSq S (θ - θhat) ≤ ρsq})

end FoundationsRL.LinUCB


