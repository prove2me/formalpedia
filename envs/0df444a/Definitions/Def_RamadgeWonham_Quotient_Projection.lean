-- Prove2me | Definitions.Def_RamadgeWonham_Quotient_Projection
-- name    : RamadgeWonham_Quotient_Projection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:39:00.39126+00:00
-- url     : https://prove2.me/theorems/2524851e-0378-4279-93f6-dd5e0c8c1b39
-- title:
--   Projection π: 𝒮 → 𝒮̂ between supervisors (§8, p. 219)
-- statement:
--   Let $\mathcal S = (S, \phi)$ and $\hat{\mathcal S} = (\hat S, \hat\phi)$ be supervisors, with $S = (X, \Sigma, \xi, x_0, X_m)$ and $\hat S = (\hat X, \Sigma, \hat\xi, \hat x_0, \hat X_m)$. A total function $\pi : X \to \hat X$ is a **projection** from $\mathcal S$ to $\hat{\mathcal S}$, written $\pi : \mathcal S \to \hat{\mathcal S}$, if
--
--   1. $\pi$ is surjective;
--   2. $\pi(x_0) = \hat x_0$ and $X_m = \pi^{-1}(\hat X_m)$;
--   3. $\hat\xi(\sigma, \pi(x)) = \pi(\xi(\sigma, x))$ for every pair $(\sigma, x)$ at which $\xi(\sigma, x)$ is defined;
--   4. $\hat\phi \circ \pi = \phi$.
--
--   $\hat S$ is then called the **quotient** of $S$ under $\pi$. Condition 3 is only a partial commutation: $\hat\xi$ may be defined where $\xi$ is not.
--
--   A projection lumps the states of a supervisor without changing its control action; Proposition 8.1 shows it preserves all closed-loop languages and completeness.
--
--   **Formalization Note** Condition 4 compares the maps $X \to \{0,1\}^{\Sigma_c}$; their extensions to $\Sigma$ agree automatically off $\Sigma_c$, so this is the page's $\hat\phi \circ \pi = \phi$ for $\phi : X \to \{0,1\}^\Sigma$.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 219, §8, definition of projection (i)-(iv) and footnotes 6, 7

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Supervisor

namespace RamadgeWonham.Quotient

variable {α : Type} {Ec : Set α}

/-- A projection `π : 𝒮 → 𝒮̂` between supervisors `𝒮 = (S, φ)`, `S = (X, Σ, ξ, x₀, X_m)` and
`𝒮̂ = (Ŝ, φ̂)`, `Ŝ = (X̂, Σ, ξ̂, x̂₀, X̂_m)` (§8, p. 219): a total function `π : X → X̂` such that
(i) `π` is surjective; (ii) `π(x₀) = x̂₀` and `X_m = π⁻¹(X̂_m)`; (iii) `ξ̂(σ, π(x)) = π(ξ(σ, x))`
for all `(σ, x)` where `ξ(σ, x)` is defined (only "partially commutative", footnote 7); and
(iv) `φ̂ ∘ π = φ`. -/
def IsProjection (𝒮 𝒮h : Shared.Supervisor α Ec) (π : 𝒮.S.Q → 𝒮h.S.Q) : Prop :=
  Function.Surjective π ∧
  (π 𝒮.S.q0 = 𝒮h.S.q0 ∧ 𝒮.S.Qm = π ⁻¹' 𝒮h.S.Qm) ∧
  (∀ (σ : α) (x x' : 𝒮.S.Q), 𝒮.S.δ σ x = some x' → 𝒮h.S.δ σ (π x) = some (π x')) ∧
  (∀ x : 𝒮.S.Q, 𝒮h.φ (π x) = 𝒮.φ x)

end RamadgeWonham.Quotient


