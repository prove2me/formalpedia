-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_LinearSetting
-- name    : FoundationsRL_LinUCB_LinearSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:17.240629+00:00
-- url     : https://prove2.me/theorems/8289c69f-7efc-4b02-ab09-0a20ac26ac93
-- title:
--   Standing assumptions of the linear model (§§3.1–3.2)
-- statement:
--   The **linear setting** collects the assumptions of §3.1 and §3.2 on $(M^\star,\Theta,\phi,\theta^\star)$:
--
--   1. $\Theta\subseteq B_2^d(1)$ and $\phi:\mathcal X\times\Pi\to B_2^d(1)$;
--   2. $\phi$ is measurable;
--   3. every function of the class takes values in $[0,1]$, and $r\in[0,1]$ almost surely under every $M^\star(\cdot\mid x,\pi)$;
--   4. $\theta^\star\in\Theta$ and $f^\star(x,\pi)=\langle\theta^\star,\phi(x,\pi)\rangle$ for all $x,\pi$.
--
--   Every result of the mission about linear models is stated under these assumptions.
--
--   **Formalization Note** Measurability of $\phi$ is the field's standing convention, and is automatic for finite $\mathcal X$ and $\Pi$ with the discrete σ-algebra. Boundedness of $\Theta$ and $\phi$ alone gives values in $[-1,1]$, so item 3 is a separate assumption, stated on p. 41.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §3.1, p. 41 and §3.2, p. 43

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_meanReward

open MeasureTheory ProbabilityTheory Matrix

namespace FoundationsRL.LinUCB

/-- The standing assumptions on the linear model (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §3.1, p. 41, and §3.2, p. 43):

* `Θ ⊆ B^d_2(1)` and `ϕ : X × Π → B^d_2(1)`, where `v ∈ B^d_2(1)` is written `v ⬝ᵥ v ≤ 1`;
* every `f ∈ F` takes values in `[0, 1]`, and `r ∈ [0, 1]` almost surely under every `M⋆(· | x, π)`;
* `f⋆ ∈ F`: the true parameter `θstar ∈ Θ` satisfies `f⋆(x, π) = ⟨θ⋆, ϕ(x, π)⟩`.

**Formalization Note.** `ϕ` is jointly measurable, the field's standing convention, without which
`f(x^t, π^t)` is not a random variable; it is automatic for finite `X` and `Π` with the discrete
σ-algebra. `Θ` is an arbitrary set. -/
structure LinearSetting {X Act : Type*} [MeasurableSpace X] [MeasurableSpace Act] {d : ℕ}
    (Mstar : Kernel (X × Act) ℝ) (Θ : Set (Fin d → ℝ)) (ϕ : X → Act → Fin d → ℝ)
    (θstar : Fin d → ℝ) : Prop where
  theta_ball : ∀ θ ∈ Θ, θ ⬝ᵥ θ ≤ 1
  feature_ball : ∀ x a, ϕ x a ⬝ᵥ ϕ x a ≤ 1
  measurable_feature : Measurable fun z : X × Act => ϕ z.1 z.2
  class_range : ∀ θ ∈ Θ, ∀ x a, θ ⬝ᵥ ϕ x a ∈ Set.Icc (0 : ℝ) 1
  reward_range : ∀ z, Mstar z (Set.Icc (0 : ℝ) 1)ᶜ = 0
  star_mem : θstar ∈ Θ
  realizable : ∀ x a, meanReward Mstar x a = θstar ⬝ᵥ ϕ x a

end FoundationsRL.LinUCB


