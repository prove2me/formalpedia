-- Prove2me | Definitions.Def_RobustCtxPricing_Density
-- name    : RobustCtxPricing_Density
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:07.446361+00:00
-- url     : https://prove2.me/theorems/055a4207-6a07-4633-b5c4-5789a34c45c8
-- title:
--   Densities over $\Theta$ — uniform density, $\epsilon$-window median (3), Update-Density (Algorithm 3)
-- statement:
--   The algorithm keeps a density $\mu_t$ over $\Theta$. This module defines the three density operations of §3.1.
--
--   1. **Uniform density.** $\mu_1(\theta)=1/\mathrm{vol}(\Theta)$ for $\theta\in\Theta$ and $0$ outside.
--   2. **$\epsilon$-window median (Definition 3.2).** Given a density $\mu_t$ and a direction $u_t$, a value $m_t$ is an $\epsilon$-window median of $\mu_t$ in direction $u_t$ if
--   $$
--   \int_\Theta\mu_t(\theta)\,\mathbb I\{\langle u_t,\theta\rangle\le m_t-\epsilon/2\}\,d\theta=\int_\Theta\mu_t(\theta)\,\mathbb I\{\langle u_t,\theta\rangle\ge m_t+\epsilon/2\}\,d\theta. \qquad (3)
--   $$
--   3. **Update-Density (Algorithm 3).** If $Y_t=1$, the density is multiplied by $\tfrac32$ on $\{\langle u_t,\theta\rangle\ge m_t+\epsilon/2\}$, by $1$ on the window $\{|\langle u_t,\theta\rangle-m_t|\le\epsilon/2\}$ and by $\tfrac12$ on $\{\langle u_t,\theta\rangle\le m_t-\epsilon/2\}$; if $Y_t=0$ the factors of the two tails are swapped.
--
--   The update shifts mass towards the half-space the feedback points to, while keeping the density constant inside the $\epsilon$-window.
--
--   **Formalization Note** Integrals are Lebesgue integrals over the closed ball. The window-median predicate does not choose among several solutions of (3). The three cases of Algorithm 3 overlap on the hyperplanes $\langle u_t,\theta\rangle=m_t\pm\epsilon/2$; there the window case (factor $1$) is used. In Algorithm 4 the update only runs for contexts that are not predicted, hence nonzero, and then these hyperplanes have Lebesgue measure zero.
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Algorithm 4 Line 2 (p.21), Definition 3.2 and Equation (3) (p.14), Algorithm 3 (p.15)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model

open MeasureTheory

namespace RobustCtxPricing

/-- **The uniform density over `Θ`.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in
Robust Contextual Pricing*, arXiv:2607.11210, Algorithm 1/4, Line 2 (pp.12, 21): "Initialize `µ_1`
as the uniform density over `Θ`".

`uniformDensity d θ = 1 / vol(Θ)` for `θ ∈ Θ` and `0` outside, with `vol` the Lebesgue measure of
`ℝ^d`. -/
noncomputable def uniformDensity (d : ℕ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (Theta d).indicator (fun _ => ((volume (Theta d)).toReal)⁻¹)

/-- **ϵ-window median, Equation (3) (Definition 3.2).** Castiglioni–Stradi, arXiv:2607.11210, §3.1,
p.14: "Given a density `µ_t` and a direction `u_t`, we define the ϵ-window median of `µ_t` in
direction `u_t` as the value `m_t` such that
`∫_Θ µ_t(θ) 𝕀{⟨u_t, θ⟩ ≤ m_t − ϵ/2} dθ = ∫_Θ µ_t(θ) 𝕀{⟨u_t, θ⟩ ≥ m_t + ϵ/2} dθ`. (3)"

`IsWindowMedian ϵ μ u m` says that `m` satisfies (3).

**Formalization Note.** Integrals are Lebesgue integrals over `Θ` (closed unit ball). The predicate
does not choose among several solutions of (3): every solution is a window median, and Algorithm 4
(`IsAlg4Run`) may post any of them. -/
def IsWindowMedian {d : ℕ} (ϵ : ℝ) (μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (u : EuclideanSpace ℝ (Fin d)) (m : ℝ) : Prop :=
  ∫ θ in Theta d ∩ {θ | inner ℝ u θ ≤ m - ϵ / 2}, μ θ =
    ∫ θ in Theta d ∩ {θ | m + ϵ / 2 ≤ inner ℝ u θ}, μ θ

/-- **Update-Density (Algorithm 3).** Castiglioni–Stradi, arXiv:2607.11210, p.15. If `Y_t = 1`,
`µ_{t+1}(θ) = (3/2)µ_t(θ)` for `⟨u_t, θ⟩ ≥ m_t + ϵ/2`, `µ_t(θ)` for `|⟨u_t, θ⟩ − m_t| ≤ ϵ/2`,
`(1/2)µ_t(θ)` for `⟨u_t, θ⟩ ≤ m_t − ϵ/2`; if `Y_t = 0` the factors `3/2` and `1/2` of the two tails
are swapped.

**Formalization Note.** The paper's cases overlap on the two hyperplanes `⟨u_t, θ⟩ = m_t ± ϵ/2`;
here the window case `|⟨u_t, θ⟩ − m_t| ≤ ϵ/2` takes priority there. In Algorithm 4 the update is
only run when `u_t` is not predicted, hence `u_t ≠ 0` (the empty combination predicts `0`), and
then the hyperplanes are Lebesgue-null, so the choice changes no integral. -/
noncomputable def updateDensity {d : ℕ} (ϵ : ℝ) (μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (u : EuclideanSpace ℝ (Fin d)) (m : ℝ) (Y : Bool) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun θ =>
    if |inner ℝ u θ - m| ≤ ϵ / 2 then μ θ
    else if Y = true then
      (if m + ϵ / 2 ≤ inner ℝ u θ then (3 / 2 : ℝ) * μ θ else (1 / 2 : ℝ) * μ θ)
    else
      (if inner ℝ u θ ≤ m - ϵ / 2 then (3 / 2 : ℝ) * μ θ else (1 / 2 : ℝ) * μ θ)

end RobustCtxPricing


