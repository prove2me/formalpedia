-- Prove2me | Definitions.Def_InfHorizonVP_IsGateauxDifferentiableAt
-- name    : InfHorizonVP_IsGateauxDifferentiableAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:08.276784+00:00
-- url     : https://prove2.me/theorems/aaf9e392-99a8-4e7f-8bed-c7d5a488cefd
-- title:
--   Gateaux differentiability (2.1)
-- statement:
--   A function $\varphi:E\to\mathbb R$ is **Gateaux differentiable** at $\bar x$ with Gateaux derivative $\nabla\varphi(\bar x)\in E^*$ if
--   $$
--   \lim_{\theta\to0}\frac{\varphi(\bar x+\theta v)-\varphi(\bar x)}{\theta}=\langle\nabla\varphi(\bar x),v\rangle\tag{2.1}
--   $$
--   for every $v\in E$.
--
--   **Formalization Note** $E^*$ is `E →L[ℝ] ℝ`; $\theta\to0$ is two-sided with $\theta\neq0$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.3, (2.1)

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Gateaux differentiability (2.1).**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.3: "A real-valued function ϕ : E → R is said to be
Gateaux differentiable at x̄ ∈ E if there exists an element ∇ϕ(x̄) ∈ E* such that
lim_{θ→0} (ϕ(x̄ + θv) − ϕ(x̄))/θ = ⟨∇ϕ(x̄), v⟩ (2.1) for every v ∈ E; ∇ϕ(x̄) is called the Gateaux
derivative of ϕ at x̄."

`IsGateauxDifferentiableAt φ g x̄` says `φ` is Gateaux differentiable at `x̄` with Gateaux
derivative `g`.

**Formalization Note.** `E* = E →L[ℝ] ℝ`; `θ → 0` is two-sided with `θ ≠ 0` (`𝓝[≠] 0`). -/
def IsGateauxDifferentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → ℝ) (g : E →L[ℝ] ℝ) (x : E) : Prop :=
  ∀ v : E, Tendsto (fun θ : ℝ => (φ (x + θ • v) - φ x) / θ) (𝓝[≠] 0) (𝓝 (g v))

end InfHorizonVP


