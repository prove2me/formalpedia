-- Prove2me | Definitions.Def_InfHorizonVP_IsStrictlyDifferentiableAt
-- name    : InfHorizonVP_IsStrictlyDifferentiableAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:38.852293+00:00
-- url     : https://prove2.me/theorems/9bb78f12-2789-4bbf-8ab4-1a5be8dab334
-- title:
--   Strict differentiability (2.2)
-- statement:
--   A function $\varphi:E\to\mathbb R$ is **strictly differentiable** at $\bar x$ with strict derivative $\nabla\varphi(\bar x)\in E^*$ if
--   $$
--   \lim_{x\to\bar x,\ \theta\to0}\frac{\varphi(x+\theta v)-\varphi(x)}{\theta}=\langle\nabla\varphi(\bar x),v\rangle\tag{2.2}
--   $$
--   uniformly in $v\in C$ for every compact $C\subseteq E$.
--
--   **Formalization Note** Uniformity is only over compact sets, which in infinite dimensions is weaker than Mathlib's `HasStrictFDerivAt`.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.3, (2.2)

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Strict differentiability (2.2).**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.3: "A function ϕ is said to be strictly
differentiable at x̄ if there exists ∇ϕ(x̄) ∈ E* such that lim_{x→x̄, θ→0} (ϕ(x + θv) − ϕ(x))/θ =
⟨∇ϕ(x̄), v⟩ (2.2) and the convergence in (2.2) is uniform in v ∈ C for every compact subset C of
E. Then ∇ϕ(x̄) is called the strict derivative of ϕ at x̄."

`IsStrictlyDifferentiableAt φ g x̄` says `φ` is strictly differentiable at `x̄` with strict
derivative `g`.

**Formalization Note.** Uniformity is over compact sets only; in infinite dimensions this is
weaker than Mathlib's norm-uniform `HasStrictFDerivAt`, which is therefore not used. `θ → 0` is
two-sided with `θ ≠ 0`. -/
def IsStrictlyDifferentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → ℝ) (g : E →L[ℝ] ℝ) (x : E) : Prop :=
  ∀ C : Set E, IsCompact C → ∀ ε > 0, ∃ δ > 0, ∀ y : E, ‖y - x‖ < δ → ∀ θ : ℝ, θ ≠ 0 → |θ| < δ →
    ∀ v ∈ C, |(φ (y + θ • v) - φ y) / θ - g v| < ε

end InfHorizonVP


