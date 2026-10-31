-- Prove2me | Definitions.Def_RBMSensitivity_Data_Assumption_2_4
-- name    : RBMSensitivity_Data_Assumption_2_4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:47.094053+00:00
-- url     : https://prove2.me/theorems/6e175a7e-549c-483d-9aa9-b16f76c6a8f8
-- title:
--   Assumption 2.4: the sets $B^\alpha$
-- statement:
--   **Assumption 2.4.** For each $\alpha\in U$ there exists $\theta(\alpha)>0$ and a compact, convex, symmetric set $B^\alpha$ in $\mathbb R^J$ with $0\in(B^\alpha)^\circ$ such that for $i\in\mathcal I$,
--   $$\Big\{z\in\partial B^\alpha,\ |\langle z,n_i\rangle|<\theta(\alpha)\Big\}\ \Rightarrow\ \langle\nu,d_i(\alpha)\rangle=0\quad\text{for all }\nu\in\nu_{B^\alpha}(z).$$
--   Furthermore, $\alpha\mapsto B^\alpha$ is continuous in the Hausdorff metric.
--
--   This is the geometric condition of Dupuis and Ishii for Lipschitz continuity of the Skorokhod map. The norm of $B^\alpha$ is also the norm in which the derivative problem is contractive.
--
--   **Formalization Note** The family $\alpha\mapsto B^\alpha$ is an argument of the formal assumption, since later statements refer to it.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Assumption 2.4, (2.6), p.6

import Mathlib
import Definitions.Def_RBMSensitivity_Data
import Definitions.Def_RBMSensitivity_inwardNormals
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- Assumption 2.4: arXiv:1907.00472v2, (2.6), p.6, for a given family `α ↦ B^α`.

For each `α ∈ U` there is `θ(α) > 0` and a compact, convex, symmetric `B^α` with `0 ∈ (B^α)°` such
that for `i ∈ I`, `z ∈ ∂B^α` with `|⟨z, n_i⟩| < θ(α)` implies `⟨ν, d_i(α)⟩ = 0` for all `ν ∈ ν_{B^α}(z)`.
Furthermore `α ↦ B^α` is continuous in the Hausdorff metric (1.1).

**Formalization Note.** The family `B` is an argument because later statements use the norm of `B^α`;
each theorem takes it as a variable, which is the same as assuming that some family exists. `θ` is
under an existential. The sets `B^α`, `α ∈ U`, are compact and nonempty, so `Metric.hausdorffDist`
is finite and is the metric `ρ_H` of (1.1). -/
def Data.Assumption_2_4 {J : ℕ} (D : Data J) (B : ℝ → Set (E J)) : Prop :=
  (∀ α ∈ D.U, ∃ θ : ℝ, 0 < θ ∧ IsCompact (B α) ∧ Convex ℝ (B α) ∧ (∀ x ∈ B α, -x ∈ B α) ∧
    (0 : E J) ∈ interior (B α) ∧
    ∀ i, ∀ z ∈ frontier (B α), |⟪z, D.n i⟫| < θ →
      ∀ ν ∈ inwardNormals (B α) z, ⟪ν, D.d i α⟫ = 0) ∧
  ∀ α ∈ D.U, Tendsto (fun β => Metric.hausdorffDist (B β) (B α)) (𝓝[D.U] α) (𝓝 0)

end RBMSensitivity


