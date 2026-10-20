-- Prove2me | Definitions.Def_Plasticity_C0Sum
-- name    : Plasticity_C0Sum
-- status  : Definition
-- author  : @scanstone
-- created : 2026-10-19T18:59:22.258364+00:00
-- url     : https://prove2.me/theorems/2388ab97-e638-43ce-9dfb-d3d55709f771
-- title:
--   The $c_0$ sum of a family of real normed spaces
-- statement:
--   For a family $(E_i)_{i\in I}$ of real normed spaces over an arbitrary index set $I$, the **$\ell_\infty$ sum** consists of the families $x=(x_i)_{i\in I}$ with $x_i\in E_i$ and $\sup_i\|x_i\|<\infty$, normed by $\|x\|=\sup_{i\in I}\|x_i\|$.
--   The **$c_0$ sum** $c_0(I;E_i)$ is the subspace of those $x$ whose block norms tend to $0$: for every $\varepsilon>0$ only finitely many $i$ have $\|x_i\|\ge\varepsilon$.
--   It carries the inherited supremum norm.
--
--   **Formalization Note** The $\ell_\infty$ sum is Mathlib's `lp E ⊤`; `c0Sum E` is the submodule of `lp E ⊤` of the `x` with `fun i => ‖x i‖` tending to `0` along the cofinite filter, and as a type it carries the subspace norm.
-- source:
--   This repository: expositions/c0_sums_euclidean_blocks.md §1 (c₀ sums of a family of blocks with the supremum block norm), as used in expositions/c0_planes_with_scalars.md §1

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Order.Filter.Cofinite

/-!
# Plasticity: c₀ sums of normed spaces

For a family `E : ι → Type*` of real normed spaces over an arbitrary index set, Mathlib's
`lp E ⊤` is the ℓ∞ sum: the families `x` with `x i ∈ E i` and bounded block norms, with the
norm `‖x‖ = sup_i ‖x i‖`. Inside it, `c0Sum E` is the c₀ sum: the families whose block norms
tend to `0` along the cofinite filter (for every `ε > 0`, only finitely many `i` have
`‖x i‖ ≥ ε`). As a submodule it carries the inherited supremum norm.
-/

namespace Plasticity

open Filter Topology

/-- The c₀ sum of a family of real normed spaces: the elements of the ℓ∞ sum `lp E ⊤`
whose block norms `‖x i‖` tend to `0` along the cofinite filter. -/
def c0Sum {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] : Submodule ℝ (lp E ⊤) where
  carrier := {x | Tendsto (fun i => ‖x i‖) cofinite (𝓝 0)}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, lp.coeFn_zero, Pi.zero_apply, norm_zero]
    exact tendsto_const_nhds
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, lp.coeFn_add, Pi.add_apply] at *
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => norm_add_le _ _) ?_
    simpa using hx.add hy
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, lp.coeFn_smul, Pi.smul_apply, norm_smul] at *
    simpa using hx.const_mul ‖c‖

end Plasticity


