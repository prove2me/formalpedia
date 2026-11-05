-- Prove2me | Definitions.Def_DegenNRM_Assumption1
-- name    : DegenNRM_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:39.158128+00:00
-- url     : https://prove2.me/theorems/8d0aa2da-3a3d-4cab-8565-67f3829d8e3b
-- title:
--   Assumption 1: rewards on $[l_j,u_j]$ with density at least $\alpha$, point masses allowed
-- statement:
--   Let $\alpha\in\mathbb R$. The instance satisfies **Assumption 1** with constant $\alpha$ if $\alpha>0$ and, for every type $j$, the reward law $F_j$ is concentrated on $[l_j,u_j]$, i.e. $F_j([l_j,u_j])=1$, and
--
--   1. either $l_j=u_j$, so that $F_j$ is the point mass at $l_j$ (the paper sets the density to $\infty$ there, so that every $\alpha$ qualifies);
--   2. or $F_j$ has a Lebesgue density $f_j$ with $f_j(r)\ge\alpha$ for every $r\in[l_j,u_j]$.
--
--   Assumption 1 is the standing hypothesis of Section 3 of the paper. The density bound makes the quantile function $F_j^{-1}$ $(1/\alpha)$-Lipschitz, which drives the quadratic bounds of the myopic regret.
--
--   **Formalization Note** The density is an extended nonnegative measurable function and the bound reads $\mathrm{ofReal}(\alpha)\le f_j(r)$. A density case with $l_j=u_j$ cannot occur, so the disjunction is exactly the paper's dichotomy.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Assumption 1, p.10

import Mathlib
import Definitions.Def_DegenNRM_Instance

open MeasureTheory

namespace DegenNRM

/-- **Assumption 1** (Jiang, Ma & Zhang, arXiv:2210.07996v5, Assumption 1, p.10).

`α > 0`, and for each type `j` the reward law `F_j` is supported on `[l_j, u_j]` and either

1. `l_j = u_j`: `F_j` is the point mass at `l_j` ("we allow lj = uj for a type j, i.e., the
   reward distribution for type j query is a point mass. In this case, we let the density be
   fj(r) = ∞ for r = lj = uj and any constant α would satisfy fj(r) ≥ α", p.10); or
2. `F_j` has a Lebesgue density `f_j` with `f_j(r) ≥ α` for every `r ∈ [l_j, u_j]`.

**Formalization Note.** The two cases are the printed hypothesis with its point-mass convention
made explicit. A density case with `l_j = u_j` cannot occur (a density gives the singleton
mass `0`), so the disjunction is exactly the paper's dichotomy. The density is an extended
nonnegative function and the bound is `ENNReal.ofReal α ≤ f r`. -/
def Assumption1 {m n : ℕ} (inst : Instance m n) (α : ℝ) : Prop :=
  0 < α ∧ ∀ j, inst.F j (Set.Icc (inst.l j) (inst.u j)) = 1 ∧
    (inst.l j = inst.u j ∨
      ∃ f : ℝ → ENNReal, Measurable f ∧ inst.F j = volume.withDensity f ∧
        ∀ r ∈ Set.Icc (inst.l j) (inst.u j), ENNReal.ofReal α ≤ f r)

end DegenNRM


