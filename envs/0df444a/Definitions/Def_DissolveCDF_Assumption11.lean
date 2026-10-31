-- Prove2me | Definitions.Def_DissolveCDF_Assumption11
-- name    : DissolveCDF_Assumption11
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:46.164479+00:00
-- url     : https://prove2.me/theorems/c3717567-1e39-4771-92f4-7c847612981a
-- title:
--   Assumption 1.1 — blanket assumptions on $f$ and $c$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and $c:\mathbb R^n\to\mathbb R^p$, and let $\mathcal M=\{x\in\mathbb R^n: c(x)=0\}$ be the feasible region of
--
--   $$
--   \min_{x\in\mathbb R^n} f(x)\quad\text{s.t.}\quad c(x)=0. \tag{OCP}
--   $$
--
--   **Assumption 1.1** holds when
--
--   1. $\nabla f$ is locally Lipschitz continuous on $\mathbb R^n$;
--   2. the transposed Jacobian $J_c(x)\in\mathbb R^{n\times p}$ is locally Lipschitz continuous on $\mathbb R^n$;
--   3. the linear independence constraint qualification holds on $\mathcal M$: $J_c(x)$ has full column rank for every $x\in\mathcal M$.
--
--   These are the standing hypotheses on the problem data for every result of the mission.
--
--   **Formalization Note** Items 1 and 2 presuppose differentiability of $f$ and $c$, which is stated explicitly. Full column rank is injectivity of $J_c(x):\mathbb R^p\to\mathbb R^n$; local Lipschitz continuity of $J_c$ is for the operator norm.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §1.1, Assumption 1.1, p.1

import Mathlib
import Definitions.Def_DissolveCDF_transJac

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Assumption 1.1 (p.1): the blanket assumptions on the objective `f : ℝⁿ → ℝ` and
the constraint map `c : ℝⁿ → ℝᵖ` of (OCP) `min f(x) s.t. c(x) = 0`, with feasible set
`M = {x | c(x) = 0}`:
1. `∇f` is locally Lipschitz continuous in `ℝⁿ`;
2. the transposed Jacobian `J_c(x) ∈ ℝ^{n×p}` is locally Lipschitz continuous in `ℝⁿ`;
3. LICQ: `J_c(x)` has full column rank for every `x ∈ M`.

**Formalization Note** Items 1 and 2 presuppose that `f` and `c` are differentiable, which is
stated as the fields `differentiable_f` and `differentiable_c`. Full column rank of `J_c(x)` is
injectivity of the linear map `J_c(x) : ℝᵖ → ℝⁿ`. Local Lipschitz continuity of `J_c` is with
respect to the operator norm (all norms on `ℝ^{n×p}` are equivalent, so the choice does not
matter). -/
structure Assumption11 {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p)) : Prop where
  differentiable_f : Differentiable ℝ f
  locallyLipschitz_gradient_f : LocallyLipschitz (gradient f)
  differentiable_c : Differentiable ℝ c
  locallyLipschitz_transJac_c : LocallyLipschitz (transJac c)
  licq : ∀ x, c x = 0 → Function.Injective (transJac c x)

end DissolveCDF


