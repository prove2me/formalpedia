-- Prove2me | Definitions.Def_DissolveCDF_Assumption12
-- name    : DissolveCDF_Assumption12
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:53.197405+00:00
-- url     : https://prove2.me/theorems/1ad12544-267e-4b8b-803b-0b13de440853
-- title:
--   Assumption 1.2 — blanket assumptions on the constraint dissolving operator $\mathcal A$
-- statement:
--   Let $c:\mathbb R^n\to\mathbb R^p$ with feasible set $\mathcal M=\{x: c(x)=0\}$. A map $\mathcal A:\mathbb R^n\to\mathbb R^n$ satisfies **Assumption 1.2** (and is then called a constraint dissolving operator) when
--
--   1. $\mathcal A$ is locally Lipschitz smooth on $\mathbb R^n$;
--   2. $\mathcal A(x)=x$ for every $x\in\mathcal M$;
--   3. the Jacobian of $c(\mathcal A(x))$ vanishes on $\mathcal M$, i.e.
--
--   $$
--   J_{\mathcal A}(x)\,J_c(x)=0\qquad\text{for every }x\in\mathcal M .
--   $$
--
--   Item 3 makes $c(\mathcal A(y))$ quadratically small in $c(y)$ near $\mathcal M$, which is what lets the penalty $\frac\beta2\|c\|^2$ be exact.
--
--   **Formalization Note** "Locally Lipschitz smooth" is read as: $\mathcal A$ is differentiable and $J_{\mathcal A}$ is locally Lipschitz continuous (operator norm).
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §1.3, Assumption 1.2, p.4

import Mathlib
import Definitions.Def_DissolveCDF_transJac

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, Assumption 1.2 (p.4): the blanket assumptions on the constraint dissolving
operator `A : ℝⁿ → ℝⁿ` for the constraint map `c : ℝⁿ → ℝᵖ`, with `M = {x | c(x) = 0}`:
* `A` is locally Lipschitz smooth in `ℝⁿ`;
* `A(x) = x` for every `x ∈ M`;
* the Jacobian of `c(A(x))` vanishes on `M`, that is `J_A(x) J_c(x) = 0` for every `x ∈ M`.

**Formalization Note** "Locally Lipschitz smooth" is read as: `A` is differentiable and its
transposed Jacobian `J_A` is locally Lipschitz continuous (operator norm). `J_A(x) J_c(x)` is the
composition of the linear maps `J_c(x) : ℝᵖ → ℝⁿ` and `J_A(x) : ℝⁿ → ℝⁿ`. -/
structure Assumption12 {n p : ℕ} (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop where
  differentiable_A : Differentiable ℝ A
  locallyLipschitz_transJac_A : LocallyLipschitz (transJac A)
  fixes_feasible : ∀ x, c x = 0 → A x = x
  transJac_comp_eq_zero : ∀ x, c x = 0 → transJac A x ∘L transJac c x = 0

end DissolveCDF


