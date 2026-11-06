-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Assumption21
-- name    : RollingProbeQN_Convex_Assumption21
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:39.202284+00:00
-- url     : https://prove2.me/theorems/a961e040-5a01-4323-a323-3658f7726d55
-- title:
--   Assumption 2.1: convex $C^2$ objective with $0\preceq H\preceq L_1I$, $L_2$-Lipschitz Hessian, sparsity pattern and partition
-- statement:
--   **Assumption 2.1.** The function $f:\mathbb R^d\to\mathbb R$ is convex and twice continuously differentiable, and positive constants $L_1,L_2,R$ satisfy, for all $x,y$,
--
--   $$0\preceq H(x)\preceq L_1 I,\qquad \|H(x)-H(y)\|_{\mathrm{op}}\le L_2\|x-y\|.$$
--
--   A minimizer $x^\star$ of $f$ exists and $\|x_0-x^\star\|\le R$. A pattern $\mathcal S$ with $\operatorname{supp}H(x)\subseteq\mathcal S$ for every $x$, and a partition of the columns into $\chi\ge1$ groups that is structurally orthogonal for $\mathcal S$, are given.
--
--   This is the standing assumption of every result of Section 3 and Appendix E.
--
--   **Formalization Note** $0\preceq H(x)\preceq L_1I$ is written as $0\le\langle H(x)v,v\rangle\le L_1\|v\|^2$ for all $v$; the operator norm is the norm of continuous linear maps; $\operatorname{supp}H(x)\subseteq\mathcal S$ says $\langle e_i,H(x)e_j\rangle=0$ for $(i,j)\notin\mathcal S$. The oracle clause of the paper (exact gradients) is the choice $G=\nabla f$ in the theorems.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Assumption 2.1 and Definition 2.2, p. 7

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_hess
import Definitions.Def_RollingProbeQN_Convex_IsStructOrthPartition

namespace RollingProbeQN.Convex

/-- **Assumption 2.1.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Assumption 2.1, p. 7: "The function `f : R^d → R` is convex and twice continuously
differentiable, with known positive upper bounds `L1, L2` such that `0 ⪯ H(x) ⪯ L1 I`, and
`‖H(x) − H(y)‖op ≤ L2 ‖x − y‖`. A minimizer `x★` exists, and a known `R > 0` satisfies
`‖x0 − x★‖ ≤ R`. […] A pattern `S` with `supp H(x) ⊆ S` for every `x ∈ R^d`, and a partition
`g1, …, gχ` of `[d]` that is structurally orthogonal for `S` (Definition 2.2), are supplied."

**Formalization Note.** `0 ⪯ H(x) ⪯ L₁ I` is written with the quadratic form of `hess f x`; the
operator norm is the norm of continuous linear maps. `supp H(x) ⊆ S` says that every entry
`⟪e_i, H(x) e_j⟫` with `(i, j) ∉ S` vanishes. `0 < χ` is the paper's partition into `χ ≥ 1` groups
(reading R7 of the mission). The oracle clause ("exact values and gradients") is the choice
`G = gradient f` in the statements that use this predicate. -/
def Assumption21 (d χ : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (L₁ L₂ R : ℝ)
    (S : Set (Fin d × Fin d)) (grp : Fin d → Fin χ) (x₀ xstar : EuclideanSpace ℝ (Fin d)) : Prop :=
  0 < L₁ ∧ 0 < L₂ ∧ 0 < R ∧ 0 < χ ∧
  ConvexOn ℝ Set.univ f ∧ ContDiff ℝ 2 f ∧
  (∀ x v : EuclideanSpace ℝ (Fin d),
    0 ≤ inner ℝ (hess f x v) v ∧ inner ℝ (hess f x v) v ≤ L₁ * ‖v‖ ^ 2) ∧
  (∀ x y : EuclideanSpace ℝ (Fin d), ‖hess f x - hess f y‖ ≤ L₂ * ‖x - y‖) ∧
  IsMinOn f Set.univ xstar ∧ ‖x₀ - xstar‖ ≤ R ∧
  (∀ (x : EuclideanSpace ℝ (Fin d)) (i j : Fin d), (i, j) ∉ S →
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (hess f x (EuclideanSpace.single j (1 : ℝ))) = 0) ∧
  IsStructOrthPartition S grp

end RollingProbeQN.Convex


