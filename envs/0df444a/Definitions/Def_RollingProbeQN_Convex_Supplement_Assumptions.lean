-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Supplement_Assumptions
-- name    : RollingProbeQN_Convex_Supplement_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:41:49.647943+00:00
-- url     : https://prove2.me/theorems/0b234fd4-7774-4214-8584-42f734ae3981
-- title:
--   Assumption 4.1 (strong convexity) and Assumption 5.1 (the nonconvex setting)
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ and write $H(x)=\nabla^2 f(x)$.
--
--   1. **Assumption 4.1.** In addition to Assumption 2.1, $f$ is $\mu$-strongly convex for a known $\mu>0$: $\mu I\preceq H(x)$ for every $x$, that is,
--   $$\mu\|v\|^2\le\langle H(x)v,v\rangle\qquad\text{for all }x,v\in\mathbb R^d .$$
--   2. **Assumption 5.1.** $f$ is twice continuously differentiable and bounded below, with known constants $L_1,L_2>0$ such that
--   $$\|H(x)\|_{\mathrm{op}}\le L_1,\qquad \|H(x)-H(y)\|_{\mathrm{op}}\le L_2\|x-y\|\qquad\text{for all }x,y,$$
--   a pattern $\mathcal S$ with $\operatorname{supp}H(x)\subseteq\mathcal S$ for every $x$, and a partition $g_1,\dots,g_\chi$ of $[d]$ that is structurally orthogonal for $\mathcal S$ (Definition 2.2). No convexity, no minimizer and no radius $R$ are assumed.
--
--   Assumption 4.1 is the setting of Section 4 (Theorem 4.2 and the restart scheme of Theorem G.1); Assumption 5.1 is the setting of Section 5 and of Theorems B.3, I.6 and I.9.
--
--   **Formalization Note** $H(x)$ is the published `hess f x`; the Loewner bound is written with the quadratic form, the operator norm is the norm of continuous linear maps, and the partition is the published `IsStructOrthPartition` (0-based groups, surjective group map, $\chi\ge1$). The oracle clause is the choice $G=\nabla f$ in the theorems.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Assumption 4.1, p. 13; Assumption 5.1, p. 17

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_hess
import Definitions.Def_RollingProbeQN_Convex_IsStructOrthPartition

namespace RollingProbeQN.Convex.Supplement

/-- **Assumption 4.1 (strong convexity).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Assumption 4.1, p. 13: "In addition to
Assumption 2.1, `f` is `μ`-strongly convex for a known `μ > 0`, that is, `μI ⪯ H(x)` for every `x`."

`Assumption41 f μ` is the part beyond Assumption 2.1: `μ > 0` and `μ‖v‖² ≤ ⟪H(x)v, v⟫` for all
`x, v`. The theorems use it together with the published `Assumption21`.

**Formalization Note.** `H(x)` is the published `hess f x`; `μI ⪯ H(x)` is written with the quadratic
form, as `0 ⪯ H(x) ⪯ L₁I` is in `Assumption21`. -/
def Assumption41 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (μ : ℝ) : Prop :=
  0 < μ ∧ ∀ x v : EuclideanSpace ℝ (Fin d), μ * ‖v‖ ^ 2 ≤ inner ℝ (hess f x v) v

/-- **Assumption 5.1 (the nonconvex setting).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Assumption 5.1, p. 17: "The function
`f : R^d → R` is twice continuously differentiable and bounded below, with known positive constants
`L1, L2` such that `‖H(x)‖op ≤ L1`, `‖H(x) − H(y)‖op ≤ L2‖x − y‖` for all `x, y ∈ R^d`. The oracle
returns exact gradients at arbitrary query points. A pattern `S` with `supp H(x) ⊆ S` for every `x`,
and a partition `g1, …, gχ` of `[d]` that is structurally orthogonal for `S`, are supplied as in
Assumption 2.1".

No convexity, no minimizer and no radius `R` are assumed.

**Formalization Note.** As in the published `Assumption21`: `H(x)` is `hess f x`, the operator norm is
the norm of continuous linear maps, `supp H(x) ⊆ S` says that every entry `⟪e_i, H(x)e_j⟫` with
`(i, j) ∉ S` vanishes, the partition is the published `IsStructOrthPartition` (0-based groups,
surjective group map) and `0 < χ` is the partition into `χ ≥ 1` groups (reading R7 of the base
mission). The oracle clause is the choice `G = gradient f` in the statements. -/
def Assumption51 (d χ : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (L₁ L₂ : ℝ)
    (S : Set (Fin d × Fin d)) (grp : Fin d → Fin χ) : Prop :=
  0 < L₁ ∧ 0 < L₂ ∧ 0 < χ ∧ ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧
  (∀ x : EuclideanSpace ℝ (Fin d), ‖hess f x‖ ≤ L₁) ∧
  (∀ x y : EuclideanSpace ℝ (Fin d), ‖hess f x - hess f y‖ ≤ L₂ * ‖x - y‖) ∧
  (∀ (x : EuclideanSpace ℝ (Fin d)) (i j : Fin d), (i, j) ∉ S →
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (hess f x (EuclideanSpace.single j (1 : ℝ))) = 0) ∧
  IsStructOrthPartition S grp

end RollingProbeQN.Convex.Supplement


