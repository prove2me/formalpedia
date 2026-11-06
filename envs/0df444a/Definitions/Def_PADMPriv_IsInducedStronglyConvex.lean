-- Prove2me | Definitions.Def_PADMPriv_IsInducedStronglyConvex
-- name    : PADMPriv_IsInducedStronglyConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:08.040354+00:00
-- url     : https://prove2.me/theorems/550496d3-07eb-4225-b433-f4b0a8576b34
-- title:
--   $A$-induced $\varrho$-strong convexity (Definition 7)
-- statement:
--   Let $F:\mathbb R^p\to\mathbb R$ and $A\in\mathbb R^{m\times p}$. $F$ is **$A$-induced $\varrho$-strongly convex** if $\varrho>0$ and for all $x,x'\in\mathbb R^p$, $v\in\partial F(x)$ and $v'\in\partial F(x')$,
--   $$
--   (v-v')^\top(x-x') \ \ge\ \varrho\,\|A(x-x')\|_2^2. \tag{24}
--   $$
--   Here $\partial F(x)$ is the convex subdifferential of Definition A1: $s\in\partial F(x)$ iff $F(t)-F(x)\ge s^\top(t-x)$ for all $t$. The notion is weaker than ordinary strong convexity (it only controls directions seen by $A$), and it is what makes $T_F$ a contraction (Proposition 5.1).
--
--   **Formalization Note** The subdifferential is the published `ProxAlg.FixedPoint.subdifferential` of $F$ viewed as an extended-real function; for real-valued $F$ it is exactly Definition A1.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Definition 7, Eq. (24), p.11; Definition A1, p.19

import Mathlib
import Definitions.Def_ProxAlg_FixedPoint_Basic

namespace PADMPriv

open scoped InnerProductSpace

/-- Induced strong convexity, Definition 7 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.11: `F` is
`A`-induced `ϱ`-strongly convex if `ϱ > 0` and for all `x, x′`, `v ∈ ∂F(x)`, `v′ ∈ ∂F(x′)`,
`(v − v′)ᵀ(x − x′) ≥ ϱ ‖A(x − x′)‖₂²` (24). Here `∂F` is the convex subdifferential of
Definition A1, p.19: `s ∈ ∂F(x)` iff `F(t) − F(x) ≥ sᵀ(t − x)` for all `t`.

**Formalization Note** `∂F` is the published `ProxAlg.FixedPoint.subdifferential` applied to
`F` coerced to `EReal`; for a real-valued `F` its effective-domain clause holds automatically,
so it is exactly Definition A1. -/
def IsInducedStronglyConvex {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (ϱ : ℝ)
    (F : EuclideanSpace ℝ (Fin p) → ℝ) : Prop :=
  0 < ϱ ∧ ∀ (x x' v v' : EuclideanSpace ℝ (Fin p)),
    v ∈ ProxAlg.FixedPoint.subdifferential (fun t => (F t : EReal)) x →
    v' ∈ ProxAlg.FixedPoint.subdifferential (fun t => (F t : EReal)) x' →
    ϱ * ‖Matrix.toEuclideanLin A (x - x')‖ ^ 2 ≤ ⟪v - v', x - x'⟫_ℝ

end PADMPriv


