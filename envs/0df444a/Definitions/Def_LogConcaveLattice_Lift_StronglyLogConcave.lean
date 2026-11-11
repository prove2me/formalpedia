-- Prove2me | Definitions.Def_LogConcaveLattice_Lift_StronglyLogConcave
-- name    : LogConcaveLattice_Lift_StronglyLogConcave
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:09.20033+00:00
-- url     : https://prove2.me/theorems/1b544560-c91a-4b04-a6f2-51ed9dbb2f36
-- title:
--   §1.1 — $\alpha$-strongly log-concave functions
-- statement:
--   For $\alpha>0$, a smooth ($C^\infty$) function $f:\mathbb R^n\to(0,\infty)$ is **$\alpha$-strongly log-concave** if
--   $$\nabla^2(-\log f)(x)\succcurlyeq\alpha\cdot\mathrm{Id}\qquad\text{for every }x\in\mathbb R^n,$$
--   that is, the second derivative of $-\log f$ at $x$, as a bilinear form, satisfies $D^2(-\log f)(x)(v,v)\ge\alpha\|v\|^2$ for all $v\in\mathbb R^n$.
--
--   Strong log-concavity is the curvature condition behind the Bakry–Émery criterion and Hargé's comparison theorem; in Theorem 1.1 it is the property of the lattice lift.
--
--   **Formalization Note** Smoothness (`ContDiff ℝ ∞`, not analyticity) and strict positivity are part of the predicate, as in the source's definition, so the second derivative is a genuine one and $\log f$ is evaluated only at positive values.
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, §1.1 p. 3 (definition of α-strong log-concavity); Loewner order p. 6

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice

open scoped RealInnerProductSpace

namespace LogConcaveLattice.Lift

variable {n : ℕ}

/-- **α-strong log-concavity** (p. 3): a smooth (`C^∞`) function `f : ℝⁿ → (0, ∞)` is
α-strongly log-concave if `∇²(−log f)(x) ≽ α · Id` for every `x ∈ ℝⁿ`, i.e. the second
derivative of `−log f` at `x`, as a bilinear form, satisfies `D²(−log f)(x)(v, v) ≥ α ‖v‖²`
for all `v`. Smoothness and strict positivity are part of the definition, as on p. 3. -/
def IsStronglyLogConcave (α : ℝ) (f : V n → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ x, 0 < f x) ∧
    ∀ x v : V n, α * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun y => -Real.log (f y))) x v v

end LogConcaveLattice.Lift


