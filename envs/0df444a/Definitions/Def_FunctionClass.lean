-- Prove2me | Definitions.Def_FunctionClass
-- name    : FunctionClass
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:11:57.065345+00:00
-- url     : https://prove2.me/theorems/46ff5a67-05d4-49df-986a-8b228e02dda9
-- title:
--   The admissible function classes of Theorems A and B
-- statement:
--   This module introduces the two function classes the theorems quantify over, both stated on a complete real inner product space. `Admissible L R f x₀ x⋆`, the class of Theorem A, is a structure requiring: $0 < L$; convexity of $f$ on the whole space (`ConvexOn ℝ Set.univ f`); differentiability of $f$; a globally $L$-Lipschitz gradient, stated pointwise as $\|\nabla f(x) - \nabla f(y)\| \le L\|x-y\|$ for all $x, y$; that $x_\star$ is a global minimiser, $f(x_\star) \le f(x)$ for all $x$; and the radius condition $\|x_0 - x_\star\| \le R$. `AdmissibleUnique` extends it with the field `unique_min`, requiring the minimiser to be unique: $f(x) = f(x_\star) \Rightarrow x = x_\star$. The latter is the class of Theorem B, and the uniqueness is genuinely used, since it is what makes the constructed common extremizer a legitimate member.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), Theorem A lines 19-23 and Theorem B lines 2062-2068; Lean: FullFormalization.FunctionClass lines 1-89

-- Generated from F:/20261008/FullFormalization\FullFormalization\FunctionClass.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.FunctionClass

  The admissible function class of the source document.

  Theorem A (source lines 19-23):

      `f` is a differentiable convex function on an arbitrary finite-dimensional
      Euclidean space, `∇f` is globally `L`-Lipschitz, `L > 0`, there is an
      optimizer `x⋆`, and `‖x₀ - x⋆‖ ≤ R`.

  Theorem B (source lines 2062-2068):

      the same class, but the class requires the optimizer to be *unique*, and
      the radius is measured from `x_init`.

  Representation choices (see DEPENDENCY_MAP.md, section 0, R1-R6):

  * The ambient space is a real inner product space `E` that is complete.
    `gradient` in Mathlib is only defined on a complete inner product space.
    The source's "finite-dimensional Euclidean space" is complete, and the two
    headline theorems additionally carry `[FiniteDimensional ℝ E]` so that the
    Lean statements match the source hypothesis for hypothesis.  Intermediate
    lemmas do not carry `FiniteDimensional`, because they do not use it.

  * Convexity is `ConvexOn ℝ Set.univ f` (convexity on the whole space).

  * "Globally `L`-Lipschitz gradient" is the pointwise statement
    `∀ x y, ‖∇f x - ∇f y‖ ≤ L * ‖x - y‖`, which is the source's wording
    verbatim and avoids an `NNReal` coercion.

  * "An optimizer" is `IsMinOn f Set.univ x⋆`, i.e. `∀ x, f x⋆ ≤ f x`.
    Theorem B's "unique optimizer" is recorded as the separate field
    `unique_min`.
-/

import Mathlib
import Definitions.Def_Coefficients

namespace FullFormalization

open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Source lines 19-23: the admissible class of Theorem A.

`L > 0`, `f` differentiable and convex, `∇f` globally `L`-Lipschitz, `x⋆` an
optimizer, `x₀` within radius `R` of `x⋆`.  (The source does not require `R > 0`
for Theorem A, but Theorem A's *statement* has `R` on the right-hand side of
`f(x_N) - f⋆ ≤ 2 L R^2 / (N^2 + 7 N + 4)`; the inequality is trivial for `R = 0`,
so no positivity of `R` is needed and none is assumed here.) -/
structure Admissible (L R : ℝ) (f : E → ℝ) (x₀ xstar : E) : Prop where
  /-- the smoothness constant is positive -/
  L_pos : 0 < L
  /-- `f` is convex on the whole space -/
  convex : ConvexOn ℝ Set.univ f
  /-- `f` is differentiable -/
  differentiable : Differentiable ℝ f
  /-- the gradient is globally `L`-Lipschitz -/
  smooth : ∀ x y : E, ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖
  /-- `x⋆` is a global minimizer -/
  isMin : ∀ x : E, f xstar ≤ f x
  /-- the initial point lies within radius `R` of the minimizer -/
  within_radius : ‖x₀ - xstar‖ ≤ R

/-- Source lines 2062-2068: the admissible class of Theorem B.

Identical to `Admissible`, but the optimizer is required to be **unique**
(source line 2065: "要求存在唯一最优点 `x⋆`").  This uniqueness is genuinely
used: it is what makes the constructed common extremizer a legitimate member of
the class. -/
structure AdmissibleUnique (L R : ℝ) (f : E → ℝ) (x₀ xstar : E) : Prop
    extends Admissible L R f x₀ xstar where
  /-- the minimizer is unique -/
  unique_min : ∀ x : E, f x = f xstar → x = xstar

namespace Admissible

variable {L R : ℝ} {f : E → ℝ} {x₀ xstar : E}



end Admissible

end FullFormalization


