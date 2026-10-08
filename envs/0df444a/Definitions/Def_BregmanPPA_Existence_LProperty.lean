-- Prove2me | Definitions.Def_BregmanPPA_Existence_LProperty
-- name    : BregmanPPA_Existence_LProperty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:54.698074+00:00
-- url     : https://prove2.me/theorems/f00e1f10-0f89-41de-8d12-aec8bac89546
-- title:
--   Definition 2 — the L-property; trimonotone (3-cyclically monotone) operators
-- statement:
--   Let $R:H\to2^H$ be an operator on a real inner product space $H$.
--
--   1. $R$ is **trimonotone** if for all pairs $(x_0,y_0),(x_1,y_1),(x_2,y_2)$ in its graph
--   $$
--   \langle x_1-x_0,y_0\rangle+\langle x_2-x_1,y_1\rangle+\langle x_0-x_2,y_2\rangle\le0 .
--   $$
--   2. (Definition 2, p. 208) A monotone operator $R$ has the **L-property** if, for all $u\in\operatorname{dom}R$ and $v\in\operatorname{im}R$,
--   $$
--   \inf\{\langle x-u,\,y-v\rangle : x\in\operatorname{dom}R,\ y\in Rx\}>-\infty .
--   $$
--
--   Trimonotonicity is cyclic monotonicity for cycles of length three; taking $x_2=x_0$ shows that it implies monotonicity. The L-property is the hypothesis on the operator $B$ in the Brézis–Haraux range theorem (Theorem 3).
--
--   **Formalization Note** The paper uses the word *trimonotone* without defining it; the definition is that of Brézis and Haraux [5] (their "3-monotone"), i.e. Rockafellar's cyclic monotonicity with three points. The L-property is encoded as monotonicity of $R$ together with boundedness from below of the set of real numbers $\langle x-u,y-v\rangle$, $y\in Rx$; the condition $x\in\operatorname{dom}R$ is implied by $y\in Rx$. Monotone, $\operatorname{dom}$ and $\operatorname{im}$ are the published `ThreeOpSplitting.Convergence.IsMonotoneOp`, `dom` and `DouglasRachfordPPA.GenDR.imOp`.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 208, Definition 2 and Theorem 2 (trimonotone, after Brézis–Haraux [5])

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace BregmanPPA.Existence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A trimonotone (3-cyclically monotone) operator, in the sense of Brézis–Haraux [5]: for all
`(x₀, y₀), (x₁, y₁), (x₂, y₂)` in the graph of `R`,
`⟪x₁ − x₀, y₀⟫ + ⟪x₂ − x₁, y₁⟫ + ⟪x₀ − x₂, y₂⟫ ≤ 0`. -/
def IsTrimonotone (R : H → Set H) : Prop :=
  ∀ x₀ x₁ x₂ y₀ y₁ y₂ : H, y₀ ∈ R x₀ → y₁ ∈ R x₁ → y₂ ∈ R x₂ →
    inner ℝ (x₁ - x₀) y₀ + inner ℝ (x₂ - x₁) y₁ + inner ℝ (x₀ - x₂) y₂ ≤ 0

/-- Definition 2 (p. 208): a monotone operator `R` has the L-property if, for all `u ∈ dom R`
and `v ∈ im R`, `inf {⟪x − u, y − v⟫ | x ∈ dom R, y ∈ R x} > −∞`. -/
def HasLProperty (R : H → Set H) : Prop :=
  IsMonotoneOp R ∧ ∀ u ∈ dom R, ∀ v ∈ imOp R,
    BddBelow {t : ℝ | ∃ x y, y ∈ R x ∧ t = inner ℝ (x - u) (y - v)}

end BregmanPPA.Existence


