-- Prove2me | Definitions.Def_DualTwoStageRO_Assumption1
-- name    : DualTwoStageRO_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:01.989691+00:00
-- url     : https://prove2.me/theorems/53c0801a-4fe2-4c94-8d9a-38bd6f1cde8d
-- title:
--   Assumption 1 (relatively complete recourse, strict for non-affine constraints)
-- statement:
--   **Assumption 1 (Relatively Complete Recourse).** For all $x\in\mathcal X$ and all $\zeta\in\mathcal U$ there exists $y\in\mathbb R^{n_y}$ with
--
--   $$\zeta^\top F_{i\cdot}(x)+f_i(x)+g_i(y)\le0,\quad i=1,\dots,m_1,\qquad A(x)\zeta+By=b(x),$$
--
--   and $\zeta^\top F_{i\cdot}(x)+f_i(x)+g_i(y)<0$ for every $i=1,\dots,m_1$ for which $g_i$ is nonlinear.
--
--   The module splits this into `RecourseAt` (the condition at one pair $(x,\zeta)$), `Assumption1At` (for all $\zeta\in\mathcal U$ at one $x$) and `Assumption1` (for all $x\in\mathcal X$). It is a refined Slater condition for the inner problem of (1), which is what makes the first dualization exact.
--
--   **Formalization Note** "$g_i$ is nonlinear" is read as "$g_i$ is not affine" (`IsAffineFun`). Strictness is never required of the equality constraint.
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), Assumption 1, p.1795

import Mathlib
import Definitions.Def_DualTwoStageRO_primalValue
import Definitions.Def_DualTwoStageRO_IsAffineFun

namespace DualTwoStageRO

open Matrix

variable {nx ny nζ m1 m2 p : ℕ}

/-- The recourse condition of Assumption 1 at one pair `(x, ζ)`: some `y ∈ ℝ^{ny}` satisfies the
constraints of (1), strictly for every `i = 1,…,m1` with `g_i` not affine. -/
def RecourseAt (P : Problem nx ny nζ m1 m2 p) (x : Fin nx → ℝ) (ζ : Fin nζ → ℝ) : Prop :=
  ∃ y ∈ innerFeasible P x ζ, ∀ i : Fin m1, ¬ IsAffineFun (P.g i.succ) →
    ζ ⬝ᵥ (fun j => P.F i j x) + P.f i.succ x + P.g i.succ y < 0

/-- Assumption 1 at one here-and-now decision `x`: `RecourseAt P x ζ` for every `ζ ∈ U`. -/
def Assumption1At (P : Problem nx ny nζ m1 m2 p) (x : Fin nx → ℝ) : Prop :=
  ∀ ζ ∈ P.U, RecourseAt P x ζ

/-- **Assumption 1 (Relatively Complete Recourse).**
de Ruiter, Zhen, den Hertog, *Technical Note—Dual Approach for Two-Stage Robust Nonlinear
Optimization*, Operations Research 71(5), 2023, p.1795: "For all x ∈ X and all ζ ∈ U, there exists a
y ∈ R^{ny}, such that ζ⊤F_i·(x) + f_i(x) + g_i(y) ≤ 0, i = 1,…,m1, A(x)ζ + By = b(x), and for all
i = 1,…,m1 for which g_i is nonlinear, we have ζ⊤F_i·(x) + f_i(x) + g_i(y) < 0."

**Formalization Note.** "g_i is nonlinear" is read as "g_i is not affine" (`IsAffineFun`). -/
def Assumption1 (P : Problem nx ny nζ m1 m2 p) : Prop :=
  ∀ x ∈ P.X, Assumption1At P x

end DualTwoStageRO


