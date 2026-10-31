-- Prove2me | Definitions.Def_DualTwoStageRO_primalValue
-- name    : DualTwoStageRO_primalValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:56.598133+00:00
-- url     : https://prove2.me/theorems/6e4dfe8e-8e0a-47ed-9f32-5bc70df4fdf8
-- title:
--   Worst-case value of a here-and-now decision in problem (1)
-- statement:
--   Fix the data of (1)–(3). For $x\in\mathbb R^{n_x}$ and $\zeta\in\mathbb R^{n_\zeta}$ the **inner feasible set** is
--
--   $$Y(x,\zeta)=\bigl\{y\in\mathbb R^{n_y}:\ \zeta^\top F_{i\cdot}(x)+f_i(x)+g_i(y)\le0,\ i=1,\dots,m_1,\ \ A(x)\zeta+By=b(x)\bigr\},$$
--
--   the **inner value** is $\inf_{y\in Y(x,\zeta)}\{f_0(x)+g_0(y)\}$, and the **worst-case value** of $x$ is
--
--   $$\Phi(x)=\sup_{\zeta\in\mathcal U}\ \inf_{y\in Y(x,\zeta)}\ \bigl\{f_0(x)+g_0(y)\bigr\}.$$
--
--   Problem (1) is $\inf_{x\in\mathcal X}\Phi(x)$, and $x$ is feasible for (1) when $\Phi(x)<+\infty$.
--
--   **Formalization Note** All values are in `EReal`: the inner value is $+\infty$ when $Y(x,\zeta)=\emptyset$ and may be $-\infty$; $\Phi(x)$ may be $+\infty$ when $\mathcal U$ is unbounded. The module also defines `innerFeasible` and `innerValue`.
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), §1.1, p.1794, problem (1)

import Mathlib
import Definitions.Def_DualTwoStageRO_Problem

namespace DualTwoStageRO

open Matrix

variable {nx ny nζ m1 m2 p : ℕ}

/-- The feasible set of the inner (wait-and-see) problem of (1) at `(x, ζ)`
(de Ruiter, Zhen, den Hertog, Operations Research 71(5), 2023, (1), p.1794):
`{y ∈ ℝ^{ny} | ζ⊤F_i·(x) + f_i(x) + g_i(y) ≤ 0, i = 1,…,m1, A(x)ζ + By = b(x)}`.
The paper's constraint `i` (`i = 1,…,m1`) is `i : Fin m1`, with `f i.succ`, `g i.succ`. -/
def innerFeasible (P : Problem nx ny nζ m1 m2 p) (x : Fin nx → ℝ) (ζ : Fin nζ → ℝ) :
    Set (Fin ny → ℝ) :=
  {y | (∀ i : Fin m1, ζ ⬝ᵥ (fun j => P.F i j x) + P.f i.succ x + P.g i.succ y ≤ 0) ∧
    P.A x *ᵥ ζ + P.B *ᵥ y = P.b x}

/-- The inner value `inf_y {f_0(x) + g_0(y) | y feasible}` of (1) at `(x, ζ)`, in `EReal`:
`⊤` when no `y` is feasible, possibly `⊥`. -/
noncomputable def innerValue (P : Problem nx ny nζ m1 m2 p) (x : Fin nx → ℝ) (ζ : Fin nζ → ℝ) :
    EReal :=
  ⨅ y ∈ innerFeasible P x ζ, ((P.f 0 x + P.g 0 y : ℝ) : EReal)

/-- **Worst-case value of a here-and-now decision in (1)**, `sup_{ζ∈U} inf_y {…}`.
de Ruiter, Zhen, den Hertog, *Technical Note—Dual Approach for Two-Stage Robust Nonlinear
Optimization*, Operations Research 71(5), 2023, (1), p.1794:
`inf_{x∈X} sup_{ζ∈U} inf_y { f0(x) + g0(y) | ζ⊤F_i·(x) + f_i(x) + g_i(y) ≤ 0, i = 1,…,m1,
A(x)ζ + By = b(x) }`. The optimal value of (1) is `⨅ x ∈ P.X, primalValue P x`.

**Formalization Note.** Every value is in `EReal`: the infimum over an empty feasible set is `⊤`,
the supremum may be `⊤` (unbounded `U`) and the inner infimum may be `⊥`. "x is feasible for (1)"
is read as `primalValue P x < ⊤`. -/
noncomputable def primalValue (P : Problem nx ny nζ m1 m2 p) (x : Fin nx → ℝ) : EReal :=
  ⨆ ζ ∈ P.U, innerValue P x ζ

end DualTwoStageRO


