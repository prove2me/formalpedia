-- Prove2me | Definitions.Def_GradSuffice_IsValidOracle
-- name    : GradSuffice_IsValidOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:16.777175+00:00
-- url     : https://prove2.me/theorems/80ab1cc4-c593-4a17-8218-ae3d63b9b6ba
-- title:
--   Valid first-order oracle
-- statement:
--   Let $(U,f)$ be an objective on $W$. A map $g:X\to X^\star$ is a **valid first-order oracle** for it if $g(w)$ is a subgradient of $f$ at every $w\in W$:
--   $$f(u)\ge f(w)+g(w)\cdot(u-w)\qquad\text{for all } w\in W,\ u\in U.$$
--   Queried at $w$, the oracle answers the pair $(f(w),g(w))$. When the subdifferential has several elements any selection is allowed, and the algorithms must succeed for every valid selection.
--
--   **Formalization Note** The oracle is a fixed (memoryless) selection $w\mapsto g(w)$, as in the paper's description of an oracle that receives a point and returns a pair.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, pp.3–4, Eq. (1)

import Mathlib
import Definitions.Def_GradSuffice_Objective

namespace GradSuffice

/-- **Valid first-order oracle.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.4: "a first-order oracle `O` receives a point
`w ∈ W` and returns a pair `(f(w), ξ)`, where `ξ ∈ ∂f(w)`. When the subdifferential contains several
elements, the oracle may return any of them"; `∂f(w₀)` is the set of `ξ ∈ X⋆` with
`f(w) ≥ f(w₀) + ξ · (w − w₀)` for every `w` in the domain (Eq. (1), p.3).

**Formalization Note.** The oracle is a selection `g : X → StrongDual ℝ X` (the value part of the
answer is `f w` itself); validity is the subgradient inequality (1) at every `w ∈ W`, tested on the
whole domain `U` of the objective. -/
def IsValidOracle {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {W : Set X} (F : Objective X W) (g : X → StrongDual ℝ X) : Prop :=
  ∀ w ∈ W, ∀ u ∈ F.U, F.f w + g w (u - w) ≤ F.f u

end GradSuffice


