-- Prove2me | Definitions.Def_TensorAHPE_epsSubdiff
-- name    : TensorAHPE_epsSubdiff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:21.321915+00:00
-- url     : https://prove2.me/theorems/665f0bc4-dade-4acc-b327-70fc0cad4ffc
-- title:
--   The $\epsilon$-subdifferential $\partial_\epsilon h(x)$
-- statement:
--   Let $h : \mathbb R^n \to (-\infty,+\infty]$ and $\epsilon \in \mathbb R$. The **$\epsilon$-subdifferential** of $h$ at $x$ is
--
--   $$\partial_\epsilon h(x) := \{u \in \mathbb R^n \;:\; h(y) \ge h(x) + \langle y-x, u\rangle - \epsilon \ \text{ for all } y \in \mathbb R^n\}.$$
--
--   For $\epsilon = 0$ it is the subdifferential of convex analysis. It describes the inexact optimality conditions used by the approximate subproblem solutions of the paper (Definition 2.1) and by the A-HPE framework (condition (3.1)).
--
--   **Formalization Note** The inequality is read in the extended reals, with the real number $\langle y-x,u\rangle-\epsilon$ added to $h(x)$. For a proper $h$ the set is empty wherever $h(x)=+\infty$, and empty when $\epsilon<0$ and $h(x)$ is finite; the paper only uses $\epsilon \ge 0$.
-- source:
--   Jiang, Wang & Zhang, An Optimal High-Order Tensor Method for Convex Optimization, arXiv:1812.06557v3, §2, p.6 (definition of ∂_ε h(x))

import Mathlib

namespace TensorAHPE

/-- **The ε-subdifferential.**
Jiang, Wang & Zhang, arXiv:1812.06557v3, §2, p.6: "For a scalar ε ≥ 0, the ε-subdifferential of
a proper closed convex function h is defined as:
∂_ε h(x) := {u | h(y) ≥ h(x) + ⟨y − x, u⟩ − ε, ∀ y ∈ ℝⁿ}."

**Formalization Note.** `h` is `EReal`-valued and the inequality is read in `EReal`, with the real
number `⟨y − x, u⟩ − ε` added to `h x`. For a proper function (never `−∞`, somewhere finite) the
set is empty at every `x` with `h x = +∞`, since the inequality would force `h y = +∞` for all
`y`; it is also empty when `ε < 0` and `h x` is finite (take `y = x`). The definition is the
page's for every `ε`; the paper only uses `ε ≥ 0`. -/
def epsSubdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → EReal) (ε : ℝ) (x : E) : Set E :=
  {u | ∀ y, h x + ((inner ℝ (y - x) u - ε : ℝ) : EReal) ≤ h y}

end TensorAHPE


