-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_IsIntegralExt
-- name    : CombOpt_MinCostFlow_IsIntegralExt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:22.460511+00:00
-- url     : https://prove2.me/theorems/c641a745-eb5d-4396-b1f9-d2b284a87c00
-- title:
--   Integrality of an extended-real bound
-- statement:
--   A bound $a\in\mathbb R\cup\{\infty\}$ (a capacity) or $a\in\mathbb R\cup\{-\infty\}$ (a lower bound) is **integral** if, whenever it is finite, it is an integer. A vector of bounds is integral when each component is; in the book's words, "we use '$u$ is integral' to mean that the finite components of $u$ are integers."
--
--   **Formalization Note** Bounds are extended reals (`EReal`); `IsIntegralExt a` holds for $a=\pm\infty$ and for integer $a$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, p. 39 (PDF p. 48)

import Mathlib

namespace CombOpt.MinCostFlow

/-- **Integrality of an extended-real bound.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, p. 39 (PDF p. 48): "We use 'u is integral' to mean that the finite components of u
are integers." A capacity `u_e ∈ ℝ ∪ {∞}` or a lower bound `ℓ_e ∈ ℝ ∪ {−∞}` is *integral* when, if
finite, it is an integer.

**Formalization Note.** Bounds are elements of `EReal`; `IsIntegralExt a` holds when `a = ⊤`,
`a = ⊥`, or `a` is (the image of) an integer. -/
def IsIntegralExt (a : EReal) : Prop :=
  a ≠ ⊤ → a ≠ ⊥ → ∃ k : ℤ, a = ((k : ℝ) : EReal)

end CombOpt.MinCostFlow


