-- Prove2me | Definitions.Def_RadGauss_LipschitzGaussian_cubeExtension
-- name    : RadGauss_LipschitzGaussian_cubeExtension
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:40:22.822156+00:00
-- url     : https://prove2.me/theorems/9eabb9ca-0b55-46b4-af1a-ed93120990bc
-- title:
--   Extension of a boolean function g : {±1}^k → {±1} to ℝ^k by tents of radius 1 (proof of Theorem 16)
-- statement:
--   Let $g : \{\pm1\}^k \to \{\pm1\}$ be a boolean function, and view the cube $\{\pm1\}^k$ as a subset of $\mathbb R^k$ with the Euclidean norm $\|\cdot\|$. The **extension** of $g$ is the function $g : \mathbb R^k \to \mathbb R$ defined by
--
--   $$
--   g(x) = \begin{cases} (1 - \|x - a\|)\, g(a) & \text{if } \|x - a\| < 1 \text{ for some } a \in \{\pm1\}^k,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   It places a tent of height $g(a)$ and radius $1$ at each vertex $a$ of the cube. It is the function $\phi$ to which Bartlett and Mendelson apply Theorem 14 in the proof of Theorem 16.
--
--   **Formalization Note** The vertex of $\mathbb R^k$ given by a sign vector $a$ is `cubeVertex a`. When some vertex lies within distance $<1$ of $x$, one such vertex is selected by choice; that it is unique (so the choice does not matter) is part of the companion theorem `cubeExtension_spec`, not of this definition.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 472 (PDF p. 10), proof of Theorem 16

import Mathlib

namespace RadGauss.LipschitzGaussian

/-- The vertex of the cube `{±1}^k ⊂ ℝ^k` (with its Euclidean structure) given by a sign vector
`a : Fin k → ℤˣ`. -/
noncomputable def cubeVertex {k : ℕ} (a : Fin k → ℤˣ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => ((a j : ℤ) : ℝ))

/-- **The extension of a boolean function** (proof of Theorem 16, p. 472). For
`g : {±1}^k → {±1}` and `x ∈ ℝ^k`, `g(x) = (1 − ‖x − a‖) g(a)` if `‖x − a‖ < 1` for some
`a ∈ {±1}^k`, and `g(x) = 0` otherwise; `‖·‖` is the Euclidean norm. When such an `a` exists,
one of them is selected by choice; the page observes that it is unique. -/
noncomputable def cubeExtension {k : ℕ} (g : (Fin k → ℤˣ) → ℤˣ) (x : EuclideanSpace ℝ (Fin k)) :
    ℝ := by
  classical
  exact if h : ∃ a : Fin k → ℤˣ, ‖x - cubeVertex a‖ < 1 then
      (1 - ‖x - cubeVertex h.choose‖) * ((g h.choose : ℤ) : ℝ)
    else 0

end RadGauss.LipschitzGaussian


