-- Prove2me | Definitions.Def_MetodosNumericos_edoDefs
-- name    : MetodosNumericos_edoDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T16:33:20.39835+00:00
-- url     : https://prove2.me/theorems/416e3243-c067-4ffb-b75e-374c3b30bb77
-- title:
--   Euler and Picard iterations for an initial value problem
-- statement:
--   The Euler iterates $y_{i+1} = y_i + h f(x_0+ih, y_i)$ with step $h$, and the Picard iterates $y_0(x) = y_0$, $y_{k+1}(x) = y_0 + \\int_{x_0}^{x} f(t,y_k(t))\\,dt$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 9, §9.5 p. 186 (Picard) and §9.9 p. 192 (Euler).

import Mathlib

namespace MetodosNumericos

/-- Euler's method for the initial value problem `y' = f(x, y)`, `y(x₀) = y₀`,
with step `h`: `y₀` given and `y_{i+1} = yᵢ + h f(xᵢ, yᵢ)` where `xᵢ = x₀ + i h`. -/
noncomputable def eulerSeq (f : ℝ → ℝ → ℝ) (x0 y0 h : ℝ) : ℕ → ℝ
  | 0 => y0
  | i + 1 => eulerSeq f x0 y0 h i + h * f (x0 + i * h) (eulerSeq f x0 y0 h i)

/-- The Picard iterates for `y' = f(x, y)`, `y(x₀) = y₀`:
`y₀(x) = y₀` and `y_{k+1}(x) = y₀ + ∫_{x₀}^{x} f(t, y_k(t)) dt`. -/
noncomputable def picardSeq (f : ℝ → ℝ → ℝ) (x0 y0 : ℝ) : ℕ → (ℝ → ℝ)
  | 0 => fun _ => y0
  | k + 1 => fun x => y0 + ∫ t in x0..x, f t (picardSeq f x0 y0 k t)

end MetodosNumericos


