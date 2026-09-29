-- Prove2me | Definitions.Def_mandelbrot_sets
-- name    : mandelbrot_sets
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T01:27:04.879745+00:00
-- url     : https://prove2.me/theorems/8f17f9ed-9c1e-4203-a9bc-493d235497ae
-- title:
--   The Mandelbrot and Multibrot sets, and attracting cycles
-- statement:
--   Fix a natural number $n$ and a parameter $c \in \mathbb{C}$, and iterate the map $f_{n,c}(z) = z^{n} + c$ starting from the critical point $z = 0$.
--
--   **Multibrot set.** $M_n$ is the set of parameters $c$ whose critical orbit $\left(f_{n,c}^{\,k}(0)\right)_{k \ge 0}$ does *not* escape to infinity; escape to infinity is expressed as convergence of the orbit along the cobounded filter, i.e. the orbit eventually leaves every bounded set.
--
--   **Mandelbrot set.** $M = M_2$ is the case $n = 2$, the classical Mandelbrot set: the set of $c \in \mathbb{C}$ for which the orbit of $0$ under $z \mapsto z^{2} + c$ stays bounded.
--
--   **Attracting cycles.** For a map $f : \mathbb{C} \to \mathbb{C}$, a point $z$ lies on an attracting cycle of period $n$ when $n > 0$, $f^{n}(z) = z$, the iterate $f^{n}$ is complex differentiable at $z$, and the multiplier satisfies $\left| (f^{n})'(z) \right| < 1$. A parameter $c$ is called *hyperbolic* when $z \mapsto z^{2} + c$ has such a cycle.
-- source:
--   A. Douady and J. H. Hubbard, Etude dynamique des polynomes complexes (Orsay notes), 1984/85; https://en.wikipedia.org/wiki/Mandelbrot_set ; https://en.wikipedia.org/wiki/Multibrot_set

import Mathlib

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- The Multibrot set of power `n` is the set of all parameters `c : ℂ` for which `0` does not
escape to infinity under repeated application of `z ↦ z ^ n + c`. -/
def multibrotSet (n : ℕ) : Set ℂ :=
  {c | ¬ Tendsto (fun k ↦ (fun z ↦ z ^ n + c)^[k] 0) atTop (cobounded ℂ)}

/-- The Mandelbrot set is the special case of the Multibrot set for `n = 2`: the set of all
parameters `c : ℂ` for which `0` does not escape to infinity under repeated application of
`z ↦ z ^ 2 + c`. -/
abbrev mandelbrotSet : Set ℂ := multibrotSet 2

/-- We say that `z : ℂ` is part of an attracting cycle of period `n` of `f : ℂ → ℂ` if `n > 0`,
`z` is an `n`-periodic point (i.e. `f^[n] z = z`), `f^[n]` is differentiable at `z`, and the
multiplier `‖deriv f^[n] z‖` is strictly less than one. -/
def IsAttractingCycle (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : Prop :=
  (0 < n) ∧ f.IsPeriodicPt n z ∧ DifferentiableAt ℂ f^[n] z ∧ ‖deriv f^[n] z‖ < 1

end Mandelbrot


