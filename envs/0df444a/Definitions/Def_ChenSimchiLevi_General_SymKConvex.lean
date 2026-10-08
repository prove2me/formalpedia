-- Prove2me | Definitions.Def_ChenSimchiLevi_General_SymKConvex
-- name    : ChenSimchiLevi_General_SymKConvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:45:18.669565+00:00
-- url     : https://prove2.me/theorems/fa8c2189-d0d5-4469-8312-4e32424b8f43
-- title:
--   Symmetric $k$-convexity and $k$-concavity
-- statement:
--   A real-valued function $f$ is **symmetrically $k$-convex** if for every $x_0,x_1\in\mathbb R$ and $\lambda\in[0,1]$,
--   $$f((1-\lambda)x_0+\lambda x_1)\le(1-\lambda)f(x_0)+\lambda f(x_1)+\max\{\lambda,1-\lambda\}k.$$
--   It is symmetrically $k$-concave when $-f$ has this property.
--
--   Unlike the ordered-chord $k$-convexity used for additive demand, this definition treats the endpoints symmetrically. It is the structural property preserved by the general-demand recursion.
--
--   **Formalization Note** The definition itself accepts any real $k$; the paper's standing condition $k\ge0$ appears in the theorems that use it.
-- source:
--   Chen, Simchi-Levi, Operations Research 52(6) (2004), p. 891, Definition 4.1, equation (8)

import Mathlib

set_option autoImplicit false

namespace ChenSimchiLevi.General

/-- Definition 4.1, equation (8). The standing restriction `0 ≤ k` belongs to theorems. -/
def SymKConvex (k : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x₀ x₁ : ℝ, ∀ l ∈ Set.Icc (0 : ℝ) 1,
    f ((1 - l) * x₀ + l * x₁) ≤
      (1 - l) * f x₀ + l * f x₁ + max l (1 - l) * k

/-- Symmetric `k`-concavity means symmetric `k`-convexity of the negative. -/
def SymKConcave (k : ℝ) (f : ℝ → ℝ) : Prop :=
  SymKConvex k (fun x => -f x)

end ChenSimchiLevi.General


