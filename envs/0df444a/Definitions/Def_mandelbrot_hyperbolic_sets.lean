-- Prove2me | Definitions.Def_mandelbrot_hyperbolic_sets
-- name    : mandelbrot_hyperbolic_sets
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T21:41:55.55218+00:00
-- url     : https://prove2.me/theorems/31235284-4c24-4fef-bfd8-7c1910796a6a
-- title:
--   Hyperbolic sets of quadratic polynomials $z \mapsto z^2 + c$
-- statement:
--   Let $f_c(z) = z^2 + c$. A set $K \subseteq \mathbb{C}$ is a **hyperbolic set** for $f_c$ (`Mandelbrot.IsHyperbolicSet c K`) if
--
--   1. $K$ is compact;
--   2. $K$ is forward invariant: $f_c(K) \subseteq K$;
--   3. some iterate is uniformly expanding on $K$: there is $n \geq 1$ with $|(f_c^{n})'(z)| > 1$ for every $z \in K$.
--
--   This is the notion used by Shishikura to define the *hyperbolic dimension* of a Julia set, $\operatorname{hyp\text{-}dim} J(f_c) = \sup\{\dim_H K : K \text{ a hyperbolic set of } f_c\}$. A hyperbolic set is automatically contained in the Julia set $J(f_c)$: the derivatives of the iterates grow exponentially along $K$ while the orbits stay bounded, which is impossible at a point of the Fatou set by normality. For a compact subset of $\mathbb{C}$ the Euclidean and spherical metrics are comparable, so the condition matches the spherical-metric version in Shishikura's paper up to passing to a further iterate. Examples: any repelling periodic cycle, and for $c$ outside $M$ the whole Julia set.
-- source:
--   M. Shishikura, The Hausdorff dimension of the boundary of the Mandelbrot set and Julia sets, Ann. of Math. (2) 147 (1998), 225-267, https://arxiv.org/abs/math/9201282 (notion of hyperbolic sets and hyperbolic dimension)

import Definitions.Def_mandelbrot_sets

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- A set `K ⊆ ℂ` is a *hyperbolic set* for the quadratic polynomial `z ↦ z ^ 2 + c` if it is
compact, forward invariant (`f_c(K) ⊆ K`), and some iterate `f_c^[n]` (`n > 0`) is uniformly
expanding on `K`: `‖(f_c^[n])'(z)‖ > 1` for every `z ∈ K`. Such a set is automatically contained
in the Julia set of `f_c`. -/
def IsHyperbolicSet (c : ℂ) (K : Set ℂ) : Prop :=
  IsCompact K ∧ MapsTo (fun z ↦ z ^ 2 + c) K K ∧
    ∃ n : ℕ, 0 < n ∧ ∀ z ∈ K, 1 < ‖deriv (fun z ↦ z ^ 2 + c)^[n] z‖

end Mandelbrot


