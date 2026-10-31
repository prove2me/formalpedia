-- Prove2me | Definitions.Def_FDivToolkit_IsAdmissibleH
-- name    : FDivToolkit_IsAdmissibleH
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:12.087633+00:00
-- url     : https://prove2.me/theorems/051b291f-1190-443b-b1d2-206298effcc3
-- title:
--   Generating functions $H$ and the inverse $H^{-1}$
-- statement:
--   A **generating function** is a continuous, strictly increasing function $H:\mathbb R\to\mathbb R$ with $\lim_{y\to\infty}H(y)=\infty$ and $H(0)=0$. Such an $H$ maps $\mathbb R$ bijectively onto the ray $(L,\infty)$, where $L=\lim_{y\to-\infty}H(y)\in[-\infty,0)$, and $H^{-1}$ is the inverse of this bijection.
--
--   The class of divergences of the paper is parametrized by $H$, and the worst-case density is explicit through $H^{-1}$.
--
--   **Formalization Note** `Hinv H` is `Function.invFun H`, a true inverse on the range of $H$ and arbitrary off it. The mission applies it only on the range.
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), §2.1, p.5; Proposition 1, p.8

import Mathlib

open Filter

namespace FDivToolkit

/-- The class of generating functions `H` (Kruse, Schneider & Schweizer, SSRN 3680475
(Aug 25, 2020), §2.1, p.5): "Let `H : ℝ → ℝ` be a continuous, strictly increasing function such
that `lim_{y→∞} H(y) = ∞` and `H(0) = 0`." -/
structure IsAdmissibleH (H : ℝ → ℝ) : Prop where
  continuous : Continuous H
  strictMono : StrictMono H
  tendsto_atTop : Tendsto H atTop atTop
  map_zero : H 0 = 0

/-- The inverse `H⁻¹` of `H` (Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020),
Proposition 1, p.8).

**Formalization Note.** For an admissible `H`, the range of `H` is the open ray `(L, ∞)` with
`L = lim_{y→−∞} H(y)`. `Hinv H` is a genuine inverse on that range and an arbitrary value off it,
so it is only ever applied to points of the range: nonnegative points, or points tested by
`· ∈ Set.range H` as in `gwc`. -/
noncomputable def Hinv (H : ℝ → ℝ) : ℝ → ℝ :=
  Function.invFun H

end FDivToolkit


