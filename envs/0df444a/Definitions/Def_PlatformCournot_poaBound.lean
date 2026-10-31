-- Prove2me | Definitions.Def_PlatformCournot_poaBound
-- name    : PlatformCournot_poaBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:23.616812+00:00
-- url     : https://prove2.me/theorems/eb547eee-1979-42c4-a546-0c51574ff82b
-- title:
--   The bound $\frac32\bigl(1-\frac1{3n+6}\bigr)$ of Theorem 1
-- statement:
--   For $n$ firms, the price of anarchy bound of Theorem 1 is
--
--   $$b(n)=\frac32\Bigl(1-\frac{1}{3n+6}\Bigr)=\frac{3n+5}{2(n+2)}.$$
--
--   It equals $4/3$ for $n=1$ and increases to $3/2$ as $n\to\infty$.
--
--   **Formalization Note** Written as printed, with $n$ cast to a real number.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Theorem 1, p.15

import Mathlib

namespace PlatformCournot

/-- **The price of anarchy bound of Theorem 1, `(3/2)(1 − 1/(3n+6))`.**
Pang et al., arXiv:1903.04574v3, Theorem 1, p.15: "ρ(F × M,C) ≤ (3/2)(1 − 1/(3n + 6))."

**Formalization Note** Written as printed, with `n : ℕ` cast to `ℝ`; it equals
`(3n + 5) / (2(n + 2))`. -/
noncomputable def poaBound (n : ℕ) : ℝ :=
  (3 / 2) * (1 - 1 / (3 * (n : ℝ) + 6))

end PlatformCournot


