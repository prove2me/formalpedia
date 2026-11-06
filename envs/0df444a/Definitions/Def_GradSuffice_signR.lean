-- Prove2me | Definitions.Def_GradSuffice_signR
-- name    : GradSuffice_signR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:20.907295+00:00
-- url     : https://prove2.me/theorems/f95b01e3-1061-4ce2-b5a7-256aadc2d5d3
-- title:
--   Sign of a Boolean, $\sigma\in\{-1,+1\}$
-- statement:
--   A **sign** is an element $\sigma\in\{-1,+1\}$. Branches of complete binary trees are strings of signs: $-1$ labels the left edge and $+1$ the right edge of every internal node.
--
--   Signs are encoded by Booleans, and $\mathrm{signR}(b)$ is the real number they stand for: $\mathrm{signR}(\mathrm{true})=+1$ and $\mathrm{signR}(\mathrm{false})=-1$.
--
--   **Formalization Note** Signs are `Bool` throughout the mission, with `true` standing for $+1$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.5 and §3.1, p.7

import Mathlib

namespace GradSuffice

/-- **Signs as reals.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.5 and §3.1, p.7: signs `σᵢ ∈ {−1, +1}`.

**Formalization Note.** A sign is a `Bool`; `signR true = +1` (right edge, `+1`) and
`signR false = −1` (left edge, `−1`). -/
def signR (b : Bool) : ℝ := if b then 1 else -1

end GradSuffice


