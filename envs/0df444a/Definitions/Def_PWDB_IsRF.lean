-- Prove2me | Definitions.Def_PWDB_IsRF
-- name    : PWDB_IsRF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:16.528955+00:00
-- url     : https://prove2.me/theorems/26209315-5a84-4a6b-95d4-7024e207e929
-- title:
--   Assumption (RF): convex–concave saddle functions
-- statement:
--   A function $f : E \times F \to \mathbb R$ satisfies **(RF)** if $x \mapsto f(x,z)$ is convex for every $z$ and $z \mapsto f(x,z)$ is concave for every $x$.
--
--   The paper states (RF) as: $f(\cdot, z)$ is proper, closed and convex for every $z$, and $-f(x,\cdot)$ is proper, closed and convex for every $x$; it then shows (p.8) that this forces $f$ to be real-valued. On finite-dimensional spaces a real-valued convex function is continuous, so for real-valued $f$ the two formulations coincide.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), §3, assumption (RF) and the paragraph after it, p.8

import Mathlib

namespace PWDB

/-- **Assumption (RF)** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, §3, p.8): "The function
`fi(x, zi)` is proper, closed and convex in `x` for every fixed `zi`, and `−fi(x, zi)` is proper,
closed and convex in `zi` for every fixed `x` across all `i ∈ I0`."

`IsRF g` says that the real-valued function `g` is convex in `x` for every fixed `z` and concave in
`z` for every fixed `x`.

**Formalization Note** The paper shows right after (RF) (p.8) that (RF) forces `fi` to be
real-valued: properness in `x` excludes `−∞`, properness of `−fi` in `zi` excludes `+∞`.
Conversely a real-valued convex function on a finite-dimensional space is continuous, hence proper
and closed. So for a function `g : E → F → ℝ` on finite-dimensional spaces, (RF) is exactly
convexity in `x` and concavity in `z`. -/
def IsRF {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (g : E → F → ℝ) : Prop :=
  (∀ z, ConvexOn ℝ Set.univ (fun x => g x z)) ∧ (∀ x, ConcaveOn ℝ Set.univ (fun z => g x z))

end PWDB


