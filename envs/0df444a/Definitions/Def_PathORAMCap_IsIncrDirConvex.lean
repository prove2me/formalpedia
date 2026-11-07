-- Prove2me | Definitions.Def_PathORAMCap_IsIncrDirConvex
-- name    : PathORAMCap_IsIncrDirConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:10.269637+00:00
-- url     : https://prove2.me/theorems/eaf7059f-fd27-4956-917b-a2b0b38e6d0e
-- title:
--   Increasing directionally convex functions on $[0,\infty)^d$
-- statement:
--   A function $f$ on the nonnegative orthant $[0,\infty)^d$ is **increasing and directionally convex** if it is coordinatewise increasing and
--
--   $$f(z+h+k)-f(z+k)\ge f(z+h)-f(z)\qquad(z,h,k\ge0):$$
--
--   adding a load has at least as large an effect when the background load is larger. Joint convexity is not required.
--
--   The exponential overflow cost $A\mapsto u^{D^{(4)}(A)}$ has this property, which is what the Poissonization step of the upper bound uses.
--
--   **Formalization Note** $f$ is a real function on $\mathbb R^d$ and only its values on the orthant enter. Coordinatewise monotonicity on the orthant is stated as monotonicity for the product order there, which is equivalent.
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), §4.3.3 (a), p.22 (PDF p.25), eq. (25)

import Mathlib

set_option autoImplicit false

namespace PathORAMCap

/-- **Increasing and directionally convex** functions on the nonnegative orthant (Chang, Au, *The
Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…),
§4.3.3 (a), p.22 (PDF p.25), (25)): "f(z + h + k) − f(z + k) ≥ f(z + h) − f(z) (z, h, k ≥ 0). … A
function f on nonnegative vectors is called increasing and directionally convex here if it is
coordinatewise increasing and satisfies (25)."

**Formalization Note.** `f` is a real function on `Fin d → ℝ`; only its values on `[0, ∞)^d` enter.
Coordinatewise increasing on the orthant is stated as monotonicity for the product order on the
orthant (the two are equivalent there). No joint convexity is required. -/
def IsIncrDirConvex {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Prop :=
  (∀ x y : Fin d → ℝ, 0 ≤ x → x ≤ y → f x ≤ f y) ∧
    ∀ z h k : Fin d → ℝ, 0 ≤ z → 0 ≤ h → 0 ≤ k → f (z + h) - f z ≤ f (z + h + k) - f (z + k)

end PathORAMCap


