-- Prove2me | Definitions.Def_CK_CKLaneA1_JnConvex
-- name    : CK_CKLaneA1_JnConvex
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:06:25.665171+00:00
-- url     : https://prove2.me/theorems/c1698ec0-49be-4c88-b8d6-66787f3f3f8d
-- title:
--   Courtade–Kumar proof module `CKLaneA1.JnConvex` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.JnConvex` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.JnConvex` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.JnConvex (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/JnConvex.lean)

import Mathlib.Analysis.Convex.Deriv
import Definitions.Def_CK_GeneralCK_CorrectionHessianNatural

/-!
(Lane A1 copy of `~/agy_local_lean/fixededge/GeneralCK/JnConvex.lean`, re-namespaced to
`CKLaneA1` because the F-C provider root does not contain `GeneralCK.JnConvex`.)

# `jn` is convex on `(0, 1/2]`, and the two-corner bracket for its divided difference

`2fa0a23e` asked for this at 10:52Z, after diagnosing that

    j = (jn w − jn u) / (w − u)

computed as an interval **quotient** is up to `4.6×` wider than the true range of `j`
over the box:

```
u=0.02 w=0.05   quotient  j ∈ [−33.9133, −29.4118]  width 4.5015
                direct    j ∈ [−32.0812, −31.0941]  width 0.9870
```

and that this, not the algebraic form and not the `R` bracket, accounts for the `4×`
disagreement between the lanes' cover sizings.  On the target itself it is worth
`3.96×` at the governing point `(0.02, 0.05)`.

## Why convexity is the right tool, with the alternatives priced

`jn` is convex here, so its divided difference is monotone **in each argument
separately**, so its range over a box `[u₁,u₂] × [w₁,w₂]` is attained at two corners:

    j ∈ [ j(u₁,w₁),  j(u₂,w₂) ]

and that is exactly the "direct" column above.

Two cheaper-looking routes are closed, both with measurements:

* **Mean value theorem**, `j = jn' ξ` for some `ξ`, giving `j ∈ [jn' u₁, jn' w₂]`.
  This needs no convexity API at all and is the obvious first reach.  `2fa0a23e`
  measured it: width `31.2` at `(0.02, 0.05)` against `0.987` for the two-corner
  form — **32× worse than the two-corner bracket and 7× worse than the interval
  quotient it would replace.**  It makes things worse.
* **Decomposition.**  `jn x = log(1−x) − log x` is convex-plus-concave: `−log x` is
  convex, `log(1−x)` is concave.  The sum is convex on `(0,1/2)` only because the
  convex part dominates, so it must go through the second derivative.

## The domain restriction is load-bearing

```
jn x   = log(1−x) − log x
jn' x  = −1/(1−x) − 1/x = −1/(x(1−x))
jn'' x = (1−2x)/(x(1−x))²
```
`jn''` is positive exactly when `x < 1/2`.  `jn` is antisymmetric about `1/2` and is
**concave** on `(1/2, 1)`.  Stating this on `Ioc 0 (1/2)` is not tidiness — the
statement is false on any domain reaching past `1/2`.  The closed right endpoint is
kept because `jn'' (1/2) = 0 ≥ 0`, and because `2fa0a23e` has certified the cover's
cells at `w = 1/2` exactly.
-/

namespace CKLaneA1

open GeneralCK.Correction.Natural

open Set

set_option autoImplicit false

/-- `jn` has the expected derivative on `(0,1)`. -/
theorem hasDerivAt_jn {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    HasDerivAt jn (-1/(x*(1-x))) x := by
  have hx : x ≠ 0 := ne_of_gt h0
  have h1x : (1:ℝ) - x ≠ 0 := ne_of_gt (by linarith)
  have hd1 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1/(1-x)) x := by
    have h := (((hasDerivAt_id x).const_sub (1:ℝ)).log h1x)
    simpa using h
  have hd2 : HasDerivAt Real.log (1/x) x := by
    simpa using Real.hasDerivAt_log hx
  have heq : jn =ᶠ[nhds x] (fun t => Real.log (1 - t) - Real.log t) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with t ht
    rw [jn, Real.log_div (ne_of_gt (by linarith [ht.2] : (0:ℝ) < 1 - t)) (ne_of_gt ht.1)]
  have hsum : HasDerivAt jn (-1/(1-x) - 1/x) x := (hd1.sub hd2).congr_of_eventuallyEq heq
  have hval : -1/(1-x) - 1/x = -1/(x*(1-x)) := by
    field_simp
    try ring
  rw [← hval]
  exact hsum

/-- The derivative of `jn`, as a named function, so it can be handed to
`convexOn_of_hasDerivWithinAt2_nonneg` without `deriv^[2]` plumbing. -/
noncomputable def jnD (x : ℝ) : ℝ := -1/(x*(1-x))

/-- The second derivative of `jn`, likewise. -/
noncomputable def jnDD (x : ℝ) : ℝ := (1-2*x)/(x*(1-x))^2

theorem hasDerivAt_mul_one_sub {x : ℝ} : HasDerivAt (fun t : ℝ => t*(1-t)) (1-2*x) x := by
  have h1 : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using h1.const_sub (1:ℝ)
  have h := h1.mul h2
  have hv : (1:ℝ) * (1 - x) + x * (-1) = 1 - 2*x := by ring
  rw [hv] at h
  exact h

theorem hasDerivAt_jnD {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    HasDerivAt jnD (jnDD x) x := by
  have hne : x*(1-x) ≠ 0 := ne_of_gt (mul_pos h0 (by linarith))
  have hd : HasDerivAt (fun t : ℝ => (-1:ℝ)/(t*(1-t)))
      ((0 * (x*(1-x)) - (-1:ℝ) * (1-2*x))/(x*(1-x))^2) x :=
    (hasDerivAt_const x (-1:ℝ)).div hasDerivAt_mul_one_sub hne
  have hval : (0 * (x*(1-x)) - (-1:ℝ) * (1-2*x))/(x*(1-x))^2 = jnDD x := by
    unfold jnDD
    ring
  rw [← hval]
  exact hd

theorem continuousOn_jn : ContinuousOn jn (Ioc (0:ℝ) (1/2)) := by
  intro x hx
  exact (hasDerivAt_jn hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt

/-- 🔴 **`jn` is convex on `(0, 1/2]`.**  False past `1/2`; see the module docstring. -/
theorem jn_convexOn : ConvexOn ℝ (Ioc (0:ℝ) (1/2)) jn := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc _ _) continuousOn_jn
    (f' := jnD) (f'' := jnDD) ?_ ?_ ?_
  · intro x hx
    rw [interior_Ioc] at hx
    exact (hasDerivAt_jn hx.1 (by linarith [hx.2])).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact (hasDerivAt_jnD hx.1 (by linarith [hx.2])).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    have hp : 0 < x*(1-x) := mul_pos hx.1 (by linarith [hx.2])
    unfold jnDD
    exact div_nonneg (by linarith [hx.2]) (by positivity)

/-- A divided difference does not care which way round its two points are written. -/
theorem slope_symm (f : ℝ → ℝ) (x y : ℝ) :
    (f y - f x)/(y - x) = (f x - f y)/(x - y) := by
  rw [← neg_sub (f y) (f x), ← neg_sub y x, neg_div_neg_eq]

/-- 🔴 **The two-corner bracket.**  For a box `[u₁,u₂] × [w₁,w₂]` lying to the left of
`1/2` and with the `u`-interval strictly below the `w`-interval, the divided
difference `j = (jn w − jn u)/(w − u)` attains its extremes at the two corners.

This is `2fa0a23e`'s "direct" evaluation, and it replaces an interval quotient that
was up to `4.6×` too wide. -/
theorem jn_divided_difference_bracket
    {u₁ u u₂ w₁ w w₂ : ℝ}
    (h0 : 0 < u₁) (h1 : u₁ ≤ u) (h2 : u ≤ u₂) (h3 : u₂ < w₁)
    (h4 : w₁ ≤ w) (h5 : w ≤ w₂) (h6 : w₂ ≤ 1/2) :
    (jn w₁ - jn u₁)/(w₁ - u₁) ≤ (jn w - jn u)/(w - u)
      ∧ (jn w - jn u)/(w - u) ≤ (jn w₂ - jn u₂)/(w₂ - u₂) := by
  have hu₁ : u₁ ∈ Ioc (0:ℝ) (1/2) := ⟨h0, by linarith⟩
  have hu : u ∈ Ioc (0:ℝ) (1/2) := ⟨by linarith, by linarith⟩
  have hu₂ : u₂ ∈ Ioc (0:ℝ) (1/2) := ⟨by linarith, by linarith⟩
  have hw₁ : w₁ ∈ Ioc (0:ℝ) (1/2) := ⟨by linarith, by linarith⟩
  have hw : w ∈ Ioc (0:ℝ) (1/2) := ⟨by linarith, by linarith⟩
  have hw₂ : w₂ ∈ Ioc (0:ℝ) (1/2) := ⟨by linarith, by linarith⟩
  -- every `u` point is strictly below every `w` point, via `u₂ < w₁`
  have nw₁u₁ : w₁ ≠ u₁ := ne_of_gt (by linarith)
  have nwu₁ : w ≠ u₁ := ne_of_gt (by linarith)
  have nwu : w ≠ u := ne_of_gt (by linarith)
  have nw₂u : w₂ ≠ u := ne_of_gt (by linarith)
  have nw₂u₂ : w₂ ≠ u₂ := ne_of_gt (by linarith)
  have nu₁w : u₁ ≠ w := ne_of_lt (by linarith)
  have nuw : u ≠ w := ne_of_lt (by linarith)
  have nuw₂ : u ≠ w₂ := ne_of_lt (by linarith)
  have nu₂w₂ : u₂ ≠ w₂ := ne_of_lt (by linarith)
  constructor
  · -- j(u₁,w₁) ≤ j(u₁,w) ≤ j(u,w)
    have step1 : (jn w₁ - jn u₁)/(w₁ - u₁) ≤ (jn w - jn u₁)/(w - u₁) :=
      jn_convexOn.secant_mono hu₁ hw₁ hw nw₁u₁ nwu₁ h4
    have step2 : (jn u₁ - jn w)/(u₁ - w) ≤ (jn u - jn w)/(u - w) :=
      jn_convexOn.secant_mono hw hu₁ hu nu₁w nuw h1
    rw [slope_symm jn w u₁, slope_symm jn w u] at step2
    linarith
  · -- j(u,w) ≤ j(u,w₂) ≤ j(u₂,w₂)
    have step1 : (jn w - jn u)/(w - u) ≤ (jn w₂ - jn u)/(w₂ - u) :=
      jn_convexOn.secant_mono hu hw hw₂ nwu nw₂u h5
    have step2 : (jn u - jn w₂)/(u - w₂) ≤ (jn u₂ - jn w₂)/(u₂ - w₂) :=
      jn_convexOn.secant_mono hw₂ hu hu₂ nuw₂ nu₂w₂ h2
    rw [slope_symm jn w₂ u, slope_symm jn w₂ u₂] at step2
    linarith

#check @jn_convexOn
#check @jn_divided_difference_bracket
#print axioms hasDerivAt_jn
#print axioms hasDerivAt_jnD
#print axioms jn_convexOn
#print axioms jn_divided_difference_bracket

end CKLaneA1


