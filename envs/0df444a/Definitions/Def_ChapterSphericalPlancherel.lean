-- Prove2me | Definitions.Def_ChapterSphericalPlancherel
-- name    : ChapterSphericalPlancherel
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:10:40.069698+00:00
-- url     : https://prove2.me/theorems/d46de995-0852-4f58-a66d-5f1f24da08f8
-- title:
--   Chapter SphericalPlancherel
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSphericalPlancherel.lean`): generated def bundle for ChapterSphericalPlancherel. See BookProof/ChapterSphericalPlancherel.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSphericalPlancherel.lean

import Definitions.Def_ChapterSphericalBessel
import Mathlib


/-!
# Unitarity of the spherical transform (Fourier–Bessel / Hankel Plancherel, `l = 0`)

`book.tex` §A.5 introduces the *spherical transform*

`(𝓢f)(p) = √(2/π) ∫₀^∞ f(r) jₗ(p r) r² dr`

and uses it as a **unitary** map of `L²((0,∞), r² dr)` onto itself in every
angular-momentum sector.  `BookProof.ChapterBesselHarmonic` and
`BookProof.ChapterNote68AllModes` proved that the transform intertwines `−∂⃗²`
with multiplication by `p²` (Note 68); its *unitarity* was the remaining
recorded boundary.  This module proves it in the `s`-wave sector `l = 0`.

## Strategy

With `j₀(x) = sin x / x` the kernel collapses to a sine kernel: writing
`G(r) = r f(r)`,

`p · (𝓢f)(p) = √(2/π) ∫₀^∞ G(r) sin(p r) dr`,

so the spherical Plancherel theorem is exactly Plancherel for the **Fourier sine
transform** on `(0,∞)`.  That in turn is the Fourier–Plancherel theorem of
Mathlib applied to the *odd extension*: for an odd function `G` the Fourier
transform is `𝓕G(w) = −2i ∫₀^∞ sin(2πwx) G(x) dx`, and both `‖G‖²` and `‖𝓕G‖²`
are even, so the factors of two match up.

## Contents

* `integral_eq_zero_of_odd`, `integral_eq_two_smul_of_even`,
  `integral_eq_two_mul_of_even_real` — the elementary symmetry lemmas;
* `fourier_odd_eq` — the Fourier transform of an odd integrable function is
  `−2i` times its sine transform;
* `sine_plancherel` — **Plancherel for the sine transform** (`2π` convention);
* `sineKernel_plancherel` — the same in the analysts' `sin(pr)` convention:
  `∫₀^∞ |∫₀^∞ G(r) sin(pr) dr|² dp = (π/2) ∫₀^∞ |G(r)|² dr`;
* `spherical_plancherel` — **unitarity of the spherical transform for `l = 0`**:
  `∫₀^∞ |(𝓢f)(p)|² p² dp = ∫₀^∞ |f(r)|² r² dr`, for every radial profile `f`
  whose moment `r ↦ r f(r)` is (the restriction of) an odd Schwartz function.

The class of admissible profiles is a dense subspace of `L²((0,∞), r² dr)`; the
extension of `𝓢` to the whole space by continuity, and the sectors `l ≥ 1`, are
not treated here.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterSphericalPlancherel

open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

/-! ## Elementary symmetry lemmas for integrals on the line -/









/-! ## The sine transform and the Fourier transform of an odd function -/

/-- The Fourier **sine transform** in the `2π` convention used by Mathlib's
Fourier transform. -/
noncomputable def sineTransform (G : ℝ → ℂ) (w : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (Real.sin (2 * π * (x * w)) : ℂ) * G x







/-! ## Plancherel for the sine transform -/



/-- The sine transform in the analysts' convention, with kernel `sin(p r)`. -/
noncomputable def sineKernelTransform (G : ℝ → ℂ) (p : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (Real.sin (p * x) : ℂ) * G x





/-! ## Unitarity of the spherical transform in the `s`-wave sector -/

/-- The **spherical transform** of a radial profile in the sector `l = 0`:
`(𝓢f)(p) = √(2/π) ∫₀^∞ f(r) j₀(p r) r² dr`. -/
noncomputable def sphericalTransform (f : ℝ → ℂ) (p : ℝ) : ℂ :=
  (Real.sqrt (2 / π) : ℂ) * ∫ r in Ioi (0 : ℝ), f r * (sbessel 0 (p * r) : ℂ) * (r : ℂ) ^ 2





/-! ## Non-vacuity: an explicit odd Schwartz function

The hypothesis of `spherical_plancherel` is satisfied by a nonzero function: the
antisymmetrization of a smooth bump supported away from the origin.  So the
theorem really does say something about a nontrivial class of radial profiles.
-/

/-- A smooth bump centred at `2`, equal to `1` on `[1, 3]` and supported in
`(0, 4)`. -/
noncomputable def bumpAtTwo : ContDiffBump (2 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩

/-- Its antisymmetrization: a nonzero odd smooth compactly supported function. -/
noncomputable def oddBump (x : ℝ) : ℂ := (bumpAtTwo x : ℂ) - (bumpAtTwo (-x) : ℂ)





theorem contDiff_oddBump : ContDiff ℝ ∞ oddBump := by
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => (bumpAtTwo x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp bumpAtTwo.contDiff
  have h2 : ContDiff ℝ ∞ (fun x : ℝ => (bumpAtTwo (-x) : ℂ)) := h1.comp contDiff_neg
  exact h1.sub h2

theorem hasCompactSupport_oddBump : HasCompactSupport oddBump := by
  have h1 : HasCompactSupport (fun x : ℝ => (bumpAtTwo x : ℂ)) := by
    apply HasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ))
    · exact bumpAtTwo.hasCompactSupport
    · simp
  have h2 : HasCompactSupport (fun x : ℝ => (bumpAtTwo (-x) : ℂ)) :=
    h1.comp_homeomorph (Homeomorph.neg ℝ)
  exact h1.sub h2

/-- `oddBump` as a Schwartz function. -/
noncomputable def oddSchwartz : 𝓢(ℝ, ℂ) :=
  hasCompactSupport_oddBump.toSchwartzMap contDiff_oddBump









end BookProof.ChapterSphericalPlancherel


