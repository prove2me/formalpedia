-- Prove2me | Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
-- name    : LeanLevy_Levy_LevyKhintchineUniqueness
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-31T10:23:03.267197+00:00
-- url     : https://prove2.me/theorems/0e1f850a-24d5-4ecd-b805-666dd9588ad7
-- title:
--   LeanLevy source module: Levy.LevyKhintchineUniqueness
-- statement:
--   Pinned source definition and helper bundle. The original generated Lean module passed the earlier local build. This draft awaits Prove2Me remote compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineUniqueness.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

/-!
# Uniqueness of the Lévy–Khintchine triple: the smeared canonical measure

This file begins Part B of the Lévy–Khintchine programme: the triple `(b, σ², ν)` is
determined by the characteristic exponent. The route follows Sato (Theorem 8.1): the
*smeared exponent*
`g(ξ) := ψ(ξ) − ½ ∫_{[-1,1]} ψ(ξ + u) du`
is the characteristic function of a **finite** measure `ρ` on `ℝ`, from which `σ²` is read
off as an atom and `ν` by untilting on `{0}ᶜ`.

## The smeared measure

We construct `ρ = smearedMeasure σ² ν` and prove it is finite and computes its atom at `0`.
Later tasks identify `charFun ρ` with the smeared exponent (giving `ρ` from the exponent alone)
and invert `ρ` back to `(σ², ν)`.

### Pinning the Gaussian coefficient (worked by hand)

The Gaussian piece of the LK exponent is `ψ_G(ξ) = −σ²ξ²/2`. Its smear is
```
g_G(ξ) = ψ_G(ξ) − ½ ∫_{-1}^{1} ψ_G(ξ + u) du
       = −σ²ξ²/2 + (σ²/4) ∫_{-1}^{1} (ξ + u)² du.
```
Since `∫_{-1}^{1} (ξ + u)² du = ∫_{-1}^{1} (ξ² + 2ξu + u²) du = 2ξ² + 0 + 2/3`, we get
```
g_G(ξ) = −σ²ξ²/2 + (σ²/4)(2ξ² + 2/3) = −σ²ξ²/2 + σ²ξ²/2 + σ²/6 = σ²/6.
```
The Gaussian smear is the **constant** `σ²/6`; a constant is the characteristic function of a
point mass at `0`, so `ρ` carries a Dirac atom of weight `σ²/6` (NOT `σ²`). Hence the
recovery formula `σ² = 6 · ρ{0}` (`smearedMeasure_singleton_zero`).

### The jump piece

The smear of the jump piece produces, via the Fourier identity
`½ ∫_{-1}^{1} e^{iux} du = Real.sinc x` (`intervalIntegral_exp_I_symm`), a density
`1 − Real.sinc x` against `ν`. We use the mathlib spelling `Real.sinc x` throughout — for a
Lévy measure `ν` with `ν{0} = 0` this agrees `ν`-a.e. with the classical `1 − sin x / x`, and
`Real.sinc` makes the sinc bounds from `LevyKhintchineProof` (`one_sub_sinc_le_mul_min`,
`mul_min_le_one_sub_sinc`) apply syntactically.

## Main definitions

* `ProbabilityTheory.smearedMeasure` — the finite measure `ρ = (σ²/6)•δ₀ + ν.withDensity(1 − sinc)`.

## Main results

* `ProbabilityTheory.lintegral_one_sub_sinc_lt_top` — the withDensity mass is finite.
* `ProbabilityTheory.smearedMeasure_isFiniteMeasure` — `ρ` is a finite measure.
* `ProbabilityTheory.smearedMeasure_singleton_zero` — `ρ{0} = σ²/6`, so `σ² = 6·ρ{0}`.
-/

open MeasureTheory ENNReal Set
open scoped NNReal ENNReal Real

namespace ProbabilityTheory

variable (σ_sq : ℝ≥0) (ν : Measure ℝ)

/-- The **smeared canonical measure** `ρ` from Sato's uniqueness route. It is the finite
measure whose characteristic function is the smeared Lévy–Khintchine exponent
`g(ξ) = ψ(ξ) − ½ ∫_{[-1,1]} ψ(ξ + u) du`.

Its two pieces are pinned by the smear algebra:
* a Dirac atom at `0` of weight `σ²/6` (the smear of the Gaussian piece `−σ²ξ²/2` is the
  constant `σ²/6`; see the module docstring for the hand computation), and
* a density `1 − Real.sinc x` against the Lévy measure `ν` (the smear of the jump piece).

The `Real.sinc` spelling is chosen deliberately over the classical `1 − sin x / x`: the two
agree `ν`-a.e. when `ν{0} = 0`, and `Real.sinc` matches the sinc bounds proved in
`LevyKhintchineProof`. -/
noncomputable def smearedMeasure : Measure ℝ :=
  ((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)
    + ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))









/-!
## The smear identity

We identify the *smeared exponent* `g(ξ) = ψ_T(ξ) − ½ ∫_{[-1,1]} ψ_T(ξ+u) du` with
`charFun (smearedMeasure σ² ν) ξ`. The drift piece cancels (its `u`-average is symmetric),
the Gaussian piece contributes the constant `σ²/6`, and the jump piece contributes
`∫ e^{ixξ}(1 − sinc x) dν`.
-/

section SmearIdentity

variable {ν : Measure ℝ}

























end SmearIdentity

/-!
## Recovery of the triple from the smeared measure

The smearing is injective: from `ρ = smearedMeasure σ² ν` (with `ν` a Lévy measure) both `σ²`
and `ν` are recovered. The Gaussian coefficient is read off the atom at `0`
(`smearedMeasure_singleton_zero`); the Lévy measure is recovered by restricting to `{0}ᶜ` — which
discards the Dirac atom and leaves the jump density untouched — and untilting the density
`1 − Real.sinc x`, which is strictly positive `ν`-a.e. (`one_sub_sinc_pos`, using `ν{0} = 0`).
-/

section Recovery

variable {ν : Measure ℝ}













end Recovery

/-!
## Uniqueness of the triple

Chaining the smear identity with `Measure.ext_of_charFun` and the smearing inversion pins the
whole triple `(b, σ², ν)` from the exponent alone.
-/

section Uniqueness





end Uniqueness

/-!
## Characterization of infinite divisibility

The three pieces of the Lévy–Khintchine programme compose into the classical characterization:
a probability measure on `ℝ` is infinitely divisible **iff** its characteristic function is
`exp ∘ ψ_T` for some Lévy–Khintchine triple `T`, and that triple is then **unique**.

* forward direction: `levyKhintchine_representation` (needs only infinite divisibility);
* backward direction: `levyKhintchine_converse` + `Measure.ext_of_charFun` (a triple's law is
  pinned by its characteristic function, so it must equal `μ`);
* uniqueness: `LevyKhintchineTriple.ext_of_exponent_eq`, once exponents are identified from
  equal exponentials by the continuous-log argument below.
-/

section Characterization







end Characterization

end ProbabilityTheory


