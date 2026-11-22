-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F000
-- name    : LevyStochCalc_Ito_PicardFixedPoint_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:03:33.630918+00:00
-- url     : https://prove2.me/theorems/c559c62d-bf9c-474d-ae6e-12b2f3f9465c
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardFixedPoint
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardFixedPoint. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardWellPosed_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Existence and uniqueness via the Banach fixed-point theorem

This file packages Banach's fixed-point theorem (`ContractingWith.fixedPoint`)
in the `∃!` shape of a Picard iteration, and states the existence/uniqueness
theorem for the jump-diffusion SDE in the form consumed by `Ito/Setting.lean`,
forwarding to `exists_jumpDiffusion_unique_of_solvesOn` in
`Ito/PicardWellPosed.lean`.

## Contents

* `picardFixedPoint_generic`, `picardFixedPoint`, `picardFixedPoint_of_exists`
  — the abstract fixed-point packaging.
* `picardFixedPoint_jumpDiffusion_exists_unique` — the concrete
  existence/uniqueness statement for the jump-diffusion SDE, relative to a
  filtration satisfying the usual conditions.
* `JumpDiffusion.exists_unique`, `JumpDiffusion.agree_at_zero` — the form
  consumed by `Ito/Setting.lean`.
-/
open MeasureTheory ProbabilityTheory Function
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Banach fixed-point shim (generic form).** For any nonempty complete
metric space `M` and any contraction `Φ : M → M` (i.e. `ContractingWith K Φ`
for some `K < 1`), there is a **unique** fixed point of `Φ`.

This is the direct repackaging of Mathlib's
`ContractingWith.fixedPoint` + `fixedPoint_isFixedPt` + `fixedPoint_unique`
into the `∃!` shape natural for the Picard iteration:

  `∃! X : M, Φ X = X`.

Substantive content sits inside `ContractingWith`: Mathlib proves
existence by showing `(Φ^[n] x)` is a Cauchy sequence (geometric `K^n`
decay) and uses completeness to extract its limit; uniqueness is
immediate from the contraction (two fixed points would have
`d(x, y) ≤ K · d(x, y)` with `K < 1`).

This generic form takes the metric / completeness / nonemptiness as
instance arguments — the SDE specialisation
(`picardFixedPoint`) bundles them on the SBoundedProcess Banach space. -/
theorem picardFixedPoint_generic
    {M : Type*} [MetricSpace M] [Nonempty M] [CompleteSpace M]
    {K : NNReal} {Φ : M → M} (hΦ : ContractingWith K Φ) :
    ∃! X : M, Φ X = X := by
  -- Extract the fixed point from Mathlib's `ContractingWith.fixedPoint`.
  refine ⟨ContractingWith.fixedPoint Φ hΦ, ?_, ?_⟩
  · -- Existence: `fixedPoint_isFixedPt` says `Φ (fixedPoint ...) = fixedPoint ...`.
    exact hΦ.fixedPoint_isFixedPt
  · -- Uniqueness: any fixed point equals `ContractingWith.fixedPoint`.
    intro Y hY
    -- `hY : Φ Y = Y` is `Function.IsFixedPt Φ Y`.
    exact hΦ.fixedPoint_unique hY
/-- **Banach fixed-point shim (SBoundedProcess form).** Specialises
`picardFixedPoint_generic` to the SBoundedProcess setting required by
the jump-diffusion SDE Picard iteration.

**Typeclass-placeholder notice:**
when invoked with the *default* `MetricSpace` / `CompleteSpace` instances
on `SBoundedProcess P T` (the discrete-metric instances installed in
`PicardSpace.lean`), this theorem is **typeclass-trivial**: a contraction
on the discrete metric collapses to the identity on the fixed-point
fibre, completeness is vacuous (Cauchy sequences are eventually
constant), and the unique fixed point is the starting iterate. NO
SUBSTANTIVE MATHEMATICAL CONTENT is carried by the discrete-metric
specialisation — it discharges the typeclass obligation only.

The literature-substantive Banach work (Bielecki β-weighted L²-sup
norm with genuine contraction at the analytical rate
`3 n L² (T+2) / (2β)` for `β > 3 n L² (T+2) / 2`) does not pass through
this shim: the contraction estimate is `bieleckiNorm_picardSelfMap_diff_le`
(`Ito/PicardContraction.lean`), the iterates converge to `picardLimit`
(built on `bieleckiLimit`, `Ito/PicardLimit.lean`), and the SDE chain ends
in `exists_jumpDiffusion_unique_of_solvesOn` (`Ito/PicardWellPosed.lean`).
**Downstream consumers needing the SDE strong-existence result should use
`JumpDiffusion.exists_unique` below or that theorem, not this typeclass-shim
theorem applied on `SBoundedProcess`.**

The hypothesis bundle:

* `[MetricSpace (SBoundedProcess P T)]` — the `S²` / Bielecki metric on
  the càdlàg L²-bounded process space (the discrete-metric instance
  from `PicardSpace.lean` is one canonical choice — but typeclass-
  trivial as above; the Bielecki β-norm on the `AEQuot` quotient from
  `PicardSpace.lean` is the literature choice).
* `[Nonempty (SBoundedProcess P T)]` — witnessed e.g. by the constant
  zero process.
* `[CompleteSpace (SBoundedProcess P T)]` — `S²` is the standard Banach
  space of càdlàg L²-bounded processes; completeness is the usual
  quotient by P-null sets / Lebesgue-null time sets.
* `Φ : SBoundedProcess P T → SBoundedProcess P T` — the Picard map on
  the process space (lifted from `picardStep`, requires the
  measurability / progressive-measurability / L²-finiteness
  hypotheses on `(μ, σ, γ)` along candidate processes).
* `hΦ : ContractingWith K Φ` — the substantive Bielecki β-norm
  contraction estimate (combines `bielecki_weighted_integral_bound`
  with the per-component Lipschitz bounds on drift / diffusion / jump).

Conclusion: **a unique fixed point of `Φ`**. For the actual Picard map the
fixed point is `picardLimit` (`Ito/PicardContraction.lean`), and that it
solves the SDE on the window is `solvesOn_of_isFixedPoint`
(`Ito/PicardWindow.lean`).

This form uses the globally-available instances on `SBoundedProcess`
(from `PicardSpace.lean`: discrete metric + Cauchy-eventually-constant
completeness — typeclass-placeholders only). The Bielecki β-norm is a
genuine metric on the quotient `AEQuot β T` of `PicardSpace.lean`; the
well-posedness proof works with it as a pseudo-edist on path maps
directly. -/
theorem picardFixedPoint
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {n : ℕ}
    (T : ℝ)
    {K : NNReal} {Φ : SBoundedProcess (n := n) P ℱ T → SBoundedProcess (n := n) P ℱ T}
    (hΦ : ContractingWith K Φ) :
    ∃! X : SBoundedProcess (n := n) P ℱ T, Φ X = X :=
  picardFixedPoint_generic hΦ
/-- **Convenience corollary — Picard fixed point in
existential-bundle form.** Same content as `picardFixedPoint`, but
expressed with the contraction packaged as an existential
`∃ (Φ : ...) (K : ℝ≥0) (_hK : K < 1), LipschitzWith K Φ`.

This matches the natural form a downstream caller would obtain from
the (downstream) `picardStep_bielecki_contraction` lemma: that lemma
produces the map `Φ`, the rate `K`, the proof `K < 1`, and the
Lipschitz bound, all bundled together.

The conclusion strips out a witness `Φ` from the existential and
delivers its unique fixed point. -/
theorem picardFixedPoint_of_exists
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {n : ℕ}
    (T : ℝ)
    (h_contraction :
      ∃ (Φ : SBoundedProcess (n := n) P ℱ T → SBoundedProcess (n := n) P ℱ T)
        (K : NNReal) (_hK : K < 1),
          ∀ X Y : SBoundedProcess (n := n) P ℱ T, edist (Φ X) (Φ Y) ≤ K * edist X Y) :
    ∃ (Φ : SBoundedProcess (n := n) P ℱ T → SBoundedProcess (n := n) P ℱ T),
      ∃! X : SBoundedProcess (n := n) P ℱ T, Φ X = X := by
  -- Unpack the contraction existential.
  obtain ⟨Φ, K, hK_lt_one, hΦ_lip⟩ := h_contraction
  -- Build a `ContractingWith K Φ`: the contraction is the conjunction of
  -- `K < 1` (given by `hK_lt_one`) and `LipschitzWith K Φ`. The latter is
  -- definitionally `∀ x y, edist (Φ x) (Φ y) ≤ K * edist x y`, which is
  -- precisely `hΦ_lip`.
  have hΦ : ContractingWith K Φ := ⟨hK_lt_one, hΦ_lip⟩
  exact ⟨Φ, picardFixedPoint_generic hΦ⟩
/-- **Well-posedness of the jump-diffusion SDE, relative to a filtration satisfying the usual
conditions.**

Thin forwarder over `exists_jumpDiffusion_unique_of_solvesOn` in `Ito/PicardWellPosed.lean`,
which builds the solution by Picard iteration on the Bielecki-weighted process space over each
window and glues the windows.

The filtration is a parameter, and both the produced solution
and the competitor are asked to satisfy the integral equation relative to it. The `is_solution`
field of `JumpDiffusion` quantifies the filtration existentially, so two `JumpDiffusion`s can
carry incomparable Brownian filtrations; the `L²` Itô isometry — which is what the Gronwall step
uses — is available only within a single filtration, and a join of two Brownian filtrations need
not be Brownian, so uniqueness across filtrations is outside both the literature scope
(Applebaum 6.2.9 and Ikeda–Watanabe IV fix the filtered space) and the method. The usual
conditions `[ℱ.IsRightContinuous]`, `hℱ0` and `hnull` are the standing hypotheses of that
literature and are used by the construction.

**Reference**: Applebaum 2009 Theorem 6.2.9; Ikeda–Watanabe Chapter IV. -/
theorem picardFixedPoint_jumpDiffusion_exists_unique
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    {L : ℝ}
    (hL : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν) :
    ∃ jd : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀,
      (∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd.X T)
        ∧ ∀ jd' : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀,
            (∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd'.X T) →
              ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω :=
  exists_jumpDiffusion_unique_of_solvesOn W N ℱ hℱW hℱN coeffs x₀ hℱ0 hnull hReg hL
end LevyStochCalc.Ito.Picard

/-! ## Literature theorem: `JumpDiffusion.exists_unique`

This is the headline existence-and-uniqueness theorem cited from
Applebaum 2009 Theorem 6.2.9 / Ikeda-Watanabe IV. Its qualified name is
`LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` — we re-open
that namespace explicitly here so the original location in
`Ito/Setting.lean` (a module that this file imports) is preserved at
the level of qualified names.

**Why the theorem lives here, not in `Ito/Setting.lean`**: the proof
forwards through `picardFixedPoint_jumpDiffusion_exists_unique` (above),
which forwards to `exists_jumpDiffusion_unique_of_solvesOn` in
`Ito/PicardWellPosed.lean`. Putting the theorem in `LevyStochCalc.Ito.Setting`
would require that module to import `LevyStochCalc.Ito.PicardWellPosed`,
which already imports `LevyStochCalc.Ito.Setting` for the `JumpDiffusion`
structure definition, creating a cycle. -/

namespace LevyStochCalc.Ito.Setting
namespace JumpDiffusion

end JumpDiffusion
end LevyStochCalc.Ito.Setting


