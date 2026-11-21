-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient_F000
-- name    : LevyStochCalc_Ito_PicardSpaceBieleckiQuotient_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:27:04.549188+00:00
-- url     : https://prove2.me/theorems/00ec7084-4e2a-4942-b049-e37c419fc7c7
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardSpaceBieleckiQuotient
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardSpaceBieleckiQuotient. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSpaceBieleckiEDist_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Bielecki pseudo-emetric space and its separation quotient

The type synonym `SBoundedProcess.WithBielecki` carries the Bielecki β-weighted pseudo-edist,
keeping it apart from the discrete metric on `SBoundedProcess` itself. Its triangle inequality
comes from subadditivity of the Bielecki norm applied to the pointwise identity
`X - Z = (X - Y) + (Y - Z)`, whose measurability side conditions follow from slice
measurability of the inner integrand `ω ↦ (∑ i, ‖X t ω i‖₊²)^(1/2)`. The resulting
`PseudoEMetricSpace` has a separation quotient `SBoundedProcess.AEQuot`, an `EMetricSpace`
identifying processes that agree P-a.s. at each fixed `t`; the constant-zero process inhabits
both the synonym and the quotient. A closing note contrasts this weighted sup-of-`L²` norm
with the `S²` norm and records the role of the `IsRegular` hypothesis in well-posedness.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### Type-synonym carrying the Bielecki pseudo-edist instance

To avoid clashing with the existing discrete `MetricSpace` instance in
`LevyStochCalc.Ito.PicardSpaceDiscrete`, we equip a **type synonym** with the Bielecki
pseudo-edist instance. Downstream callers wanting the literature metric
write `SBoundedProcess.WithBielecki n P ℱ T β` explicitly. -/

/-- **Type synonym for `SBoundedProcess` carrying the Bielecki β-weighted
pseudo-edist instance.** Two `SBoundedProcess`es that agree P-a.s. at
every `t` have Bielecki pseudo-distance zero; this synonym carries the
pseudo-metric, and `SBoundedProcess.AEQuot` (the `SeparationQuotient`)
carries the genuine metric.

The phantom `β` allows different Bielecki β-values to define distinct
typeclass instances on the same underlying type. The `β` parameter is
intentionally unused in the type definition (it only affects the
distinct `EDist` instance that downstream registers on it). -/
def SBoundedProcess.WithBielecki (n : ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (T β : ℝ) : Type _ :=
  let _ := β  -- silence "unused variable β" — phantom parameter
  SBoundedProcess (n := n) P ℱ T
namespace SBoundedProcess.WithBielecki

variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ}

/-- **Constructor.** Wrap a `SBoundedProcess` as the Bielecki-flavored type. -/
def of (X : SBoundedProcess (n := n) P ℱ T) :
    SBoundedProcess.WithBielecki (n := n) P ℱ T β := X
/-- **Underlying `SBoundedProcess` extractor.** -/
def get (X : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    SBoundedProcess (n := n) P ℱ T := X
@[simp] lemma get_of (X : SBoundedProcess (n := n) P ℱ T) :
    SBoundedProcess.WithBielecki.get (SBoundedProcess.WithBielecki.of (n := n) (β := β) X) = X
    := rfl
@[simp] lemma of_get (X : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    SBoundedProcess.WithBielecki.of (n := n) (β := β)
      (SBoundedProcess.WithBielecki.get X) = X := rfl
end SBoundedProcess.WithBielecki

/-! ### EDist + PseudoEMetricSpace instances on `WithBielecki`

The instance is on `WithBielecki`, not on `SBoundedProcess` directly,
so the existing discrete-metric instance in `LevyStochCalc.Ito.PicardSpaceDiscrete` is
preserved. -/

noncomputable instance instEDistWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    EDist (SBoundedProcess.WithBielecki (n := n) P ℱ T β) where
  edist X Y := bieleckiEDist β T
    (SBoundedProcess.WithBielecki.get X)
    (SBoundedProcess.WithBielecki.get Y)
@[simp] lemma edist_WithBielecki_def
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ}
    (X Y : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    edist X Y = bieleckiEDist β T
      (SBoundedProcess.WithBielecki.get X) (SBoundedProcess.WithBielecki.get Y) := rfl
/-! ### Measurability of the inner Bielecki integrand

The `PseudoEMetricSpace` instance on `SBoundedProcess.WithBielecki n P ℱ T β` needs the three
edist axioms: `bieleckiEDist_self` and `bieleckiEDist_comm`, and the triangle inequality, which
applies `bieleckiNorm_add_le` to `Y₁ = X - Y`, `Y₂ = Y - Z` and identifies
`(X - Y) + (Y - Z) = X - Z` pointwise. `bieleckiNorm_add_le` asks for the per-`t`
a.e.-measurability of `ω ↦ (∑ i, ‖X.X t ω i‖₊²)^(1/2)`, which
`bieleckiNorm_inner_aemeasurable` derives from the joint measurability
`LevyStochCalc.Ito.Picard.SBoundedProcess.measurable_path` of the path map. -/

/-! ### Triangle inequality for `bieleckiEDist`

For `SBoundedProcess`es `X, Y, Z`, the pointwise identity `(X - Z) =
(X - Y) + (Y - Z)` on the underlying path maps combines with
`bieleckiNorm_add_le` to give

  `bieleckiEDist β T X Z ≤ bieleckiEDist β T X Y + bieleckiEDist β T Y Z`.

The AEMeasurability hypotheses for `bieleckiNorm_add_le` are discharged
via `bieleckiNorm_inner_aemeasurable` applied to `X.X - Y.X` and
`Y.X - Z.X`, using `LevyStochCalc.Ito.Picard.SBoundedProcess.measurable_path`. -/

/-! ### PseudoEMetricSpace + EMetricSpace instances on `WithBielecki`

With `bieleckiEDist_self`, `bieleckiEDist_comm`, `bieleckiEDist_triangle`
proven, we can register the `PseudoEMetricSpace` instance on
`SBoundedProcess.WithBielecki`. Mathlib's `PseudoEMetricSpace.mk`
constructor takes the three edist axioms plus a default
`UniformSpace` (we use the canonical one generated from the edist). -/

/-! ### AE-quotient: `SBoundedProcess.AEQuot β T`

The `SeparationQuotient` of the pseudo-emetric space `WithBielecki` is
automatically a `EMetricSpace` (separated) in Mathlib. This is the
**literature Banach space** `S²([0, T]; ℝⁿ)` modulo P-null sets, with
the Bielecki β-norm metric. -/

/-! ### The `IsRegular` hypothesis and the `S²` norm

**The `IsRegular` hypothesis.** `JumpDiffusionCoeffs.IsLipschitz coeffs ν L`
alone does not yield a `JumpDiffusion W N coeffs x₀`, so the well-posedness
theorem `exists_jumpDiffusion_unique_of_solvesOn` (`Ito/PicardWellPosed.lean`)
also takes `JumpDiffusionCoeffs.IsRegular coeffs ν`.
`LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz` constrains
the coefficients only in the state variable `x`; it says nothing about their
dependence on `s`, or, for `γ`, on `e`. The field
`LevyStochCalc.Ito.Setting.JumpDiffusion.is_solution` existentially bundles joint
measurability, progressive measurability and the `L²` bounds of
`(s, ω) ↦ σ(s, X_s ω)` and `(ω, s, e) ↦ γ(s, X_s ω, e)`, because the two
stochastic integrals need them to be well-typed. Two coefficient families satisfy
`LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz` with `L = 0` and admit no
`LevyStochCalc.Ito.Setting.JumpDiffusion` at all:

* `n = d = 1`, `μ = 0`, `γ = 0`, `σ s x = 1 / s`. Every Lipschitz clause
  reads `0 ≤ 0`, but `∫⁻ s in Icc 0 T', ‖1 / s‖₊ ^ 2 = ∞` for every
  `T' > 0`, so `h_σ_sq` fails for every path map `X`.
* `n = d = 1`, `μ = 0`, `γ = 0`, `σ s x = 1_A s` for a non-measurable
  `A ⊆ ℝ`. Again every Lipschitz clause reads `0 ≤ 0`, but
  `Function.uncurry (fun ω s => σ s (X s ω))` has `Set.univ ×ˢ A` as a
  preimage, and the `ω`-sections of that set are `A`, so `h_σ_meas`
  fails for every `X`.

`LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular` supplies (i) joint measurability of
`(s, x) ↦ μ s x`, `(s, x) ↦ σ s x` and `(s, x, e) ↦ γ s x e`, and (ii) square integrability
in `s` at a single state, `∫⁻ s in Icc 0 T', ‖σ s 0‖₊ ^ 2 < ∞` and
`∫⁻ s in Icc 0 T', ∫⁻ e, ‖γ s 0 e‖₊ ^ 2 ∂ν < ∞` (and the same for `μ`).
Together with the Lipschitz clauses these give the `L²` bounds along any
`L²`-bounded path, since Lipschitz continuity in the state gives
`‖f s x‖ ≤ ‖f s 0‖ + L ‖x‖` (`Ito/PicardIntegrand.lean`). Applebaum 6.2.9
assumes measurable coefficients of linear growth.

**Not the `S²` space.** `bieleckiNorm β T X` is
`⨆ t ∈ [0, T], exp (-β * t) * ‖X t‖_{L²}`, the weighted *sup-of-`L²`*
norm. It is not the `S²` norm `‖ ⨆ t ≤ T, ‖X t‖ ‖_{L²}`, which is what
`LevyStochCalc.Ito.Setting.JumpDiffusion.sup_L2` asks for, and the separation quotient
`SBoundedProcess.AEQuot` therefore identifies processes that agree a.e.
*at each fixed `t`*, not processes with a.e. equal paths. The
well-posedness chain bridges the two in `Ito/PicardSupL2.lean`, by Doob's
`L²` inequality over the dyadic points for the stochastic components of
the Picard step.

**Where the chain lives.** The metric structure of this file —
`bieleckiEDist` with `bieleckiEDist_comm` and `bieleckiEDist_triangle`, the
`PseudoEMetricSpace` on `SBoundedProcess.WithBielecki`, the separation
quotient `SBoundedProcess.AEQuot` with its `EMetricSpace`, and
nonemptiness of both — is not what the well-posedness proof iterates on.
That proof works with the pseudo-edist on path maps directly: the Picard
step becomes a total self-map of the process space (`picardSelfMap`;
`Ito/PicardIntegrand.lean`, `Ito/PicardOutput.lean`), it is a Bielecki
contraction (`bieleckiNorm_picardSelfMap_diff_le`,
`Ito/PicardContraction.lean`), its iterates `picardIter` converge to
`picardLimit` (built on `bieleckiLimit`, `Ito/PicardLimit.lean`), the
process built on the limit is a fixed point
(`picardSelfMapRaw_isFixedPoint`), the fixed point solves the equation on
the window and is the only solution there (`exists_solvesOn`,
`ae_eq_of_solvesOn`, `Ito/PicardWindow.lean`), and the windows glue
(`exists_globalSolution`, `Ito/PicardGlobal.lean`). -/

end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Nonemptiness of `WithBielecki β T` and `AEQuot β T`

The constant-zero process `constantZeroProcess` (from
`LevyStochCalc.Ito.PicardSpaceDiscrete`) witnesses inhabitedness of the underlying type, hence
of the type synonym and the AE-quotient. -/

/-! ### The well-posedness theorem

The existence and uniqueness statement for the jump-diffusion SDE is
`LevyStochCalc.Ito.Picard.exists_jumpDiffusion_unique_of_solvesOn` in `Ito/PicardWellPosed.lean`,
at the end of the Picard chain that starts here with the Bielecki metric on the process space. -/

end LevyStochCalc.Ito.Picard


