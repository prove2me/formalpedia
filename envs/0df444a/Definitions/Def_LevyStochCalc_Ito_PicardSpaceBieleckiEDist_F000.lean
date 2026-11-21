-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardSpaceBieleckiEDist_F000
-- name    : LevyStochCalc_Ito_PicardSpaceBieleckiEDist_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:19:59.686941+00:00
-- url     : https://prove2.me/theorems/e0f64534-0c49-4441-90eb-a48a49f205f2
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardSpaceBieleckiEDist
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardSpaceBieleckiEDist. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSpaceDiscrete_F000
import Mathlib.Analysis.MeanInequalities

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Bielecki β-weighted pseudo-edist between bounded processes

Pointwise Euclidean Minkowski on `Fin n → ℝ` lifts, through `L²`-Minkowski over `Ω`,
multiplication by the weight `exp (-β * t)` and sup-subadditivity over `t ∈ [0, T]`, to
subadditivity of the Bielecki β-norm `bieleckiNorm β T X = ⨆ t ∈ [0, T], exp (-β * t) *
(E‖X t‖²)^(1/2)`. Evaluating that norm on the pointwise path difference of two
`SBoundedProcess`es gives `bieleckiEDist`, which vanishes on the diagonal and is symmetric;
two processes whose paths agree P-a.s. at every `t` are at Bielecki distance zero, so it is a
pseudo-edist rather than an edist.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### Pointwise Euclidean Minkowski on `Fin n → ℝ`

The Bielecki β-norm has the inner part `(∑ i, ‖X t ω i‖₊²)^(1/2)` which
is the **Euclidean** norm of `X t ω : Fin n → ℝ` (NOT the sup-norm `Pi.norm_def`
of Mathlib's default `Pi.seminormedAddGroup`). The triangle inequality
requires `(∑ i, (a_i + b_i)²)^(1/2) ≤ (∑ i, a_i²)^(1/2) + (∑ i, b_i²)^(1/2)`,
which is `NNReal.Lp_add_le` at `p = 2`. -/

/-- **Pointwise Euclidean Minkowski (ENNReal form).** For NNReal-valued
`a, b : Fin n → NNReal`,
  `(∑ i, ((a i + b i) : ℝ≥0∞)²)^(1/2) ≤ (∑ i, a i²)^(1/2) + (∑ i, b i²)^(1/2)`.

This is the cast-to-`ℝ≥0∞` version of `NNReal.Lp_add_le` at `p = 2`. -/
lemma sum_sq_nnreal_add_le (n : ℕ) (a b : Fin n → NNReal) :
    (∑ i, ((a i + b i : NNReal) : ℝ≥0∞) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (∑ i, ((a i : NNReal) : ℝ≥0∞) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        + (∑ i, ((b i : NNReal) : ℝ≥0∞) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
  ENNReal.Lp_add_le Finset.univ
    (fun i => ((a i : NNReal) : ℝ≥0∞)) (fun i => ((b i : NNReal) : ℝ≥0∞))
    (by norm_num : (1:ℝ) ≤ 2)
/-! ### Bielecki edist between `SBoundedProcess`es

Defined as `bieleckiNorm β T (X.X - Y.X)`. The path map difference is
just pointwise subtraction. -/

/-- **Pointwise difference of path maps.** Subtraction of two
`SBoundedProcess`'s underlying path maps is pointwise subtraction in
`Fin n → ℝ` at each `(t, ω)`. -/
@[simp] noncomputable def SBoundedProcess.pathDiff
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X Y : SBoundedProcess (n := n) P ℱ T) : ℝ → Ω → (Fin n → ℝ) :=
  fun t ω => X.X t ω - Y.X t ω
/-- **The Bielecki β-weighted edist between two `SBoundedProcess`es.**

  `bieleckiEDist β T X Y := bieleckiNorm β T (X.X - Y.X)`,

i.e., `⨆_{t ∈ [0, T]} e^{-βt} · (E[‖X_t - Y_t‖²])^(1/2)`.

This is a **pseudo-edist** on `SBoundedProcess`: two structures with
P-a.s. equal paths at every `t` have `bieleckiEDist = 0` but are not
structurally equal as `SBoundedProcess`es. The genuine `MetricSpace` is
on the AE-quotient (`SBoundedProcess.AEQuot`); this pseudo-edist
descends to a genuine edist on the quotient. -/
noncomputable def bieleckiEDist
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (β T : ℝ) (X Y : SBoundedProcess (n := n) P ℱ T) : ℝ≥0∞ :=
  bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff X Y)
/-! ### Pseudo-edist axioms for `bieleckiEDist` -/

@[simp] lemma bieleckiEDist_self
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {β T : ℝ}
    (X : SBoundedProcess (n := n) P ℱ T) : bieleckiEDist β T X X = 0 := by
  unfold bieleckiEDist bieleckiNorm SBoundedProcess.pathDiff
  -- The path-difference is identically zero, so the L² norm is zero.
  refine le_antisymm ?_ bot_le
  refine iSup_le (fun t => ?_)
  refine iSup_le (fun _ => ?_)
  -- The integrand is pointwise zero (`X.X t ω - X.X t ω = 0`), so the
  -- lintegral is zero, hence the (1/2)-rpow is zero, multiplying gives zero.
  have h_integrand_zero :
      (fun ω : Ω => ∑ i, ((‖(X.X t ω - X.X t ω) i‖₊ : ℝ≥0∞)) ^ 2)
        = fun _ => 0 := by
    funext ω
    simp
  rw [h_integrand_zero]
  simp
lemma bieleckiEDist_comm
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {β T : ℝ}
    (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiEDist β T X Y = bieleckiEDist β T Y X := by
  -- It suffices to show, per-`(t, ω, i)`, that the inner summands agree.
  -- ‖X t ω i - Y t ω i‖₊ = ‖-(Y t ω i - X t ω i)‖₊ = ‖Y t ω i - X t ω i‖₊
  -- (by `nnnorm_neg`).
  unfold bieleckiEDist bieleckiNorm SBoundedProcess.pathDiff
  -- The integrand pointwise equality:
  have h_pw : ∀ t : ℝ, ∀ ω : Ω,
      ∑ i, (‖(X.X t ω - Y.X t ω) i‖₊ : ℝ≥0∞) ^ 2
        = ∑ i, (‖(Y.X t ω - X.X t ω) i‖₊ : ℝ≥0∞) ^ 2 := by
    intro t ω
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 2
    rw [show (X.X t ω - Y.X t ω) i = -((Y.X t ω - X.X t ω) i) by
      simp [Pi.sub_apply]]
    exact nnnorm_neg _
  -- Lift to lintegral, then to (1/2)-rpow, then to multiplication, then to sup.
  refine iSup_congr (fun t => ?_)
  refine iSup_congr (fun _ => ?_)
  congr 1
  congr 1
  exact lintegral_congr_ae (Filter.Eventually.of_forall (fun ω => h_pw t ω))
/-! ### Bielecki triangle inequality

The key analytic content: `bieleckiNorm β T ((X - Y) + (Y - Z)) ≤
bieleckiNorm β T (X - Y) + bieleckiNorm β T (Y - Z)`.

This decomposes as:
1. Pointwise (in `t, ω`) Euclidean Minkowski (`sum_sq_nnreal_add_le`).
2. L² Minkowski over `ω` (`ENNReal.lintegral_Lp_add_le`).
3. Multiplication by `ENNReal.ofReal (Real.exp (-β·t))` preserves the
   inequality (left-multiplication by a non-negative constant in ℝ≥0∞).
4. Sup-subadditivity (`iSup₂_add_le`).
-/

end LevyStochCalc.Ito.Picard


