-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0163
-- name    : PNT_ZeroFree_433_0163
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T11:59:14.1597+00:00
-- url     : https://prove2.me/theorems/4fa79f99-4405-4b50-9f4d-28a52d356192
-- title:
--   Zero-free region foundations: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2, RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Tra [0163]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2
--   - RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1
--   - RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimateL2.lean#L43-L349
--   https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimateH1.lean#L36-L111
--   https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/MeasureTheory/Function/LpSpace/Restrict.lean#L45-L214

import Definitions.Def_PNT_ZeroFree_433_0162
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.OrderClosed

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimateL2.lean#L43-L349
https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimateH1.lean#L36-L111
https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/MeasureTheory/Function/LpSpace/Restrict.lean#L45-L214
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2
section
/- Original source header, including license and authors:
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimate
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-/
/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2`

`L²` translation estimates for Euclidean `C¹_c` functions (and derived `H¹`) under invariant
measures.

This file lifts the pointwise fundamental-theorem-of-calculus bound from
`Euclidean.TranslationEstimate` to an `L²` bound using Tonelli and the measure-preserving property
of translations.

## Main results

- `enorm_translateL2_sub_toL2_le`: for `f ∈ C¹_c`, `‖τ_a f - f‖₂ ≤ ‖a‖ · ‖∇f‖₂` (as an `ℝ≥0∞`
  inequality on `L²` norms), under a right-invariant measure.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2 :
    MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimateL2 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimateL2 :
    OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddE_SobolevEuclideanTranslationEstimateL2 : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

private abbrev μI : Measure ℝ := (volume.restrict (Icc (0 : ℝ) 1))

private lemma μI_univ : (μI : Measure ℝ) Set.univ = (1 : ℝ≥0∞) := by
  simp [μI, Measure.restrict_apply, Real.volume_Icc]

private lemma holderConj_two_two : (2 : ℝ).HolderConjugate (2 : ℝ) := by
  refine (Real.holderConjugate_iff).2 ?_
  constructor
  · linarith
  · norm_num

private lemma lintegral_rpow_two_le_lintegral_rpow_two
    {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g (μI : Measure ℝ)) :
    (∫⁻ t, g t ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤ ∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
  -- Hölder with `g * 1` gives `∫ g ≤ (∫ g^2)^(1/2) * (∫ 1^2)^(1/2)`.
  have hHolder :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [Pi.mul_apply] using!
      (ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := (μI : Measure ℝ)) holderConj_two_two
        hg (aemeasurable_const : AEMeasurable (fun _t : ℝ => (1 : ℝ≥0∞)) (μI : Measure ℝ)))
  have h1 : (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) = (1 : ℝ≥0∞) := by
    -- `μI` has total mass `1`, and `1^2 = 1`.
    simp
  have h :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [h1, mul_one] using! hHolder
  -- Raise to the power `2` and simplify `((A)^(1/2))^2 = A`.
  have h' :=
    ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  -- Rewrite the RHS using `rpow_mul`.
  simpa [ENNReal.rpow_mul] using! (h'.trans_eq (by
    have : (1 / (2 : ℝ)) * (2 : ℝ) = (1 : ℝ) := by norm_num
    simpa [this] using!
      (ENNReal.rpow_mul
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ))
        (1 / (2 : ℝ)) (2 : ℝ)).symm))

/-- `L²` translation estimate for `C¹_c` functions under a right-invariant measure. -/
lemma enorm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ₑ ≤
      ‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ := by
  classical
  -- Reduce to an `eLpNorm` inequality on representatives.
  have hL2 :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
          toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => (f.1 (x + a) - f.1 x)) (2 : ℝ≥0∞) μ := by
    -- Both terms agree a.e. with the underlying pointwise translation.
    have h₁ :
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) := by
      have hf :
          (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
        (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
      have hf' :
          (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
        simpa [Function.comp, Pi.add_apply] using!
          (Measure.QuasiMeasurePreserving.ae_eq_comp
            (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
      exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
    have h₂ : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] fun x => f.1 x :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hsub :
        ((translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
              toL2 (μ := μ) (E := E) f : E →₂[μ] ℝ) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) - f.1 x := by
      filter_upwards [Lp.coeFn_sub
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f))
        (toL2 (μ := μ) (E := E) f), h₁, h₂] with x hxsub hx1 hx2
      simpa [hx1, hx2, Pi.sub_apply] using! hxsub
    -- Convert the `Lp` norm to `eLpNorm` and rewrite using a.e. equality.
    let d : E →₂[μ] ℝ :=
      translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) - toL2 (μ := μ) (E := E) f
    have hd0 : (‖d‖ₑ : ℝ≥0∞) = MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have hd1 :
        MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) (by simpa [d] using! hsub)
    simpa [d] using! hd0.trans hd1
  have hGrad :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    have h₁ :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] fun x => grad (E := E) f.1 x :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have h0 :
        (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
          MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have h1 :
        MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) h₁
    exact h0.trans h1
  -- Prove the `eLpNorm` inequality by squaring, using Tonelli and measure-preserving translation.
  have hCore :
      MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ ≤
        ‖a‖ₑ * MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    -- Expand the definition of `eLpNorm` at exponent `2`.
    have h2_ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
    have h2_netop : (2 : ℝ≥0∞) ≠ ∞ := by simp
    simp_rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      h2_ne0 h2_netop, ENNReal.toReal_ofNat] at *
    -- It suffices to compare the squared integrals.
    have hsq :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
          ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
      -- Pointwise: Cauchy–Schwarz in `t`, then Tonelli in `(x,t)`.
      have hpt :
          ∀ x : E,
            ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
              ‖a‖ₑ ^ (2 : ℝ) *
                ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
        intro x
        have h0 := enorm_sub_le_enorm_mul_lintegral_grad (E := E) (x := x) (a := a) (f := f.1)
          (hf := f.2.1)
        -- Square both sides and apply Cauchy–Schwarz in `t`.
        have h1 :
            ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
              (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
          exact ENNReal.rpow_le_rpow h0 (by norm_num)
        have hcs :
            (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
          refine lintegral_rpow_two_le_lintegral_rpow_two (g := fun t : ℝ =>
            ‖grad (E := E) f.1 (x + t • a)‖ₑ) ?_
          -- measurability from continuity of `grad`.
          have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
          have hline : Continuous fun t : ℝ => x + t • a := by
            fun_prop
          exact (hgrad.comp hline).measurable.enorm.aemeasurable
        -- Combine and rewrite.
        calc
          ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ)
              ≤ (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := h1
          _ = ‖a‖ₑ ^ (2 : ℝ) *
              (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
              simpa [Pi.smul_apply, Pi.add_apply] using!
                (ENNReal.mul_rpow_of_nonneg ‖a‖ₑ
                  (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                    ∂(μI : Measure ℝ))
                  (show (0 : ℝ) ≤ (2 : ℝ) by norm_num))
          _ ≤ ‖a‖ₑ ^ (2 : ℝ) *
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
                ∂(μI : Measure ℝ) := by
              gcongr
          _ = ‖a‖ₑ ^ (2 : ℝ) *
              ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
                ∂(μI : Measure ℝ) := rfl
      -- Integrate over `x` and apply Tonelli to swap integrals.
      let F : E × ℝ → ℝ≥0∞ :=
        fun z => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ ^ (2 : ℝ)
      have hmeas :
          AEMeasurable
            F (μ.prod (μI : Measure ℝ)) := by
        have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
        have hcont : Continuous fun z : E × ℝ => z.1 + z.2 • a := by
          fun_prop
        have hbase : Measurable fun z : E × ℝ => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ := by
          exact (hgrad.comp hcont).measurable.enorm
        have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
          (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
        simpa [F] using! (hpow.comp hbase).aemeasurable
      have hTonelli :
          (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) =
            ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
        -- Tonelli in both orders, via the product measure.
        have hprod :
            (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
              ∫⁻ x, ∫⁻ t, F (x, t) ∂(μI : Measure ℝ) ∂μ :=
          MeasureTheory.lintegral_prod (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
        have hprod_symm :
            (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
              ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) :=
          MeasureTheory.lintegral_prod_symm (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
        calc
          (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ)
              = ∫⁻ z, F z ∂μ.prod (μI : Measure ℝ) := by
                  simpa [F] using! hprod.symm
          _ = ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) := hprod_symm
          _ = ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
                  simp [F]
      -- Now use measure-preserving translation in `x` and evaluate the `t`-integral.
      have hShift :
          (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) =
            ∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ) := by
        refine MeasureTheory.lintegral_congr fun t => ?_
        -- Change of variables `x ↦ x + t•a`.
        have hmeas' : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) := by
          have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
          have hbase : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ := hgrad.measurable.enorm
          have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
            (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
          exact hpow.comp hbase
        simpa [Function.comp, add_assoc] using!
          (MeasureTheory.measurePreserving_add_right μ (t • a)).lintegral_comp (μ := μ) (ν := μ)
            (f := fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ)) hmeas'
      have hEval :
          (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) =
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
        -- `μI` has total mass `1`.
        simp [μI, Measure.restrict_apply, Real.volume_Icc]
      -- Put everything together.
      have hInt :
          (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
            ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
        calc
          (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ)
              ≤ ∫⁻ x, ‖a‖ₑ ^ (2 : ℝ) *
                    ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ := by
                refine MeasureTheory.lintegral_mono ?_
                intro x
                exact hpt x
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) := by
                -- Pull out the constant using `lintegral_const_mul''`.
                have hInner :
                    AEMeasurable
                      (fun x : E =>
                        ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) μ := by
                  -- Measurability of the inner integral follows
                  -- from `hmeas` via
                  -- `AEMeasurable.lintegral_prod_right'`.
                  simpa [F] using! (hmeas.lintegral_prod_right' (μ := μ) (ν := (μI : Measure ℝ)))
                simpa [mul_assoc] using!
                  (MeasureTheory.lintegral_const_mul'' (μ := μ) (r := ‖a‖ₑ ^ (2 : ℝ))
                    (f := fun x : E =>
                      ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) hInner)
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hTonelli
          _ = ‖a‖ₑ ^ (2 : ℝ) *
                (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hShift
          _ = ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
                exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hEval
      exact hInt
    -- Take the `1/2` power on both sides and simplify.
    have hsq' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ) * ∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      exact ENNReal.rpow_le_rpow hsq (by norm_num)
    -- Rewrite the RHS as `‖a‖ * (...)^(1/2)`.
    have hsq'' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      simpa [ENNReal.mul_rpow_of_nonneg, show (0 : ℝ) ≤ (1 / (2 : ℝ)) by nlinarith,
        mul_assoc, mul_left_comm, mul_comm] using hsq'
    have hroot : (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = ‖a‖ₑ := by
      -- `(x^2)^(1/2) = x` in `ℝ≥0∞`, accounting for simp-normalization of `2` and `1/2`.
      have hnat : (‖a‖ₑ ^ (2 : ℕ)) = ‖a‖ₑ ^ (2 : ℝ) := by
        simp
      calc
        (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = (‖a‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
          congrArg (fun r : ℝ≥0∞ => r ^ ((2 : ℝ)⁻¹)) hnat
        _ = ‖a‖ₑ := by
          have := (ENNReal.rpow_mul ‖a‖ₑ (2 : ℝ) ((2 : ℝ)⁻¹)).symm
          have hmul : (2 : ℝ) * ((2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
          simpa [hmul, ENNReal.rpow_one] using! this
    simpa [hroot, mul_assoc, mul_left_comm, mul_comm] using! hsq''
  -- Finish: translate back to the original `L²` norms.
  -- (The final `simp` is safe since we have explicit `eLpNorm` equalities above.)
  simpa [hL2, hGrad] using! hCore

/-- Real-norm form of `enorm_translateL2_sub_toL2_le`. -/
lemma norm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ ≤
      ‖a‖ * ‖toL2Grad (μ := μ) (E := E) f‖ := by
  have h := enorm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hA_ne_top :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    simp [enorm]
  have hGrad_ne_top :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    simp [enorm]
  have hB_ne_top : (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ ∞ := by
    refine ENNReal.mul_ne_top ?_ hGrad_ne_top
    simp [enorm]
  have h' :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ).toReal ≤
        (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ).toReal := by
    exact (ENNReal.toReal_le_toReal hA_ne_top hB_ne_top).2 h
  simpa [ENNReal.toReal_mul, toReal_enorm'] using! h'

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end

-- Source module: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1
section
/- Original source header, including license and authors:
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2
import Mathlib.Topology.Order.OrderClosed

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-/
/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1`

Extend Euclidean `L²` translation estimates from `C¹_c` to the closure-based Euclidean `H¹` space.

## Main results

- `norm_translateL2_sub_h1ToL2_le`: for `u ∈ H¹`, `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`, where `∇u` is the
  `L²(E)` component in our `H¹ ⊆ L² × L²(E)` model.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslationEstimateH1 :
    MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimateH1 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimateH1 :
    OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddE_SobolevEuclideanTranslationEstimateH1 : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

/-- `H¹` translation estimate via closure: `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`. -/
theorem norm_translateL2_sub_h1ToL2_le (a : E) (u : ↥(h1 (μ := μ) (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (h1ToL2 (μ := μ) (E := E) u) -
        h1ToL2 (μ := μ) (E := E) u‖ ≤
      ‖a‖ * ‖h1ToL2Grad (μ := μ) (E := E) u‖ := by
  classical
  -- Work in the ambient space `L² × L²(E)`.
  let V : Type _ := (E →₂[μ] ℝ) × (E →₂[μ] E)
  let S : Set V :=
    {v |
      ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ ≤
        ‖a‖ * ‖v.2‖}
  have hS_closed : IsClosed S := by
    -- Closedness follows from continuity of both sides.
    have hf :
        Continuous fun v : V =>
          ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ := by
      -- `v ↦ v.1` is continuous, translation is continuous,
      -- subtraction is continuous, and norm is continuous.
      have hfst : Continuous fun v : V => v.1 := continuous_fst
      have htr :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 := by
        -- `translateL2` is a continuous linear isometry.
        exact (translateL2 (μ := μ) (F := ℝ) a).toContinuousLinearMap.continuous.comp hfst
      have hsub :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 - v.1 := by
        simpa [sub_eq_add_neg] using! htr.sub hfst
      simpa [Pi.smul_apply, Pi.add_apply] using! (continuous_norm.comp hsub)
    have hg :
        Continuous fun v : V =>
          ‖a‖ * ‖v.2‖ := by
      have hsnd : Continuous fun v : V => v.2 := continuous_snd
      have hnorm : Continuous fun v : V => ‖v.2‖ := continuous_norm.comp hsnd
      simpa [mul_assoc] using! (continuous_const.mul hnorm)
    exact isClosed_le hf hg
  have hRange : (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S := by
    rintro v ⟨f, rfl⟩
    -- Reduce to the `C¹_c` estimate.
    simpa [S, graph, toL2Linear, toL2GradLinear] using!
      norm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hClosure :
      closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S :=
    closure_minimal hRange hS_closed
  have hu :
      (u : V) ∈ closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) := by
    -- `u ∈ H¹` means `u` is in the topological closure of the range of `graph`.
    have hu0 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := by
      have hu0 : (u : V) ∈ h1 (μ := μ) (E := E) := u.2
      dsimp [h1] at hu0
      exact hu0
    have hu1 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := hu0
    rw [Submodule.topologicalClosure_coe] at hu1
    exact hu1
  have huS : (u : V) ∈ S := hClosure hu
  -- Unpack membership in `S` and rewrite in terms of the bundled maps `h1ToL2` and `h1ToL2Grad`.
  simpa [S, V, h1ToL2, h1ToL2Grad] using! huS

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end

-- Source module: RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict
section
/- Original source header, including license and authors:
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-/
/-!
# `RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict`

`L^p` extension-by-zero maps for restricted measures.

Mathlib provides the equivalence

`MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s)`

(`MeasureTheory.memLp_indicator_iff_restrict`). This file packages the corresponding map on `Lp`
spaces:

`Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ`,

given by extension-by-zero (via `Set.indicator`).

## Main definitions

- `MeasureTheory.Lp.extendByZeroₗ`
- `MeasureTheory.Lp.extendByZeroₗᵢ`
-/

namespace MeasureTheory

open scoped ENNReal

namespace Lp

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)

private noncomputable def extendByZeroFun (f : Lp E p (μ.restrict s)) : Lp E p μ :=
  let hf : MemLp (fun x : α => f x) p (μ.restrict s) := Lp.memLp f
  let hfi : MemLp (s.indicator fun x : α => f x) p μ :=
    (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s) (f := fun x : α => f x) hs).2 hf
  hfi.toLp (s.indicator fun x : α => f x)

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
private lemma extendByZeroFun_coe (f : Lp E p (μ.restrict s)) :
    extendByZeroFun (μ := μ) (p := p) (s := s) hs f =ᵐ[μ] s.indicator fun x : α => f x := by
  dsimp [extendByZeroFun]
  exact MemLp.coeFn_toLp _

/-- Extension-by-zero as a linear map `Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ`. -/
noncomputable def extendByZeroₗ : Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ where
  toFun := extendByZeroFun (μ := μ) (p := p) (s := s) hs
  map_add' f g := by
    classical
    -- Prove equality by comparing pointwise representatives.
    refine Lp.ext ?_
    have h_add_restrict :
        (fun x : α => (f + g) x) =ᵐ[μ.restrict s] fun x : α => f x + g x := by
      simpa [Pi.smul_apply, Pi.add_apply] using! (Lp.coeFn_add (μ := μ.restrict s) f g)
    have h_add_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (f + g) x = f x + g x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_add_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (f + g)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs g
      , coeFn_add (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
          (extendByZeroFun (μ := μ) (p := p) (s := s) hs g)
      , h_add_on
      ] with x hfg hf hg hadd hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using! hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = (f + g) x := by simp [Set.indicator_of_mem, hx]
        _ = f x + g x := hsum'
        _ = s.indicator (fun x : α => f x) x + s.indicator (fun x : α => g x) x := by
            simp [Set.indicator_of_mem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            simp [hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
    ·
      have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using! hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            -- both summands are zero off `s`
            simp [Set.indicator_of_notMem, hx, hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
  map_smul' c f := by
    classical
    refine Lp.ext ?_
    have h_smul_restrict :
        (fun x : α => (c • f) x) =ᵐ[μ.restrict s] fun x : α => c • f x := by
      simpa [Pi.smul_apply, Pi.add_apply] using! (Lp.coeFn_smul (μ := μ.restrict s) c f)
    have h_smul_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (c • f) x = c • f x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_smul_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (c • f)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , coeFn_smul c (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
      , h_smul_on
      ] with x hcf hf hsmul hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using! hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = (c • f) x := by simp [Set.indicator_of_mem, hx]
        _ = c • f x := hsum'
        _ = c • s.indicator (fun x : α => f x) x := by simp [Set.indicator_of_mem, hx]
        _ = c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by simp [hf]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := hsmul'
    ·
      have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using! hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
            have hf0 :
                extendByZeroFun (μ := μ) (p := p) (s := s) hs f x = 0 := by
              simpa [Set.indicator_of_notMem, hx] using! hf
            have hcx :
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x = 0 := by
              calc
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x =
                    c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by
                      simpa [Pi.smul_apply] using! hsmul
                _ = 0 := by simp [hf0]
            simpa [Pi.smul_apply, Pi.add_apply] using! hcx.symm

/-- Extension-by-zero as a linear isometry. -/
noncomputable def extendByZeroₗᵢ : Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ where
  toLinearMap := extendByZeroₗ (μ := μ) (p := p) (s := s) hs
  norm_map' f := by
    classical
    -- Unfold into `MemLp.toLp` and reduce to `eLpNorm_indicator_eq_eLpNorm_restrict`.
    have hfi :
        MemLp (s.indicator fun x : α => f x) p μ :=
      (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs).2 (Lp.memLp f)
    -- Norm in the codomain is the `eLpNorm` of the indicator.
    have hnorm_out :
        ‖extendByZeroₗ (μ := μ) (p := p) (s := s) hs f‖ =
          ENNReal.toReal (eLpNorm (s.indicator fun x : α => f x) p μ) := by
      dsimp [extendByZeroₗ, extendByZeroFun]
      simp [norm_toLp (f := s.indicator (fun x : α => f x)) hfi]
    -- Rewrite the `eLpNorm` of the indicator as a restricted `eLpNorm`.
    have hnorm_restrict :
        eLpNorm (s.indicator fun x : α => f x) p μ =
          eLpNorm (fun x : α => f x) p (μ.restrict s) := by
      simpa [Pi.smul_apply, Pi.add_apply] using! (eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs)
    -- Combine with the definition of the `Lp` norm on the restricted space.
    simp [hnorm_out, hnorm_restrict, norm_def]

lemma extendByZeroₗᵢ_ae_eq (f : Lp E p (μ.restrict s)) :
    ((extendByZeroₗᵢ (μ := μ) (p := p) (s := s) hs) f : α → E) =ᵐ[μ]
      s.indicator fun x : α => f x := by
  -- Unfold to the underlying `extendByZeroFun` and use the defining AE equality.
  simpa [extendByZeroₗᵢ, extendByZeroₗ] using!
    (extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f)

lemma extendByZeroₗᵢ_congr (hs₁ hs₂ : MeasurableSet s) :
    extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₁ =
      extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₂ := by
  -- `extendByZeroₗᵢ` is characterized by its pointwise representative.
  refine LinearIsometry.toLinearMap_injective ?_
  refine LinearMap.ext ?_
  intro f
  refine MeasureTheory.Lp.ext (E := E) (p := p) (μ := μ) ?_
  have h₁ :
      ((extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₁) f : α → E) =ᵐ[μ]
        s.indicator fun x : α => f x :=
    extendByZeroₗᵢ_ae_eq (μ := μ) (E := E) (p := p) (s := s) (hs := hs₁) f
  have h₂ :
      ((extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₂) f : α → E) =ᵐ[μ]
        s.indicator fun x : α => f x :=
    extendByZeroₗᵢ_ae_eq (μ := μ) (E := E) (p := p) (s := s) (hs := hs₂) f
  exact h₁.trans h₂.symm

end

end Lp

end MeasureTheory

end


