-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0166
-- name    : PNT_ZeroFree_433_0166
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:03:34.227297+00:00
-- url     : https://prove2.me/theorems/52e4484d-c6f9-4ff0-8689-9b4aa87e60af
-- title:
--   Zero-free region foundations: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Transfer, RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2 [0166]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Transfer
--   - RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.FrechetKolmogorov
--   - RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Kernels
--   - RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.TranslationIntegral
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Transfer.lean#L42-L346
--   https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/FrechetKolmogorov.lean#L55-L181
--   https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Kernels.lean#L44-L101
--   https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/TranslationIntegral.lean#L41-L132

import Definitions.Def_PNT_ZeroFree_433_0162
import Definitions.Def_PNT_ZeroFree_433_0164
import Definitions.Def_PNT_ZeroFree_433_0165
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Transfer.lean#L42-L346
https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/FrechetKolmogorov.lean#L55-L181
https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Kernels.lean#L44-L101
https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/TranslationIntegral.lean#L41-L132
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Transfer
section
/- Original source header, including license and authors:
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-/
/-!
# `L²` compactness criterion: transfer from `BCF` compactness to `L²` (Euclidean)

This file transfers the Arzelà–Ascoli compactness of the `BoundedContinuousFunction` packaging of
`smoothFun` on the compact set `K + tsupport ψ` to a compactness statement in `L²(volume)`.

## Main results

- `smoothL2_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothL2 ψ u | ‖u‖ ≤ R }` has compact closure in `L²(volume)`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.2`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessTransfer : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessTransfer : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessTransfer : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddE_L2CompactnessTransfer : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegE_L2CompactnessTransfer : MeasurableNeg E := by
  infer_instance

variable {K : Set E} {ψ : E → ℝ}

theorem smoothL2_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R)) := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let s : Set E := Kψ (K := K) (ψ := ψ)
  have hs_compact : IsCompact s := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hs : MeasurableSet s := hs_compact.measurableSet
  have hs_lt_top : (volume : Measure E) s < ∞ :=
    hs_compact.measure_lt_top (μ := (volume : Measure E))
  let μs : Measure E := (volume : Measure E).restrict s
  haveI : Fact ((volume : Measure E) s < ∞) := ⟨hs_lt_top⟩
  haveI : IsFiniteMeasure μs := by
    infer_instance
  let mS : ℝ := (MeasureTheory.measureUnivNNReal μs) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  have hmS : 0 ≤ mS := by
    have : 0 ≤ (MeasureTheory.measureUnivNNReal μs) := by simp
    exact Real.rpow_nonneg this _
  let U : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :=
    Metric.closedBall (0 : _) R
  let A :
      Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' U
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' U
  have hA_compact : IsCompact (closure A) :=
    smoothBCF_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hdist_smoothL2_le :
      ∀ u v : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
        dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v) ≤
          mS *
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v) := by
    intro u v
    set Su :=
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
    set Sv :=
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v
    set Bu :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u
    set Bv :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v
    have hBuBv : 0 ≤ ‖Bu - Bv‖ := norm_nonneg _
    -- Work on `F := Su - Sv` and restrict to the finite-measure set `s`.
    let F : (E →₂[(volume : Measure E)] ℝ) := Su - Sv
    let g : E → ℝ := fun x => (F : E → ℝ) x
    have hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (volume : Measure E) := MeasureTheory.Lp.memLp F
    have hg_restrict : MeasureTheory.MemLp g (2 : ℝ≥0∞) μs := hg.restrict s
    let Fs : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μs := hg_restrict.toLp g
    -- Show `Fs` is pointwise bounded by `‖Bu - Bv‖` on `μs`.
    have hF_ae :
        (g =ᵐ[μs] fun x : E =>
          smoothFun (E := E) (K := K) ψ u x -
            smoothFun (E := E) (K := K) ψ v x) := by
      have hsub :
          (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
        simpa [F, g, Su, Sv] using!
          (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
      have hu :
          (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
      have hv :
          (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
      have hF :
          (F : E → ℝ) =ᵐ[(volume : Measure E)]
            fun x : E =>
              smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
        simpa [Pi.sub_apply] using! hsub.trans (hu.sub hv)
      exact MeasureTheory.ae_restrict_of_ae (μ := (volume : Measure E)) (s := s) hF
    have hFs_ae : ((Fs : E → ℝ) =ᵐ[μs] g) := by
      simpa [Fs, g] using!
        (MeasureTheory.MemLp.coeFn_toLp (μ := μs) (p := (2 : ℝ≥0∞)) (f := g) hg_restrict)
    have hbound :
        ∀ᵐ x ∂μs, ‖Fs x‖ ≤ ‖Bu - Bv‖ := by
      have hpoint :
          ∀ x : E, x ∈ s → ‖smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x‖ ≤
            ‖Bu - Bv‖ := by
        intro x hx
        let x' : ↥(Kψ (K := K) (ψ := ψ)) := ⟨x, hx⟩
        have hBu : Bu x' = smoothFun (E := E) (K := K) ψ u x := by
          simp [Bu, x']
        have hBv : Bv x' = smoothFun (E := E) (K := K) ψ v x := by
          simp [Bv, x']
        have : ‖(Bu - Bv) x'‖ ≤ ‖Bu - Bv‖ :=
          (Bu - Bv).norm_coe_le_norm x'
        simpa [hBu, hBv] using! this
      filter_upwards
        [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hs,
          hFs_ae, hF_ae] with x hx hFs hF
      have := hpoint x hx
      -- rewrite through the AE equalities
      simpa [hFs, hF] using! this
    have hnorm_Fs : ‖Fs‖ ≤ mS * ‖Bu - Bv‖ := by
      have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := μs) (p := (2 : ℝ≥0∞))
        (f := Fs) (hC := hBuBv) hbound)
      simpa [mS] using! this
    -- Relate the `L²` norm on `volume` to the restricted norm on `μs` using extension-by-zero.
    have hsupport :
        ∀ x : E, x ∉ s →
          smoothFun (E := E) (K := K) ψ u x -
            smoothFun (E := E) (K := K) ψ v x = 0 := by
      intro x hx
      have hu_supp : Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ s := by
        simpa [s] using!
          (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) u)
      have hv_supp : Function.support (smoothFun (E := E) (K := K) ψ v) ⊆ s := by
        simpa [s] using!
          (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) v)
      have hu0 : smoothFun (E := E) (K := K) ψ u x = 0 := by
        have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ u) := fun hx' => hx (hu_supp hx')
        simpa [Function.support] using! this
      have hv0 : smoothFun (E := E) (K := K) ψ v x = 0 := by
        have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ v) := fun hx' => hx (hv_supp hx')
        simpa [Function.support] using! this
      simp [hu0, hv0]
    have hF0 :
        ∀ᵐ x ∂(volume : Measure E), x ∉ s → g x = 0 := by
      have hF_ae_full :
          (g =ᵐ[(volume : Measure E)]
            fun x : E =>
              smoothFun (E := E) (K := K) ψ u x -
                smoothFun (E := E) (K := K) ψ v x) := by
        have hsub :
            (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
          simpa [F, g, Su, Sv] using!
            (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
        have hu :
            (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
          smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
        have hv :
            (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
          smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
        have hF :
            (F : E → ℝ) =ᵐ[(volume : Measure E)]
              fun x : E =>
                smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
          simpa [Pi.sub_apply] using! hsub.trans (hu.sub hv)
        simpa [g] using! hF
      filter_upwards [hF_ae_full] with x hx
      intro hxnot
      have : smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x = 0 :=
        hsupport x hxnot
      simpa [hx] using! this
    have hF_ind :
        (s.indicator g =ᵐ[(volume : Measure E)] g) := by
      filter_upwards [hF0] with x hx
      by_cases hxmem : x ∈ s
      · simp [g, hxmem]
      · have : g x = 0 := hx hxmem
        simp [g, hxmem, this]
    -- Conclude `‖F‖ = ‖Fs‖` using `extendByZeroₗᵢ` and the indicator identity.
    let Fext :
        MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E) :=
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := s) hs) Fs
    have hFext_ae :
        ((Fext : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E)) :
            E → ℝ) =ᵐ[(volume : Measure E)]
          s.indicator fun x : E => (Fs : E → ℝ) x := by
      simpa [Fext] using!
        (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq
          (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := s) hs Fs)
    have hFs_on :
        ∀ᵐ x ∂(volume : Measure E), x ∈ s → (Fs : E → ℝ) x = g x := by
      -- rewrite the AE equality `Fs = g` on the restricted measure as an implication on `volume`
      have := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure E)) (s := s) hs).1 hFs_ae
      simpa [g] using! this
    have hindicator :
        (s.indicator (fun x : E => (Fs : E → ℝ) x) =ᵐ[(volume : Measure E)] s.indicator g) := by
      filter_upwards [hFs_on] with x hx
      by_cases hxmem : x ∈ s
      · simp [hxmem, hx hxmem]
      · simp [hxmem]
    have hFext_ae' :
        (Fext : E → ℝ) =ᵐ[(volume : Measure E)] g := by
      exact hFext_ae.trans (hindicator.trans hF_ind)
    have hFext_eq : Fext = F := by
      refine MeasureTheory.Lp.ext ?_
      simpa [g, F] using! hFext_ae'
    have hnorm_F : ‖F‖ ≤ mS * ‖Bu - Bv‖ := by
      -- use `‖F‖ = ‖Fs‖` via the isometry.
      have hnorm_ext : ‖Fext‖ = ‖Fs‖ := by
        simp [Fext]
      -- `Fext = F` and `Fs` is bounded.
      have : ‖Fext‖ ≤ mS * ‖Bu - Bv‖ := by
        simpa [hnorm_ext] using! hnorm_Fs
      simpa [hFext_eq] using! this
    -- Convert to the `dist` statement.
    simpa [Su, Sv, Bu, Bv, F, dist_eq_norm, mS, mul_assoc] using! hnorm_F
  have hTB_B : TotallyBounded B := by
    -- Use a finite `BCF` ε-net for `A` with centers in the image, then transfer to `L²`.
    rw [Metric.totallyBounded_iff]
    intro ε hε
    by_cases hmS0 : mS = 0
    ·
      let c : (E →₂[(volume : Measure E)] ℝ) :=
        smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (0 : _)
      refine ⟨{c}, by simp [c], ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hle :=
        hdist_smoothL2_le u (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
      have hdist0 :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              c = 0 := by
        have :
            dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) c ≤ 0 := by
          simpa [c, hmS0] using! hle
        exact le_antisymm this dist_nonneg
      refine mem_iUnion.2 ?_
      refine ⟨c, mem_iUnion.2 ?_⟩
      refine ⟨by simp, ?_⟩
      -- membership in the open ball follows from `dist = 0` and `ε > 0`
      simpa [Metric.mem_ball, hdist0] using! hε
    · have hmSpos : 0 < mS := lt_of_le_of_ne hmS (Ne.symm hmS0)
      let δ : ℝ := ε / mS
      have hδpos : 0 < δ := div_pos hε hmSpos
      obtain ⟨t, htAsub, htFin, htCover⟩ :=
        exists_finite_cover_balls_of_isCompact_closure (s := A) (ε := δ) hA_compact hδpos
      let tFin : Finset (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
        htFin.toFinset
      have htFin_mem :
          ∀ {f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ}, f ∈ tFin ↔ f ∈ t := by
        intro f
        simp [tFin, htFin.mem_toFinset (a := f)]
      let ι : Type _ := { f // f ∈ tFin }
      have hrep :
          ∀ f : ι,
            ∃ u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
              u ∈ U ∧
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u = f.1 := by
        intro f
        have hf_t : f.1 ∈ t := (htFin_mem (f := f.1)).1 f.2
        have hfA : f.1 ∈ A := htAsub hf_t
        rcases hfA with ⟨u, huU, huEq⟩
        exact ⟨u, huU, huEq⟩
      choose uOf huOfU huOfEq using hrep
      let tL2 : Set (E →₂[(volume : Measure E)] ℝ) :=
        Set.range fun f : ι => smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f)
      have htL2_fin : tL2.Finite := Set.finite_range _
      refine ⟨tL2, htL2_fin, ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hBu : (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) ∈ A := by
        exact ⟨u, huU, rfl⟩
      have : smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u ∈ ⋃ x ∈ t, Metric.ball x δ :=
        htCover hBu
      rcases mem_iUnion.1 this with ⟨f, hf⟩
      rcases mem_iUnion.1 hf with ⟨hf_t, hf_ball⟩
      have hf_tFin : f ∈ tFin := (htFin_mem (f := f)).2 hf_t
      let f' : ι := ⟨f, hf_tFin⟩
      have hf_ball' :
          dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) f < δ := hf_ball
      have hdist :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f')) < ε := by
        have hle := hdist_smoothL2_le u (uOf f')
        have hf_eq :
            smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f') = f := by
          simpa [f'] using! huOfEq f'
        have hdist' :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < δ := by
          simpa [hf_eq] using! hf_ball'
        have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < ε := by
          have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                  (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < mS * δ := by
            exact mul_lt_mul_of_pos_left hdist' hmSpos
          have hmul : mS * δ = ε := by
            have hmS_ne : mS ≠ 0 := ne_of_gt hmSpos
            calc
              mS * δ = mS * (ε / mS) := by simp [δ]
              _ = mS * ε / mS := (mul_div_assoc mS ε mS).symm
              _ = ε := by simpa [Pi.smul_apply, Pi.add_apply] using! (mul_div_cancel_left₀ ε hmS_ne)
          simpa [hmul] using! this
        exact lt_of_le_of_lt hle this
      refine mem_iUnion.2 ?_
      refine ⟨smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f'), ?_⟩
      refine mem_iUnion.2 ?_
      refine ⟨?_, hdist⟩
      -- show the chosen center lies in `tL2`
      exact ⟨f', rfl⟩
  -- Compactness follows from total boundedness + completeness of `L²`.
  have hTB_closure : TotallyBounded (closure B) := hTB_B.closure
  have hcomplete : IsComplete (closure B) := isClosed_closure.isComplete
  have hcompact_closure : IsCompact (closure B) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨hTB_closure, hcomplete⟩
  simpa [B, U] using! hcompact_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end

-- Source module: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.FrechetKolmogorov
section
/- Original source header, including license and authors:
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Approximation
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Transfer
import Mathlib.Topology.UniformSpace.Cauchy

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-/
/-!
# `L²` compactness criterion: Fréchet–Kolmogorov (Euclidean, compact support case)

This file packages the final “precompactness via smoothing” step behind the Euclidean `L²`
compactness criterion used by the Rellich–Kondrachov stack:

- the **smoothing operator** `smoothL2 ψ` has compact image on `Metric.closedBall 0 R`;
- the **approximation inequality** bounds `‖smoothL2 ψ u - extendByZeroL2 u‖` by a translation
  error.

We state the criterion at the level needed by the project: families of `L²` functions with common
compact support (modeled as `Lp ℝ 2 (volume.restrict K)` and embedded into `L²(volume)` via
`extendByZeroL2`).

## Main results

- `norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le`:
  if the translation error averaged against `kernelMeasure ψ` is ≤ `η²`, then smoothing approximates
  `extendByZeroL2` within `η`.
- `totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  if a bounded family admits, at every scale `ε`, a kernel `ψ` for which the above translation error
  is uniformly small, then the embedded family is totally bounded in `L²(volume)`.
- `isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  the corresponding compact-closure statement.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.3`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessFrechetKolmogorov : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessFrechetKolmogorov : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessFrechetKolmogorov :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddE_L2CompactnessFrechetKolmogorov : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegE_L2CompactnessFrechetKolmogorov : MeasurableNeg E := by
  infer_instance

variable {K : Set E} {ψ : E → ℝ}

lemma norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
    (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) {η : ℝ} (hη : 0 ≤ η)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (htrans :
      ∫ t,
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (extendByZeroL2 (E := E) (K := K) hKm u)
              - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
        ∂kernelMeasure (E := E) ψ ≤ η ^ 2) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ η := by
  have hsq :
      ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤ η ^ 2 := by
    refine (le_trans ?_ htrans)
    simpa [Pi.smul_apply, Pi.add_apply] using!
      norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
        (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs hψ0 hψint u
  exact (sq_le_sq₀ (norm_nonneg _) hη).1 hsq

theorem totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) := by
  classical
  -- Use the finite `ε`-net characterization of total boundedness.
  refine (Metric.totallyBounded_iff).2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hApprox ε hε with ⟨ψ, hψc, hψcs, hψ0, hψint, htrans⟩
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
  have hB_compact : IsCompact (closure B) :=
    smoothL2_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hB_tot : TotallyBounded B :=
    (totallyBounded_closure).1 hB_compact.totallyBounded
  rcases Metric.finite_approx_of_totallyBounded hB_tot (ε / 2) hε2 with ⟨t, htB, htfin, hBcover⟩
  refine ⟨t, htfin, ?_⟩
  intro x hx
  rcases hx with ⟨u, huA, rfl⟩
  have huR : u ∈ Metric.closedBall (0 : _) R := hA huA
  have hSu_mem : smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈ B := ⟨u, huR, rfl⟩
  have hSu_cover :
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈
        ⋃ y, ⋃ (_ : y ∈ t), Metric.ball y (ε / 2) :=
    hBcover hSu_mem
  rcases Set.mem_iUnion.1 hSu_cover with ⟨y, hy⟩
  rcases Set.mem_iUnion.1 hy with ⟨hyT, hyBall⟩
  have hyDist : dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y < ε / 2 := by
    simpa [Metric.ball, Set.mem_setOf_eq] using! hyBall
  have hdist_smooth_ext :
      dist (extendByZeroL2 (E := E) (K := K) hKm u)
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) ≤ ε / 2 := by
    have hη : 0 ≤ ε / 2 := le_of_lt hε2
    have hnorm :
        ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ ε / 2 :=
      norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
        (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs hψ0 hψint (η := ε / 2) hη u (htrans u huA)
    -- Switch to `dist` with the argument order used by `dist_triangle`.
    have hdist :
        dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            (extendByZeroL2 (E := E) (K := K) hKm u) ≤ ε / 2 := by
      simpa [dist_eq_norm] using! hnorm
    simpa [dist_comm] using! hdist
  have hxDist : dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε := by
    have htri :=
      dist_triangle (extendByZeroL2 (E := E) (K := K) hKm u)
        (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
    have hlt :
        dist (extendByZeroL2 (E := E) (K := K) hKm u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            + dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
          < ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt hdist_smooth_ext hyDist
    have htmp :
        dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε / 2 + ε / 2 :=
      lt_of_le_of_lt htri hlt
    simpa [add_halves ε] using! htmp
  have hxBall : extendByZeroL2 (E := E) (K := K) hKm u ∈ Metric.ball y ε := by
    simpa [Metric.ball, Set.mem_setOf_eq] using! hxDist
  exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hyT, hxBall⟩⟩

theorem isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    IsCompact (closure (extendByZeroL2 (E := E) (K := K) hKm '' A)) := by
  have ht :
      TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) :=
    totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) hK hKm hR hA hApprox
  exact (ht.closure).isCompact_of_isClosed isClosed_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end

-- Source module: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Kernels
section
/- Original source header, including license and authors:
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-/
/-!
# `L²` compactness criterion: existence of small-support probability kernels (Euclidean)

This file provides a “kernel factory” for the Euclidean Fréchet–Kolmogorov / Riesz–Kolmogorov
criterion: for any radius `δ > 0`, produce a continuous compactly supported function `ψ : E → ℝ`
such that:

- `ψ ≥ 0`,
- `tsupport ψ ⊆ Metric.ball 0 δ`,
- `∫ ψ = 1` (so `kernelMeasure ψ` is a probability measure).

The construction uses mathlib’s `exists_smooth_tsupport_subset` bump-function lemma and normalizes
by its (positive) integral.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.5`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessKernels : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessKernels : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessKernels : OpensMeasurableSpace E := by
  infer_instance

/-- For any `δ > 0`, there exists a continuous compactly supported kernel `ψ` supported in
`Metric.ball 0 δ`, with `ψ ≥ 0` and `∫ ψ = 1` (w.r.t. Lebesgue measure). -/
theorem exists_kernel_tsupport_subset_ball_integral_eq_one {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∫ x, ψ x ∂(volume : Measure E) = 1) ∧ tsupport ψ ⊆ Metric.ball (0 : E) δ := by
  classical
  -- Start from a smooth bump supported in `ball 0 δ` with value `1` at `0`.
  have hs : (Metric.ball (0 : E) δ) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hδ
  rcases exists_contDiff_tsupport_subset (n := ⊤)
    (E := E) (s := Metric.ball (0 : E) δ) (x := (0 : E)) hs with
    ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf0⟩
  have hf_cont : Continuous f := hf_smooth.continuous
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    have hx : f x ∈ Set.Icc (0 : ℝ) 1 := hf_range ⟨x, rfl⟩
    exact hx.1
  have hf0_ne : f (0 : E) ≠ 0 := by
    -- `f 0 = 1`.
    simp [hf0]
  -- The integral is strictly positive (Lebesgue is an open-positive measure).
  have hIpos :
      0 < ∫ x, f x ∂(volume : Measure E) := by
    simpa [Pi.smul_apply, Pi.add_apply] using!
      (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure E))
        hf_cont hf_cs hf_nonneg hf0_ne)
  set I : ℝ := ∫ x, f x ∂(volume : Measure E)
  have hI0 : I ≠ 0 := ne_of_gt hIpos
  have hIpos' : 0 < I := by simpa [I] using! hIpos
  -- Normalize: `ψ = I⁻¹ • f`.
  let ψ : E → ℝ := fun x => I⁻¹ * f x
  have hψc : Continuous ψ := by
    simpa [ψ] using! (continuous_const.mul hf_cont)
  have hψcs : HasCompactSupport ψ := by
    simpa [ψ, smul_eq_mul] using!
      (HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs)
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    have hInv : 0 ≤ I⁻¹ := by
      have : 0 ≤ I := le_of_lt hIpos'
      simpa [Pi.smul_apply, Pi.add_apply] using! inv_nonneg.2 this
    simpa [ψ] using! mul_nonneg hInv (hf_nonneg x)
  have hψint : ∫ x, ψ x ∂(volume : Measure E) = 1 := by
    have : (∫ x, ψ x ∂(volume : Measure E)) = I⁻¹ * I := by
      -- Pull out the constant scalar.
      simpa [ψ, I] using!
        (MeasureTheory.integral_const_mul (μ := (volume : Measure E)) (r := I⁻¹) (f := f))
    simp [this, hI0]
  have hψ_tsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ := by
    -- Scaling does not enlarge topological support; use the bump support inclusion.
    have hsub : tsupport ψ ⊆ tsupport f := by
      simpa [ψ, smul_eq_mul] using! (tsupport_smul_subset_right (f := fun _x : E => I⁻¹) (g := f))
    exact hsub.trans hf_tsupp
  exact ⟨ψ, hψc, hψcs, hψ0, hψint, hψ_tsupp⟩

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end

-- Source module: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.TranslationIntegral
section
/- Original source header, including license and authors:
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Approximation
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-/
/-!
# `L²` compactness criterion: bounding the translation-integral by a translation modulus

This file provides a small but crucial bridge lemma used to connect a uniform translation modulus
on `L²(volume)` with the `kernelMeasure` translation-integral bound appearing in the
approximation-identity estimate.

The core observation is that if `ψ` is supported in a neighborhood where the translation modulus is
≤ `η`, then the averaged squared translation error against the probability measure
`kernelMeasure ψ` is ≤ `η²`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.4`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessTranslationIntegral : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessTranslationIntegral : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessTranslationIntegral :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddE_L2CompactnessTranslationIntegral : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegE_L2CompactnessTranslationIntegral : MeasurableNeg E := by
  infer_instance

variable {ψ : E → ℝ}

private lemma kernelMeasure_compl_ball_eq_zero_of_tsupport_subset {δ : ℝ}
    (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ) :
    kernelMeasure (E := E) ψ ((Metric.ball (0 : E) δ)ᶜ) = 0 := by
  classical
  have hψzero : ∀ x : E, x ∈ (Metric.ball (0 : E) δ)ᶜ → ψ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ψ := by
      intro hx_ts
      exact hx (hψsupp hx_ts)
    exact image_eq_zero_of_notMem_tsupport (f := ψ) hx'
  have hmeas : MeasurableSet ((Metric.ball (0 : E) δ)ᶜ) :=
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : E) δ)).compl
  have hEq :
      Set.EqOn (fun x : E => ENNReal.ofReal (ψ x)) 0 ((Metric.ball (0 : E) δ)ᶜ) := by
    intro x hx
    simp [hψzero x hx]
  -- Expand `kernelMeasure` and note the density is identically `0` on the set.
  simp [kernelMeasure, MeasureTheory.withDensity_apply, hmeas,
    MeasureTheory.setLIntegral_eq_zero
      (μ := (volume : Measure E))
      (s := (Metric.ball (0 : E) δ)ᶜ) hmeas hEq]

theorem integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    {δ η : ℝ} (hη : 0 ≤ η) (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ)
    (F : (E →₂[(volume : Measure E)] ℝ))
    (hmod :
      ∀ t : E, t ∈ Metric.ball (0 : E) δ →
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η) :
    ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
      ∂kernelMeasure (E := E) ψ ≤ η ^ 2 := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩
  have hμzero : μ ((Metric.ball (0 : E) δ)ᶜ) = 0 := by
    simpa [μ] using! kernelMeasure_compl_ball_eq_zero_of_tsupport_subset (E := E) (ψ := ψ) hψsupp
  have hAE_ball : (Metric.ball (0 : E) δ) ∈ MeasureTheory.ae μ :=
    (MeasureTheory.mem_ae_iff.2 hμzero)
  -- On `Metric.ball 0 δ`, the squared translation error is bounded by `η²`.
  have hAE_bound :
      ∀ᵐ t : E ∂μ,
        ‖‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2‖ ≤ η ^ 2 := by
    filter_upwards [hAE_ball] with t ht
    have hle : ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η := hmod t ht
    have hsq :
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ≤ η ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hη).2 hle
    have hnonneg : 0 ≤ ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 :=
      sq_nonneg _
    have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hηnonneg] using! hsq
  have hnorm_int :
      ‖∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ‖ ≤ η ^ 2 * μ.real Set.univ := by
    simpa [Pi.smul_apply, Pi.add_apply] using!
      (MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun t : E => ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2)
        (C := η ^ 2) hAE_bound)
  have hμreal : μ.real Set.univ = 1 := by
    -- `μ` is a probability measure.
    simp [MeasureTheory.measureReal_def]
  have hnonneg_int :
      0 ≤ ∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    exact sq_nonneg _
  -- Use `|∫ f| = ∫ f` for a nonnegative integrand.
  have habs :
      |∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ| ≤ η ^ 2 := by
    have := hnorm_int
    -- Replace `‖·‖` by `abs` in `ℝ` and simplify `μ.real univ = 1`.
    simpa [Real.norm_eq_abs, hμreal, mul_one] using! this
  simpa [abs_of_nonneg hnonneg_int, μ] using! habs

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end


