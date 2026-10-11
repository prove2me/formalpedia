-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0165
-- name    : PNT_ZeroFree_433_0165
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:01:43.254459+00:00
-- url     : https://prove2.me/theorems/1a80e47d-dfb4-4f41-89d5-d37d5fe65cd8
-- title:
--   Zero-free region foundations: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Compactness, RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean [0165]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Compactness
--   - RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Compactness.lean#L47-L143
--   https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/ArzelaAscoli.lean#L45-L439

import Definitions.Def_PNT_ZeroFree_433_0164
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.UniformSpace.HeineCantor

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Compactness.lean#L47-L143
https://github.com/abenenson/rellich-kondrachov/blob/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23/RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/ArzelaAscoli.lean#L45-L439
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Compactness
section
/- Original source header, including license and authors:
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Smoothing
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-/
/-!
# `L²` compactness criterion: compact smoothing operator (Euclidean)

This file proves the compactness of the fixed-kernel smoothing operator used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `Kψ`: the compact set `K + tsupport ψ` controlling supports of smoothed functions.
- `smoothBCF`: `smoothFun` packaged as a `BoundedContinuousFunction` on `Kψ`.
- `uniformContinuous_ψ`: `UniformContinuous ψ` from `Continuous ψ` + `HasCompactSupport ψ`.

The Arzelà–Ascoli compactness statement for `smoothBCF` lives in
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli`.

This is tracked under Beads `lean-103.5.2.26.5.3.2.2.1`.
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

local instance instMeasurableSpaceE_L2CompactnessCompactness : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessCompactness : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessCompactness : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddE_L2CompactnessCompactness : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegE_L2CompactnessCompactness : MeasurableNeg E := by
  infer_instance

variable {K : Set E}
variable {ψ : E → ℝ}

/-- The natural compact codomain for smoothing on `K` by a compactly supported kernel `ψ`. -/
def Kψ : Set E :=
  K + tsupport ψ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma isCompact_Kψ (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact (Kψ (K := K) (ψ := ψ)) :=
  IsCompact.add hK hψcs.isCompact

private def smoothOn (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    C(↥(Kψ (K := K) (ψ := ψ)), ℝ) where
  toFun x := smoothFun (E := E) (K := K) ψ u x
  continuous_toFun := by
    have : Continuous (smoothFun (E := E) (K := K) ψ u) :=
      continuous_smoothFun (E := E) (K := K) (ψ := ψ) (hKm := hKm) hψc hψcs u
    simpa [Pi.smul_apply, Pi.add_apply] using! this.comp continuous_subtype_val

/-- `smoothFun` packaged as a `BoundedContinuousFunction` on the compact set `K + tsupport ψ`. -/
def smoothBCF (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ :=
  letI : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
    isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
  BoundedContinuousFunction.mkOfCompact (smoothOn (E := E) (K := K) (ψ := ψ) hKm hψc hψcs u)

@[simp] lemma smoothBCF_apply (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (x : ↥(Kψ (K := K) (ψ := ψ))) :
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
      smoothFun (E := E) (K := K) ψ u x := by
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma uniformContinuous_ψ (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    UniformContinuous ψ := by
  classical
  -- `HasCompactSupport` implies `ψ = 0` outside a compact set, hence `ψ → 0` along `cocompact`.
  refine
    Continuous.uniformContinuous_of_tendsto_cocompact (f := ψ) (x := (0 : ℝ)) hψc ?_
  -- Show `ψ → 0` along `cocompact` using the `ε`-ball characterization.
  refine (Metric.tendsto_nhds.2 ?_)
  intro ε hε
  refine Filter.mem_cocompact'.mpr ⟨tsupport ψ, hψcs, ?_⟩
  intro x hx
  -- If `ψ x` is `ε`-far from `0`, then `ψ x ≠ 0`, hence `x` belongs to the support and therefore
  -- to the topological support.
  have hx' : ¬ dist (ψ x) 0 < ε := by
    simpa [Set.mem_compl_iff, Set.mem_setOf_eq] using! hx
  have hxε : ε ≤ dist (ψ x) 0 := le_of_not_gt (by simpa [gt_iff_lt] using! hx')
  have hx0 : ψ x ≠ 0 := by
    intro hψ0
    have : dist (ψ x) 0 = 0 := by simp [hψ0]
    have : ε ≤ 0 := by simpa [this] using! hxε
    exact not_lt_of_ge this hε
  have hx_supp : x ∈ Function.support ψ := by
    simpa [Function.support] using! hx0
  have hx_tsupp : x ∈ tsupport ψ := by
    have : x ∈ closure (Function.support ψ) := subset_closure hx_supp
    simpa [tsupport] using! this
  exact hx_tsupp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma aestronglyMeasurable_const_one
    (μ : Measure E) : AEStronglyMeasurable (fun _x : E => (1 : ℝ)) μ :=
  (aestronglyMeasurable_const : AEStronglyMeasurable (fun _x : E => (1 : ℝ)) μ)

private lemma integrable_norm_L2_restrict (hK : IsCompact K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Integrable (fun x : E => ‖u x‖) (volume.restrict K) := by
  classical
  -- On a finite measure space, `L² ⊆ L¹`.
  have hμ : (volume : Measure E) K < ∞ :=
    (hK.measure_lt_top (μ := (volume : Measure E)))
  letI : Fact ((volume : Measure E) K < ∞) := ⟨hμ⟩
  haveI : IsFiniteMeasure (volume.restrict K) := by
    infer_instance
  have hu2 : MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
    MeasureTheory.Lp.memLp u
  have hu1 : MemLp (fun x : E => u x) (1 : ℝ≥0∞) (volume.restrict K) :=
    hu2.mono_exponent (by norm_num)
  -- `MemLp` with exponent `1` is `Integrable`.
  exact (memLp_one_iff_integrable.mp hu1).norm

/-!
The remainder of the compactness proof (Arzelà–Ascoli on the family `smoothBCF '' closedBall`)
is tracked as part of `lean-103.5.2.26.5.3.2.2.1`.

We intentionally keep the helper lemmas above in this file so the final proof can stay short and
only reference re-usable bounds.
-/

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end

-- Source module: RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli
section
/- Original source header, including license and authors:
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.Compactness
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


-/
/-!
# `L²` compactness criterion: Arzelà–Ascoli for the smoothing operator (Euclidean)

This file proves the Arzelà–Ascoli step for the compact smoothing operator used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main result

- `smoothBCF_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothFun ψ u | ‖u‖ ≤ R }` restricted to the compact set `K + tsupport ψ`
  has compact closure in `BoundedContinuousFunction`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.1`.
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

local instance instMeasurableSpaceE_L2CompactnessArzelaAscoli : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessArzelaAscoli : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessArzelaAscoli : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddE_L2CompactnessArzelaAscoli : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegE_L2CompactnessArzelaAscoli : MeasurableNeg E := by
  infer_instance

variable {K : Set E} {ψ : E → ℝ}

private lemma smoothFun_eq_integral_restrict (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    smoothFun (E := E) (K := K) ψ u x =
      ∫ t, u t * ψ (x - t) ∂(volume.restrict K) := by
  classical
  -- Unfold convolution, then restrict the integral using the indicator defining `extendByZeroFun`.
  have :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (extendByZeroFun (E := E) (K := K) u t) • ψ (x - t) ∂(volume : Measure E) := by
    simp [smoothFun, MeasureTheory.convolution_lsmul]
  have h_ind :
      (fun t : E => extendByZeroFun (E := E) (K := K) u t * ψ (x - t)) =
        K.indicator (fun t : E => u t * ψ (x - t)) := by
    funext t
    by_cases ht : t ∈ K <;> simp [extendByZeroFun, ht]
  -- Restrict to `K` using the indicator.
  simp [this, h_ind, MeasureTheory.integral_indicator hKm]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma isCompact_diffSet (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact
      ((fun p : E × E => p.1 - p.2) '' ((Kψ (K := K) (ψ := ψ)) ×ˢ K)) := by
  have hKψ : IsCompact (Kψ (K := K) (ψ := ψ)) := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hprod : IsCompact ((Kψ (K := K) (ψ := ψ)) ×ˢ K) := hKψ.prod hK
  refine hprod.image ?_
  exact (continuous_fst.sub continuous_snd)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma exists_norm_ψ_bound_on_diffSet (hK : IsCompact K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ↥(Kψ (K := K) (ψ := ψ)), ∀ t : E, t ∈ K → ‖ψ ((x : E) - t)‖ ≤ C := by
  classical
  let diffSet : Set E :=
    (fun p : E × E => p.1 - p.2) '' ((Kψ (K := K) (ψ := ψ)) ×ˢ K)
  have hdiff : IsCompact diffSet := isCompact_diffSet (E := E) (K := K) (ψ := ψ) hK hψcs
  by_cases hne : diffSet.Nonempty
  · -- Use the extreme value theorem on the continuous function `z ↦ ‖ψ z‖`.
    have hcont : Continuous (fun z : E => ‖ψ z‖) := hψc.norm
    rcases hdiff.exists_isMaxOn hne (hcont.continuousOn) with ⟨z0, hz0, hzmax⟩
    refine ⟨‖ψ z0‖, norm_nonneg _, ?_⟩
    intro x t ht
    have hx : (x : E) ∈ Kψ (K := K) (ψ := ψ) := x.2
    have hx_t : (x : E) - t ∈ diffSet := by
      refine ⟨((x : E), t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    exact (isMaxOn_iff.1 hzmax) _ hx_t
  · -- `diffSet = ∅`: take the trivial bound.
    refine ⟨0, le_rfl, ?_⟩
    intro x t ht
    exfalso
    have hx : (x : E) ∈ Kψ (K := K) (ψ := ψ) := x.2
    have : (x : E) - t ∈ diffSet := by
      refine ⟨((x : E), t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    exact hne ⟨(x : E) - t, this⟩

/-- Arzelà--Ascoli: smoothing maps `L²(K)` bounded sets into a precompact set
in `BCF(K + tsupport ψ)`. -/
theorem smoothBCF_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _)
            R)) := by
  classical
  -- Radius `0`: the image is a singleton, hence compact.
  by_cases hR0 : R = 0
  · subst hR0
    have hball :
        Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) 0 = {0} := by
      ext u
      simp
    -- Reduce to a singleton.
    simp [hball]
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    -- Compactness of the codomain.
    letI : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
      isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
    let A :
        Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
    -- `volume.restrict K` is finite since `K` is compact.
    have hμK : (volume : Measure E) K < ∞ := hK.measure_lt_top (μ := (volume : Measure E))
    letI : Fact ((volume : Measure E) K < ∞) := ⟨hμK⟩
    haveI : IsFiniteMeasure (volume.restrict K) := by
      infer_instance
    let μ : Measure E := (volume : Measure E).restrict K
    let mK : ℝ :=
      (MeasureTheory.measureUnivNNReal (volume.restrict K)) ^ ((2 : ℝ≥0∞).toReal⁻¹)
    have hmK : 0 ≤ mK := by
      have : 0 ≤ (MeasureTheory.measureUnivNNReal (volume.restrict K)) := by simp
      exact Real.rpow_nonneg this _
    -- Uniform bound on `ψ` over the relevant compact difference set.
    obtain ⟨Cψ, hCψ_nonneg, hψ_bound⟩ :=
      exists_norm_ψ_bound_on_diffSet (E := E) (K := K) (ψ := ψ) hK hψc hψcs
    -- A compact ball controlling all values.
    let s : Set ℝ := Metric.closedBall (0 : ℝ) (R * (mK * Cψ))
    have hs : IsCompact s := by
      simpa [s] using! isCompact_closedBall (0 : ℝ) (R * (mK * Cψ))
    -- Pointwise compact range: each function in `A` takes values in `s`.
    have in_s :
        ∀ (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) (x : ↥(Kψ (K := K) (ψ := ψ))),
          f ∈ A → f x ∈ s := by
      intro f x hfA
      rcases hfA with ⟨u, hu_ball, rfl⟩
      have hu_norm : ‖u‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using! hu_ball
      -- Build the `L²(K)` kernel element.
      have hker :
          MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
        refine MemLp.of_bound (μ := (volume.restrict K))
          (hf := (hψc.aestronglyMeasurable.comp_measurable
            (measurable_const.sub measurable_id))) Cψ ?_
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            (μ := (volume : Measure E)) hKm] with t ht
        exact hψ_bound x t ht
      let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
        hker.toLp (fun t : E => ψ ((x : E) - t))
      have hkx_norm : ‖kx‖ ≤ mK * Cψ := by
        have h_ae :
            ∀ᵐ t ∂(volume.restrict K), ‖(fun t : E => ψ ((x : E) - t)) t‖ ≤ Cψ := by
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound x t ht
        have := (MeasureTheory.Lp.norm_le_of_ae_bound
          (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
          (f := kx) (hC := hCψ_nonneg) (by
            -- transport the bound through the `toLp` representative
            filter_upwards [h_ae,
              MeasureTheory.MemLp.coeFn_toLp
                (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                (f := fun t : E => ψ ((x : E) - t))
                hker] with t ht hrep
            simpa [kx, hrep] using! ht))
        simpa [mK] using! this
      -- Express the smoothing value as an `L²` inner product, then apply Cauchy–Schwarz.
      have hsmooth :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            ∫ t, u t * kx t ∂(volume.restrict K) := by
        have h_ae :
            (fun t : E => u t * kx t) =ᵐ[volume.restrict K] fun t : E => u t * ψ ((x : E) - t) := by
          filter_upwards [MeasureTheory.MemLp.coeFn_toLp
            (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
            (f := fun t : E => ψ ((x : E) - t))
            hker] with t ht
          simp [kx, ht]
        -- rewrite `smoothFun` as an integral on `volume.restrict K`
        rw [smoothFun_eq_integral_restrict
          (E := E) (K := K) (ψ := ψ) (hKm := hKm) u (x : E)]
        exact (MeasureTheory.integral_congr_ae h_ae.symm)
      have hsmooth' :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            ∫ t, kx t * u t ∂(volume.restrict K) := by
        simp [hsmooth, mul_comm]
      have hinner :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
        erw [MeasureTheory.L2.inner_def]; exact hsmooth'
      have habs :
          |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ ‖u‖ * ‖kx‖ := by
        simpa [hinner] using!
          (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx)
      have habs' : |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ R * (mK * Cψ) := by
        calc
          |smoothFun (E := E) (K := K) ψ u (x : E)|
              ≤ ‖u‖ * ‖kx‖ := habs
          _ ≤ R * (mK * Cψ) := by
            exact mul_le_mul hu_norm hkx_norm (norm_nonneg _) hR
      have : dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x) 0 ≤ R * (mK * Cψ) := by
        simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
          dist_eq_norm, Real.norm_eq_abs] using habs'
      simpa [s, Metric.mem_closedBall, dist_eq_norm] using! this
    -- Equicontinuity for `A`.
    have H' : UniformEquicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) := by
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      -- Handle the zero-measure case separately (then `mK = 0` and everything is constant).
      by_cases hmK0 : mK = 0
      · refine ⟨1, by norm_num, ?_⟩
        intro x y _ f
        -- With `mK = 0`, the range bound forces all values to be `0`.
        have hx0 : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x) 0 ≤
            R * (mK * Cψ) := by
          have :
              (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x ∈ s :=
            in_s (f := (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ)) x f.property
          simpa [s, Metric.mem_closedBall] using! this
        have hy0 : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y) 0 ≤
            R * (mK * Cψ) := by
          have :
              (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y ∈ s :=
            in_s (f := (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ)) y f.property
          simpa [s, Metric.mem_closedBall] using! this
        have hx0' :
            dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x) 0 = 0 := by
          have : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x) 0 ≤ 0 := by
            simpa [hmK0] using! hx0
          exact le_antisymm this dist_nonneg
        have hy0' :
            dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y) 0 = 0 := by
          have : dist ((f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y) 0 ≤ 0 := by
            simpa [hmK0] using! hy0
          exact le_antisymm this dist_nonneg
        have hx : (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) x = 0 :=
          dist_eq_zero.1 hx0'
        have hy : (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) y = 0 :=
          dist_eq_zero.1 hy0'
        simpa [hx, hy] using! hε
      · have hRmK_ne : R * mK ≠ 0 := mul_ne_zero hR0 hmK0
        let ε2 : ℝ := ε / 2
        have hε2pos : 0 < ε2 := by
          simpa [ε2] using! half_pos hε
        let ε' : ℝ := ε2 / (R * mK)
        have hε'pos : 0 < ε' :=
          div_pos hε2pos (mul_pos hRpos (lt_of_le_of_ne hmK (Ne.symm hmK0)))
        have hε'lt : R * mK * ε' = ε2 := by
          dsimp [ε']
          field_simp [hRmK_ne, mul_assoc, mul_left_comm, mul_comm]
        -- Use uniform continuity of `ψ` to get `δ`.
        have hUC : UniformContinuous ψ := uniformContinuous_ψ (E := E) (ψ := ψ) hψc hψcs
        rcases (Metric.uniformContinuous_iff.1 hUC) ε' hε'pos with ⟨δ, hδpos, hδ⟩
        refine ⟨δ, hδpos, ?_⟩
        intro x y hxy f
        -- Work with the `smoothBCF` representative of `f`.
        rcases f.property with ⟨u, hu_ball, hu_eq⟩
        have hu_eq' :
            (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) =
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u := by
          simpa [Pi.smul_apply, Pi.add_apply] using! hu_eq.symm
        have hu_norm : ‖u‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using! hu_ball
        -- Kernel elements at `x` and `y`.
        have hkerx :
            MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
          refine MemLp.of_bound (μ := (volume.restrict K))
            (hf := (hψc.aestronglyMeasurable.comp_measurable
              (measurable_const.sub measurable_id))) Cψ ?_
          filter_upwards
            [MeasureTheory.ae_restrict_mem
              (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound x t ht
        have hkery :
            MemLp (fun t : E => ψ ((y : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
          refine MemLp.of_bound (μ := (volume.restrict K))
            (hf := (hψc.aestronglyMeasurable.comp_measurable
              (measurable_const.sub measurable_id))) Cψ ?_
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound y t ht
        let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
          hkerx.toLp (fun t : E => ψ ((x : E) - t))
        let ky : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
          hkery.toLp (fun t : E => ψ ((y : E) - t))
        -- AE bound on `‖kx - ky‖` by `ε'`.
        have h_ae :
            ∀ᵐ t ∂(volume.restrict K), ‖(kx - ky) t‖ ≤ ε' := by
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm,
            MeasureTheory.MemLp.coeFn_toLp (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
              (f := fun t : E => ψ ((x : E) - t)) hkerx,
            MeasureTheory.MemLp.coeFn_toLp (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
              (f := fun t : E => ψ ((y : E) - t)) hkery,
            (MeasureTheory.Lp.coeFn_sub (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞)) kx ky)] with
            t ht hx_t hy_t hsub
          have hxy' : dist ((x : E) - t) ((y : E) - t) < δ := by
            simpa [sub_eq_add_neg, add_assoc] using! hxy
          have hψxy : dist (ψ ((x : E) - t)) (ψ ((y : E) - t)) < ε' :=
            hδ (a := (x : E) - t) (b := (y : E) - t) hxy'
          have : ‖ψ ((x : E) - t) - ψ ((y : E) - t)‖ ≤ ε' := by
            simpa [dist_eq_norm, sub_eq_add_neg] using! le_of_lt hψxy
          have hx' : kx t = ψ ((x : E) - t) := by simpa [kx] using! hx_t
          have hy' : ky t = ψ ((y : E) - t) := by simpa [ky] using! hy_t
          have hnorm : ‖kx t - ky t‖ ≤ ε' := by
            simpa [hx', hy'] using! this
          have hsub' : (kx - ky) t = kx t - ky t := by
            simpa [Pi.sub_apply] using! hsub
          simpa [hsub'.symm] using! hnorm
        have hkdiff : ‖kx - ky‖ ≤ mK * ε' := by
          have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
            (f := (kx - ky : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ)) (hC := le_of_lt hε'pos) h_ae)
          simpa [mK, mul_comm, mul_left_comm, mul_assoc] using! this
        -- Bound the difference of values using Cauchy–Schwarz.
        have hdist :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
              ≤ ‖u‖ * ‖kx - ky‖ := by
          -- Express each value as an inner product.
          have hx_val :
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
                inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
            have hsmooth :
                smoothFun (E := E) (K := K) ψ u (x : E) =
                  ∫ t, u t * kx t ∂(volume.restrict K) := by
              have h_ae' :
                  (fun t : E => u t * kx t) =ᵐ[volume.restrict K]
                    fun t : E => u t * ψ ((x : E) - t) := by
                filter_upwards [MeasureTheory.MemLp.coeFn_toLp
                  (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                  (f := fun t : E => ψ ((x : E) - t))
                  hkerx] with t ht
                simp [kx, ht]
              rw [smoothFun_eq_integral_restrict
                (E := E) (K := K) (ψ := ψ) (hKm := hKm)
                u (x : E)]
              exact (MeasureTheory.integral_congr_ae h_ae'.symm)
            have hsmooth' :
                smoothFun (E := E) (K := K) ψ u (x : E) =
                  ∫ t, kx t * u t ∂(volume.restrict K) := by
              simp [hsmooth, mul_comm]
            erw [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
              MeasureTheory.L2.inner_def]; exact hsmooth'
          have hy_val :
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y =
                inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) ky := by
            have hsmooth :
                smoothFun (E := E) (K := K) ψ u (y : E) =
                  ∫ t, u t * ky t ∂(volume.restrict K) := by
              have h_ae' :
                  (fun t : E => u t * ky t) =ᵐ[volume.restrict K]
                    fun t : E => u t * ψ ((y : E) - t) := by
                filter_upwards [MeasureTheory.MemLp.coeFn_toLp
                  (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                  (f := fun t : E => ψ ((y : E) - t))
                  hkery] with t ht
                simp [ky, ht]
              rw [smoothFun_eq_integral_restrict
                (E := E) (K := K) (ψ := ψ) (hKm := hKm)
                u (y : E)]
              exact (MeasureTheory.integral_congr_ae h_ae'.symm)
            have hsmooth' :
                smoothFun (E := E) (K := K) ψ u (y : E) =
                  ∫ t, ky t * u t ∂(volume.restrict K) := by
              simp [hsmooth, mul_comm]
            erw [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y,
              MeasureTheory.L2.inner_def]; exact hsmooth'
          have :
              ‖smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x -
                  smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y‖ ≤
                ‖u‖ * ‖kx - ky‖ := by
            have :
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x -
                    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y =
                  inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky) := by
              simp [hx_val, hy_val, inner_sub_right]
            have this' :
                smoothFun (E := E) (K := K) ψ u (x : E) - smoothFun (E := E) (K := K) ψ u (y : E) =
                  inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky) := by
              simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs] using! this
            have hCS :=
              (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky))
            simpa [this', dist_eq_norm, Real.norm_eq_abs] using! hCS
          simpa [dist_eq_norm] using! this
        have hle :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
              ≤ R * (mK * ε') := by
          calc
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
                ≤ ‖u‖ * ‖kx - ky‖ := hdist
            _ ≤ ‖u‖ * (mK * ε') := by
              exact mul_le_mul_of_nonneg_left hkdiff (norm_nonneg _)
            _ ≤ R * (mK * ε') := by
              have hmKε' : 0 ≤ mK * ε' := mul_nonneg hmK (le_of_lt hε'pos)
              exact mul_le_mul_of_nonneg_right hu_norm hmKε'
        have hRmkε' : R * (mK * ε') = ε2 := by
          have : R * mK * ε' = ε2 := by
            simpa [ε', mul_assoc] using! hε'lt
          simpa [mul_assoc] using! this
        have hle' :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y) ≤ ε2 := by
          simpa [hRmkε'] using! hle
        have hε2lt : ε2 < ε := by
          simpa [ε2] using! half_lt_self hε
        have :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y) < ε :=
          lt_of_le_of_lt hle' hε2lt
        simpa [hu_eq'] using! this
    have H : Equicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) := H'.equicontinuous
    -- Apply Arzelà–Ascoli.
    simpa [A, s] using!
      (BoundedContinuousFunction.arzela_ascoli (α := ↥(Kψ (K := K) (ψ := ψ))) (β := ℝ)
        (s := s) hs A (fun f x hf => in_s f x hf) H)

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end


