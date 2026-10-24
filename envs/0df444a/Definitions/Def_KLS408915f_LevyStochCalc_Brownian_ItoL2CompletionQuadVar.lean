-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
-- name    : KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:47:38.048991+00:00
-- url     : https://prove2.me/theorems/2d61763c-bda0-4b0b-8742-27c485fbe647
-- title:
--   Isometry and right-continuity of the completed Brownian Itô integral
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For $T>0$, `isometry_stochasticIntegralBrownian` identifies the squared $\operatorname{ENNReal}$ norm of the constructed integral with the time-space energy of $H$ on $[0,T]$: $$\int\|F_T\|^2\,dP=\int\!\!\int_{[0,T]}\|H(\omega,s)\|^2\,ds\,dP.$$ The bundle also proves $F_t\in L^2(P)$, vanishing a.e. for $t\le0$, right-continuity of the time slices in $L^2$, and the martingale property with respect to the right-continuous filtration $\mathcal F.\mathrm{rightCont}$. `compensatorH_memLp_prod` records product-measure $L^2$ membership of $H$ on each positive finite horizon.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean#L38-L300 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionQuadVar`, definition bundle `KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_Chaining
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_CoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_IsKolmogorovProcess
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsov
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsovInequality
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_LimitModification
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section MasterSequence
variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
include hℱ in
/-- **Conjunct 3: the L²-isometry** `∫⁻‖F T‖² = ∫⁻∫⁻_{[0,T]}‖H‖²` for `T > 0`.
The squared `L²`-norm of `Iₙ(T)` equals `∫⁻∫⁻_{[0,T]}‖Gₙ.eval‖²` (intermediate
isometry), converges to `∫⁻‖F T‖²` (norm continuity of the `L²`-limit) and to
`∫⁻∫⁻_{[0,T]}‖H‖²` (`masterApprox_evalNorm_tendsto`); uniqueness of limits. -/
lemma isometry_stochasticIntegralBrownian {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set Flp := stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global T with hFlp
  have htend : Filter.Tendsto (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global T n)
      Filter.atTop (nhds Flp) :=
    (masterLp_cauchySeq W ℱ hℱ H h_meas h_progMeas h_sq_int_global (le_of_lt hT)).tendsto_limUnder
  have hn := (htend.enorm).ennrpow_const 2
  simp only [MeasureTheory.Lp.enorm_def] at hn
  -- limit `eLpNorm ↑↑Flp ^ 2 = ∫⁻‖F T‖²`
  have hlim : MeasureTheory.eLpNorm (↑↑Flp : Ω → ℝ) 2 P ^ (2 : ℝ)
      = ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    rw [eLpNorm_sq_eq_lintegral_nnnorm_sq]
    refine lintegral_congr_ae ?_
    filter_upwards [stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global T]
      with ω hF
    rw [hF]
  rw [hlim] at hn
  have h_a : Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)) := by
    refine hn.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈T⌉₊] with n hn'
    have hcn : T ≤ (n : ℝ) + 1 := by
      have h1' : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
      have h2' : (⌈T⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      linarith
    rw [MeasureTheory.eLpNorm_congr_ae
        (masterLp_coeFn W ℱ hℱ H h_meas h_progMeas h_sq_int_global n (le_of_lt hT) hcn),
      eLpNorm_sq_eq_lintegral_nnnorm_sq,
      simpleIntegral_intermediate_isometry W ℱ hℱ
        (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
        (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n) (le_of_lt hT)]
  exact tendsto_nhds_unique h_a
    (masterApprox_evalNorm_tendsto ℱ H h_meas h_progMeas h_sq_int_global hT)
include hℱ in
/-- `F t ∈ L²(P)`. -/
lemma stochasticIntegralBrownian_memLp (t : ℝ) :
    MeasureTheory.MemLp (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t) 2 P :=
  (MeasureTheory.Lp.memLp _).ae_eq
    (stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).symm
include hℱ in
/-- `F t =ᵐ 0` for `t ≤ 0`. -/
lemma stochasticIntegralBrownian_ae_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t =ᵐ[P] 0 := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht'
  · subst ht'
    have h := masterApprox_tendsto_L2 W ℱ hℱ H h_meas h_progMeas h_sq_int_global (le_refl (0 : ℝ))
    have hconst : ∀ n, MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) 0 ω
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0 ω) 2 P
        = MeasureTheory.eLpNorm
          (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0) 2 P := by
      intro n
      rw [← MeasureTheory.eLpNorm_neg
        (f := stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0)]
      refine MeasureTheory.eLpNorm_congr_ae ?_
      filter_upwards with ω
      simp [simpleIntegral_eq_zero_of_nonpos W _ (le_refl (0 : ℝ)) ω]
    simp only [hconst] at h
    have hz : MeasureTheory.eLpNorm
        (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0) 2 P = 0 :=
      tendsto_nhds_unique tendsto_const_nhds h
    rwa [MeasureTheory.eLpNorm_eq_zero_iff
      (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global
        0).aestronglyMeasurable
      (by norm_num)] at hz
include hℱ in
/-- `∫⁻‖F t‖² = ∫⁻∫⁻_{[0,t]}‖H‖²` for all `t ≥ 0` (isometry, incl. `t = 0`). -/
lemma stochasticIntegralBrownian_lintegral_sq {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact isometry_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht'
  · subst ht'
    rw [lintegral_congr_ae (by
      filter_upwards [stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global (le_refl (0:ℝ))] with ω hω; rw [hω]; simp : _ =ᵐ[P] fun _ => (0:ℝ≥0∞))]
    rw [MeasureTheory.lintegral_zero]
    symm
    rw [← MeasureTheory.lintegral_zero (μ := P)]
    refine lintegral_congr (fun ω => ?_)
    rw [MeasureTheory.setLIntegral_measure_zero _ _ (by simp)]
include h_meas in
omit [IsProbabilityMeasure P] in
/-- Additivity of the horizon integral: `[0,r] = [0,s] ⊎ (s,r]`. -/
lemma horizon_lintegral_add {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ u in Set.Ioc s r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hinner : ∀ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume
        + ∫⁻ u in Set.Ioc s r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    rw [← Set.Icc_union_Ioc_eq_Icc hs hsr,
        MeasureTheory.lintegral_union measurableSet_Ioc
          (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))]
  rw [MeasureTheory.lintegral_congr hinner]
  exact MeasureTheory.lintegral_add_left'
    ((Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) s))
      (((h_meas.nnnorm).coe_nnreal_ennreal).pow_const 2)).aemeasurable) _
include h_meas h_sq_int_global in
/-- Right-continuity of the horizon integral `r ↦ ∫⁻∫⁻_{[0,r]}‖H‖²` at `s ≥ 0`. -/
lemma horizon_lintegral_right_tendsto {s : ℝ} (hs : 0 ≤ s) :
    Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r,
        (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      (nhdsWithin s (Set.Ioi s))
      (nhds (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
  have hz : Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Ioc s r,
        (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) (nhdsWithin s (Set.Ioi s)) (nhds 0) :=
    tendsto_setLIntegral_Ioc_prod_zero (fun ω u => (‖H ω u‖₊ : ℝ≥0∞) ^ 2)
      ((h_meas.nnnorm.coe_nnreal_ennreal).pow_const 2) hs (lt_add_one s)
      (h_sq_int_global (s + 1) (by linarith)).ne
  have ht := (tendsto_const_nhds (x := ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s,
    (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)).add hz
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (horizon_lintegral_add H h_meas hs (le_of_lt hr)).symm
include hℱ in
/-- **Right-`L²`-continuity of the Itô integral process.** `‖F r − F s‖_{L²} → 0` as
`r ↓ s`. The squared increment `∫⁻‖F r − F s‖²` equals `ofReal((∫⁻∫⁻_{[0,r]}).toReal −
(∫⁻∫⁻_{[0,s]}).toReal)` (orthogonality + isometry) and `→ 0` by horizon
right-continuity. -/
lemma stochasticIntegralBrownian_eLpNorm_two_right_tendsto (s : ℝ) :
    Filter.Tendsto (fun r => MeasureTheory.eLpNorm
        (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global s) 2 P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
  suffices hsq : Filter.Tendsto (fun r => ∫⁻ ω,
      (‖(stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r
        - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global s) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) by
    have h2 := hsq.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr (fun r => ?_)
    rw [← eLpNorm_sq_eq_lintegral_nnnorm_sq, ← ENNReal.rpow_mul,
      show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  -- the squared increment
  rcases le_or_gt 0 s with hs | hs
  · -- s ≥ 0: orthogonality + isometry + horizon continuity
    have hFsq : ∀ {t : ℝ}, 0 ≤ t →
        ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2 ∂P
          = (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) t, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
      intro t ht
      have hb := lintegral_nnnorm_sq_eq_ofReal_integral
        (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t)
      rw [stochasticIntegralBrownian_lintegral_sq W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global ht] at hb
      rw [hb, ENNReal.toReal_ofReal (integral_nonneg (fun ω => sq_nonneg _))]
    have hincr : ∀ {r : ℝ}, s ≤ r →
        ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r ω
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          = ENNReal.ofReal
            ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
              - (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal) := by
      intro r hsr
      rw [lintegral_nnnorm_sq_eq_ofReal_integral
        (g := fun ω => stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r ω
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global s ω)
        ((stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global r).sub
          (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s))]
      congr 1
      rw [integral_sq_increment_eq_of_martingale
        (martingale_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
        (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s)
        (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global r) hsr,
        hFsq (le_trans hs hsr), hFsq hs]
    -- the toReal-difference → 0
    have hcont : Filter.Tendsto (fun r =>
        ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
          - (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal))
        (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
      have hfin_s : ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ :=
        ne_top_of_le_ne_top (h_sq_int_global (s + 1) (by linarith)).ne
          (MeasureTheory.lintegral_mono (fun ω =>
            lintegral_mono_set (Set.Icc_subset_Icc_right (by linarith))))
      have h0 := (ENNReal.tendsto_toReal hfin_s).comp
        (horizon_lintegral_right_tendsto H h_meas h_sq_int_global hs)
      have h1 := h0.sub_const
        ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
      rw [sub_self] at h1
      exact h1
    have hof := (ENNReal.continuous_ofReal.tendsto 0).comp hcont
    rw [ENNReal.ofReal_zero] at hof
    refine hof.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hincr (le_of_lt hr)).symm
  · -- s < 0: eventually zero
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    symm
    rw [← MeasureTheory.lintegral_zero (μ := P)]
    refine lintegral_congr_ae ?_
    filter_upwards [stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global hr.2,
      stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas h_sq_int_global hs]
      with ω hr0 hs0
    simp [hr0, hs0]
include hℱ in
/-- **Conjunct 1 on `rightCont`: `F` is a martingale wrt `ℱ.rightCont`.**
Right-`L²`-continuity of the slices (`stochasticIntegralBrownian_eLpNorm_two_right_tendsto`)
feeds `martingale_rightCont_of_tendsto_eLpNorm_one`. -/
lemma martingale_rightCont_stochasticIntegralBrownian :
    MeasureTheory.Martingale (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
      ℱ.rightCont P := by
  refine LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one
    (martingale_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global) (fun s => ?_)
  have hF_aesm : ∀ t, MeasureTheory.AEStronglyMeasurable
      (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) P :=
    fun t => (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t).aestronglyMeasurable
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (stochasticIntegralBrownian_eLpNorm_two_right_tendsto W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global s)
    (Filter.Eventually.of_forall (fun r => bot_le))
    (Filter.Eventually.of_forall (fun r => MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num) ((hF_aesm r).sub (hF_aesm s))))
include h_meas h_sq_int_global in
omit [IsProbabilityMeasure P] in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is finite in `L²(P ⊗ vol|_{[0,t]})`,
i.e. `(ω, u) ↦ H ω u` is square-integrable over the product. -/
lemma compensatorH_memLp_prod {t : ℝ} (ht : 0 < t) :
    MeasureTheory.MemLp (fun p : Ω × ℝ => H p.1 p.2) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤),
    show (2 : ℝ≥0∞).toReal = 2 from by simp]
  have hbridge : ∫⁻ p : Ω × ℝ, (‖H p.1 p.2‖ₑ) ^ (2 : ℝ)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    rw [MeasureTheory.lintegral_prod _
      ((((h_meas.nnnorm).coe_nnreal_ennreal).pow_const 2).aemeasurable.congr
        (Filter.Eventually.of_forall (fun p => by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl)))]
    refine lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
  rw [hbridge]; exact h_sq_int_global t ht
end MasterSequence
end Ito
end Brownian
end LevyStochCalc


