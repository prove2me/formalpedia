-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FellerCoordinateProductContinuityV6
-- name    : MarkovProcess_V3HRepair_FellerCoordinateProductContinuityV6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:41:52.227692+00:00
-- url     : https://prove2.me/theorems/b678a02f-5ac8-4ec4-8c69-3122c0b02347
-- title:
--   Verified MarkovProcess source repair: FellerCoordinateProductContinuity V6
-- statement:
--   Continuity of finite-time kernel integrals of coordinate-product test functions under the Feller semigroup hypothesis. Uses the already published V3H backward-recursion integral identity and directly proves time continuity of the recursion.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FellerCoordinateProductContinuity SHA-256 8749db264f29038d8c6ba804497326421bd6e8ba7806ba166a699d615afcf380. Only repaired import paths were translated to the published Definitions.Def_MarkovProcess_V3HRepair_* module names. V5 reuses the V3H-published kernel integral alias p2m_embedded_2a9d6bc61fa8399e and adapts an accepted time-continuity proof from platform evidence SHA-256 00f4a844fdc3f6f29dae2ae8e693810cf14942abdad1fd2dc2c8b9f0552fe360; the mathematical conclusion is unchanged. V6 adds the accepted strongly-continuous semigroup joint-limit argument (platform proof evidence SHA-256 7a6e085df4df95bfc39a71b08b469159bb5d5c24a897882d1b2223bcb0b8b1cd) within the same V3H environment.

import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_FiniteTime_CoordinateProductActiveReduction_0fcd6a29
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_MarkovProcess_V3HRepair_FiniteTimeKernelRestrict

open Filter Topology
namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The contraction bound for each operator of the semigroup. -/
theorem norm_operator_le_one_repair
    (S : StronglyContinuousContractionSemigroup E) (t : NNReal) :
    ‖S t‖ ≤ 1 := S.opNorm_le_one t

/-- Pointwise distances contract under a semigroup operator. -/
theorem dist_apply_le_repair
    (S : StronglyContinuousContractionSemigroup E) (t : NNReal) (x y : E) :
    dist (S t x) (S t y) ≤ dist x y := by
  calc
    dist (S t x) (S t y) ≤ ‖S t‖ * dist x y := (S t).dist_le_opNorm x y
    _ ≤ 1 * dist x y :=
      mul_le_mul_of_nonneg_right (S.norm_operator_le_one_repair t) dist_nonneg
    _ = dist x y := one_mul _

/-- Continuous time-orbits follow directly from strong continuity. -/
theorem continuous_repair
    (S : StronglyContinuousContractionSemigroup E) (x : E) :
    Continuous (fun t ↦ S t x) := S.continuous_orbit x

/-- Joint continuity of a contraction semigroup in time and the input. -/
theorem tendsto_apply_of_tendsto_repair
    (S : StronglyContinuousContractionSemigroup E) {X : Type*} {l : Filter X}
    {t : X → NNReal} {t₀ : NNReal} {f : X → E} {f₀ : E}
    (ht : Tendsto t l (nhds t₀)) (hf : Tendsto f l (nhds f₀)) :
    Tendsto (fun x ↦ S (t x) (f x)) l (nhds (S t₀ f₀)) := by
  rw [Metric.tendsto_nhds] at hf ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have htime : ∀ᶠ x in l, dist (S (t x) f₀) (S t₀ f₀) < ε / 2 :=
    ((S.continuous_repair f₀).tendsto t₀ |>.comp ht) (Metric.ball_mem_nhds _ hhalf)
  filter_upwards [hf (ε / 2) hhalf, htime] with x hx htx
  calc
    dist (S (t x) (f x)) (S t₀ f₀)
        ≤ dist (S (t x) (f x)) (S (t x) f₀) +
            dist (S (t x) f₀) (S t₀ f₀) := dist_triangle _ _ _
    _ ≤ dist (f x) f₀ + dist (S (t x) f₀) (S t₀ f₀) :=
      by
        simpa only [add_comm] using
          add_le_add_right (S.dist_apply_le_repair (t x) (f x) f₀)
            (dist (S (t x) f₀) (S t₀ f₀))
    _ < ε / 2 + ε / 2 := add_lt_add hx htx
    _ = ε := add_halves ε

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators
namespace MarkovProcess.SubMarkovKernelSemigroup
variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

open IsFellerKernelSemigroup
theorem IsFellerKernelSemigroup.tendsto_backwardC0_repair
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes (n + 1)}
    {times0 : FiniteOrderedTimes (n + 1)}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    Tendsto (fun a ↦ hP.backwardC0 (times a) factors) l
      (nhds (hP.backwardC0 times0 factors)) := by
  induction n with
  | zero =>
      simp only [backwardC0_zero]
      exact hP.c0Semigroup.tendsto_apply_of_tendsto_repair (ht 0) tendsto_const_nhds
  | succ n ih =>
      have htail : ∀ i, Tendsto (fun a ↦ (times a).relativeTail i) l
          (nhds (times0.relativeTail i)) := by
        intro i
        simpa only [FiniteOrderedTimes.relativeTail_apply] using
          (ht i.succ).sub (ht 0)
      have hinner := ih htail (Fin.tail factors)
      simp only [backwardC0_succ]
      exact hP.c0Semigroup.tendsto_apply_of_tendsto_repair (ht 0)
        (tendsto_const_nhds.mul hinner)

/-- The finite-time integral of a coordinate-product term varies continuously when every
ordered time coordinate varies continuously. -/
theorem IsFellerKernelSemigroup.tendsto_integral_coordinateProductTerm_finiteTimeKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes n} {times0 : FiniteOrderedTimes n}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha) (x : alpha) :
    Tendsto (fun a ↦ ∫ path, term.toContinuousMap path ∂finiteTimeKernel P (times a) x) l
      (nhds (∫ path, term.toContinuousMap path ∂finiteTimeKernel P times0 x)) := by
  let A := PiContinuousMap.activeCoordinates term.factors
  by_cases hA : A.card = 0
  · have hActive : PiContinuousMap.activeCoordinates term.factors = ∅ := by
      exact Finset.card_eq_zero.mp hA
    have hTerm (path : Fin n → alpha) :
        term.toContinuousMap path = term.coefficient := by
      rw [PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply_active]
      simp only [PiContinuousMap.CoordinateProductTerm.activeEvaluation, hActive,
        Finset.card_empty, Finset.prod_fin_eq_prod_range, Finset.prod_range_zero, mul_one]
    have hIntegral (u : FiniteOrderedTimes n) :
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel P u x = term.coefficient := by
      let : IsProbabilityMeasure (finiteTimeKernel P u x) :=
        hP.isProbabilityMeasure_finiteTimeLaw P u x
      rw [integral_congr_ae (ae_of_all _ hTerm)]
      simp only [integral_const, probReal_univ, one_smul]
    simp_rw [hIntegral]
    exact tendsto_const_nhds
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hA
    let e := PiContinuousMap.activeOrderEmbedding term.factors
    let ec : Fin (k + 1) ↪o Fin n :=
      (Fin.castOrderIso hk.symm).toOrderEmbedding.trans e
    let factors : Fin (k + 1) → C₀(alpha, ℝ) := fun j ↦
      PiContinuousMap.activeNormalizedFactor term.factors (Fin.cast hk.symm j)
    have htimes : ∀ i, Tendsto (fun a ↦ (times a).restrict ec i) l
        (nhds (times0.restrict ec i)) := by
      intro i
      exact ht (ec i)
    have hIntegral (u : FiniteOrderedTimes n) :
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel P u x =
          term.coefficient * hFeller.backwardC0
            (u.restrict ec) factors x := by
      let g : (Fin (k + 1) → alpha) → ℝ :=
        fun path ↦ ∏ i, factors i (path i)
      have hg : StronglyMeasurable g := by
        exact Finset.stronglyMeasurable_fun_prod Finset.univ fun i _ ↦
          ((factors i).measurable.comp (measurable_pi_apply i)).stronglyMeasurable
      have hpoint : ∀ path : Fin n → alpha,
          term.toContinuousMap path =
            term.coefficient * g (FiniteOrderedTimes.restrictPath ec path) := by
        intro path
        rw [PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply_active]
        simp only [PiContinuousMap.CoordinateProductTerm.activeEvaluation, g,
          factors, FiniteOrderedTimes.restrictPath, ec, e,
          RelEmbedding.coe_trans, Function.comp_apply,
          OrderIso.coe_toOrderEmbedding]
        congr 1
        exact ((Fin.castOrderIso hk.symm).toEquiv.prod_comp
          (fun j ↦ PiContinuousMap.activeNormalizedFactor term.factors j
            (path (PiContinuousMap.activeOrderEmbedding term.factors j)))).symm
      calc
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel P u x =
            ∫ path, term.coefficient *
              g (FiniteOrderedTimes.restrictPath ec path) ∂finiteTimeKernel P u x := by
              apply integral_congr_ae
              exact ae_of_all _ hpoint
        _ = term.coefficient * ∫ path,
              g (FiniteOrderedTimes.restrictPath ec path) ∂finiteTimeKernel P u x := by
              rw [integral_const_mul]
        _ = term.coefficient * ∫ path, g path ∂
              (finiteTimeKernel P u).map (FiniteOrderedTimes.restrictPath ec) x := by
              rw [Kernel.map_apply _ (FiniteOrderedTimes.measurable_restrictPath ec)]
              rw [integral_map
                (FiniteOrderedTimes.measurable_restrictPath ec).aemeasurable
                hg.aestronglyMeasurable]
        _ = term.coefficient * ∫ path, g path ∂
              finiteTimeKernel P (u.restrict ec) x := by
              rw [hP.finiteTimeKernel_map_restrictPath P u ec]
        _ = term.coefficient * hFeller.backwardC0 (u.restrict ec) factors x := by
              rw [hFeller.p2m_embedded_2a9d6bc61fa8399e]
    simp_rw [hIntegral]
    apply tendsto_const_nhds.mul
    have hb := hFeller.tendsto_backwardC0_repair htimes factors
    have heval : Continuous fun f : C₀(alpha, ℝ) ↦ f x :=
      (ZeroAtInftyContinuousMap.isometry_toBCF (α := alpha) (β := ℝ)).continuous.eval
        continuous_const
    exact heval.continuousAt.tendsto.comp hb

end MarkovProcess.SubMarkovKernelSemigroup


