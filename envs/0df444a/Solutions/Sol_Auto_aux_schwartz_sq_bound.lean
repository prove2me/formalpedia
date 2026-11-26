-- Prove2me | solution 1 for Auto.aux_schwartz_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:46.76148+00:00
-- url     : https://prove2.me/submissions/c3532e57-6da9-4ba1-95b4-13f885fcfded

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {ι X F : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X]
    [SecondCountableTopologyEither X ℂ]
    {μ : Measure X} [μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ι → ℝ≥0∞) [∀ i, Fact (1 ≤ p i)]
    (hpfin : ∀ i, p i ≠ ∞)
    (B : ContinuousMultilinearMap ℂ (fun i ↦ Lp ℂ (p i) μ) F)
    (K : ℝ)
    (hcore : ∀ f : ι → SchwartzMap X ℂ,
      ‖B.toMultilinearMap (fun i ↦ (f i).toLp (p i) μ)‖ ^ 2 ≤
        K * ∏ i, ‖(f i).toLp (p i) μ‖ ^ 2) :
    ∀ g : (i : ι) → Lp ℂ (p i) μ,
      ‖B.toMultilinearMap g‖ ^ 2 ≤ K * ∏ i, ‖g i‖ ^ 2 := by
  let BR : ContinuousMultilinearMap ℝ (fun i ↦ Lp ℂ (p i) μ) F :=
    B.restrictScalars ℝ
  have hdense (i : ι) : DenseRange (SchwartzMap.toLpCLM ℝ ℂ (p i) μ) :=
    SchwartzMap.denseRange_toLpCLM (E := X) (F := ℂ) (μ := μ)
      (p := p i) (hpfin i)
  let P : ((i : ι) → Lp ℂ (p i) μ) → Prop :=
    fun g ↦ ‖BR g‖ ^ 2 ≤ K * ∏ i, ‖g i‖ ^ 2
  have hleft : Continuous fun g : (i : ι) → Lp ℂ (p i) μ ↦ ‖BR g‖ ^ 2 :=
    BR.cont.norm.pow 2
  have hprod : Continuous fun g : (i : ι) → Lp ℂ (p i) μ ↦ ∏ i, ‖g i‖ ^ 2 := by
    apply continuous_finsetProd Finset.univ
    intro i _
    exact (continuous_norm.comp (continuous_apply i)).pow 2
  have hclosed : IsClosed {g : (i : ι) → Lp ℂ (p i) μ | P g} := by
    exact isClosed_le hleft (continuous_const.mul hprod)
  intro g
  change P g
  refine (DenseRange.piMap hdense).induction_on g hclosed ?_
  intro f
  change ‖B.toMultilinearMap (fun i ↦ (f i).toLp (p i) μ)‖ ^ 2 ≤ _
  exact hcore f
end Auto
