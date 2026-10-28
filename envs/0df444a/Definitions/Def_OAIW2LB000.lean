-- Prove2me | Definitions.Def_OAIW2LB000
-- name    : OAIW2LB000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T05:12:30.514879+00:00
-- url     : https://prove2.me/theorems/ca54ff90-d052-40e2-9cf2-3dcfee2eb696
-- title:
--   Definitions bundle OAIW2LB000 of the split of OpenAI, The logarithmic Brunn–Minkowski conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LogBrunnMinkowski.main`, carved from OpenAI's openai/math development (OpenAI, *The logarithmic Brunn–Minkowski conjecture*, OpenAI Math Release, September 23, 2026, result family 91, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 399 declarations of OpenAI's Lean: 334 definitions, 4 inductive types or structures, 2 instances and 59 theorems. The definitions and types are `OAI.ABPGeometry.boundedContact`, `OAI.ABPGeometry.hessianMatrix`, `OAI.ABPGeometry.upperContact`, `OAI.AffineDistribution.dilate`, `OAI.AffineDistribution.homothety`, `OAI.AffineDistribution.jac`, `OAI.AffineDistribution.physicalCutoff`, `OAI.AffineDistribution.scaleWeight`, `OAI.AffineDistribution.transform`, `OAI.AffineDistribution.translate`, `OAI.AnnularFourier.annulus`, `OAI.AnnularFourier.conv`, `OAI.AnnularFourier.elliptic`, `OAI.AnnularFourier.lowBump`, `OAI.AnnularFourier.lowFilter`, `OAI.AnnularFourier.lowKernel`, `OAI.AnnularFourier.lowSymbol`, `OAI.AnnularFourier.normalized`, `OAI.AnnularFourier.product`, `OAI.AnnularSymbol.bump`, `OAI.AnnularSymbol.cutoff`, `OAI.AnnularSymbol.kernel`, `OAI.AnnularSymbol.multiplier`, `OAI.AnnularSymbol.symbol`, `OAI.C11Compactness.normalizedLipschitz`, `OAI.CoefficientTrace.bilinear`, `OAI.CoefficientTrace.instNormedAddCommGroupContinuousLinearMapRealId_solutions`, `OAI.CoefficientTrace.instNormedSpaceRealContinuousLinearMapId_solutions`, `OAI.CoefficientTrace.instNormedSpaceRealContinuousLinearMapId_solutions_1`, `OAI.CoefficientTrace.trace`, `OAI.CompactMollification.dd`, `OAI.CompactMollification.elliptic`, `OAI.CompactMollification.mollifier`, `OAI.CompactMomentVariational.Admissible`, `OAI.CompactMomentVariational.NormalizedConvex`, `OAI.CompactMomentVariational.SupportingSlope`, `OAI.CompactMomentVariational.chosenSlope`, `OAI.CompactMomentVariational.coercivityConstant`, `OAI.CompactMomentVariational.conjugate`, `OAI.CompactMomentVariational.dualOn` and 298 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`LogVolume_BrunnMinkowski`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean).
--
--   **Imports.** It imports the published bundle `Def_LogBrunnMinkowski`.
--
--   **Imported by** (directly, in this split): the statements `OAI.C11InteriorRegularity.continuous_hessian_rep`, `OAI.C11InteriorRegularity.holder_hessian`, `OAI.CompactMomentVariational.exists_C11_truncated`, `OAI.LogBrunnMinkowski.softVariance`, `OAI.MomentKernel.weak_kernel_smooth`, `OAI.MomentQuotient.C3_local`, `OAI.MomentSchauder.smooth_of_regular_three`, `OAI.MomentSlab.range_dual_bound` and `OAI.MomentSlab.variance_from_moment`; the proofs of `OAI.C11InteriorRegularity.continuous_hessian_rep`, `OAI.C11InteriorRegularity.holder_hessian`, `OAI.CompactMomentVariational.exists_C11_truncated`, `OAI.LogBrunnMinkowski.main`, `OAI.LogBrunnMinkowski.softVariance`, `OAI.MomentKernel.weak_kernel_smooth`, `OAI.MomentQuotient.C3_local`, `OAI.MomentSchauder.smooth_of_regular_three`, `OAI.MomentSlab.range_dual_bound` and `OAI.MomentSlab.variance_from_moment`.
-- source:
--   OpenAI, The logarithmic Brunn–Minkowski conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 91; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_LogBrunnMinkowski

section
-- module Solutions.OAIW2_LogBM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_LogBM.LogVolume_BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology NNReal

namespace CompactMomentVariational
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def conjugate (K : Set E) (u : E → ℝ) (z : E) : ℝ :=
  sSup ((fun x => ⟪x,z⟫_ℝ-u x) '' K)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def functional (ν : Measure E) (K : Set E) (u : E → ℝ) : ℝ :=
  Real.log (∫ z, Real.exp (-conjugate K u z) ∂μ) - ∫ x, u x ∂ν

def coercivityConstant (r d : ℝ) : ℝ :=
  let C := d*μ.real (Metric.closedBall (0:E) r)
  let N : ℝ := Module.finrank ℝ E
  1-N*Real.log r + Real.log (∫ z : E, Real.exp (-‖z‖) ∂μ) +
    C/2+N*Real.log (2*(N+1)/C)


end
end CompactMomentVariational

open Set Filter
open scoped Topology NNReal

noncomputable section
namespace MomentCompactness
variable {E : Type*} [NormedAddCommGroup E]

def normalizedLipschitz (R : ℝ≥0) : Set C(E,ℝ) :=
  {f | LipschitzWith R f ∧ f 0=0}

end MomentCompactness

namespace CompactMomentVariational
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

structure Admissible (ν : Measure E) (R : ℝ) (u : E → ℝ) : Prop where
  convex : ConvexOn ℝ (Metric.ball (0:E) R) u
  nonneg : ∀ x, 0 ≤ u x
  zero : u 0=0
  even : Function.Even u
  outside : ∀ x, x ∉ Metric.ball (0:E) R → u x=0
  integrable : Integrable u ν

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

structure NormalizedConvex (R : ℝ≥0) (φ : E → ℝ) : Prop where
  lipschitz : LipschitzWith R φ
  zero : φ 0=0
  nonneg : ∀ x, 0 ≤ φ x
  even : Function.Even φ
  convex : ConvexOn ℝ univ φ

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def dualOn (K : Set E) (φ : E → ℝ) : E → ℝ := K.indicator (conjugate univ φ)

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]


def valueSet (ν : Measure E) (R : ℝ) : Set ℝ :=
  {a | ∃ u, Admissible ν R u ∧ functional μ ν (Metric.ball (0:E) R) u=a}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable (μ : Measure E) [μ.IsAddHaarMeasure]

def normalizedSource (φ : E → ℝ) : Measure E :=
  μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)/(∫ y,Real.exp (-φ y) ∂μ)))

end CompactMomentVariational
end

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace TruncatedMoment
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

def partition (R : ℝ) (V : E → ℝ) : ℝ :=
  ∫ x in Metric.ball (0:E) R, Real.exp (-V x) ∂μ

def target (R : ℝ) (V : E → ℝ) : Measure E :=
  (μ.restrict (Metric.ball (0:E) R)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-V x) / partition μ R V))

end TruncatedMoment

end

open scoped ENNReal

noncomputable section
namespace CompactMomentVariational
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma convex_supporting_gradient {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {z : E}
    (hd : DifferentiableAt ℝ φ z) (w : E) :
    φ z + ⟪gradient φ z,w-z⟫_ℝ ≤ φ w := by
  let l : ℝ →ᵃ[ℝ] E := AffineMap.lineMap z w
  have hconv : ConvexOn ℝ univ (φ ∘ l) := by
    simpa only [Set.preimage_univ] using hc.comp_affineMap l
  have hder : HasDerivAt (φ ∘ l) ((fderiv ℝ φ z) (w-z)) 0 := by
    have hh : HasFDerivAt φ (fderiv ℝ φ z) (l (0:ℝ)) := by
      simpa only [l, AffineMap.lineMap_apply_zero] using hd.hasFDerivAt
    exact hh.comp_hasDerivAt (0:ℝ) (AffineMap.hasDerivAt_lineMap (a:=z) (b:=w) (x:=0))
  have hh := hconv.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num : (0:ℝ)<1) hder
  simp only [slope,sub_zero,one_smul,Function.comp_apply,l,AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_zero,inv_one,vsub_eq_sub] at hh
  rw [← toDual_gradient,InnerProductSpace.toDual_apply_apply] at hh
  linarith

end

end CompactMomentVariational
end

open scoped InnerProductSpace ContDiff Topology
noncomputable section
namespace CompactMomentVariational
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def SupportingSlope (φ : E → ℝ) (z p : E) : Prop :=
  ∀ w, φ z+⟪p,w-z⟫_ℝ ≤ φ w

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def proximalEnergy (φ : E → ℝ) (y z : E) : ℝ := φ z+(1/2)*‖z-y‖^2

lemma proximal_exists {φ : E → ℝ} {L : ℝ≥0} (hl : LipschitzWith L φ) (y : E) :
    ∃ z, ∀ w, proximalEnergy φ y z ≤ proximalEnergy φ y w := by
  have hc : Continuous (proximalEnergy φ y) :=
    hl.continuous.add (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))
  apply hc.exists_forall_le
  have hh (z : E) : (1/4)*‖z‖^2+φ 0-((L:ℝ)+‖y‖)^2 ≤ proximalEnergy φ y z := by
    have h := hl.dist_le_mul z 0
    rw [Real.dist_eq,dist_zero_right] at h
    have he : φ 0-φ z ≤ |φ z-φ 0| := by simpa only [neg_sub] using neg_le_abs (φ z-φ 0)
    have hi := real_inner_le_norm z y
    dsimp only [proximalEnergy]
    rw [norm_sub_sq_real]
    nlinarith [sq_nonneg (‖z‖/2-((L:ℝ)+‖y‖)),sq_nonneg ‖y‖]
  apply tendsto_atTop_mono hh
  have hp := (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp
    (tendsto_norm_cocompact_atTop (E:=E))
  have ht := Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<1/4) hp
  convert tendsto_atTop_add_const_right (cocompact E) (φ 0-((L:ℝ)+‖y‖)^2) ht using 1
  ext x
  simp only [Function.comp_apply]
  ring

def proximal {φ : E → ℝ} {L : ℝ≥0} (hl : LipschitzWith L φ) (y : E) : E :=
  Classical.choose (proximal_exists hl y)

lemma norm_gradient_le_lipschitz {φ : E → ℝ} {L : ℝ≥0} (hl : LipschitzWith L φ) (x : E) :
    ‖gradient φ x‖ ≤ (L:ℝ) := by
  rw [gradient,(InnerProductSpace.toDual ℝ E).symm.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hl

end CompactMomentVariational
end
open scoped ENNReal
noncomputable section
namespace CompactMomentVariational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma supportingSlope_limit {φ : E → ℝ} (hc : Continuous φ)
    {F : Filter E} [F.NeBot] {x p : E} {P : E → E}
    (hx : Tendsto (id : E → E) F (𝓝 x)) (hp : Tendsto P F (𝓝 p))
    (hs : ∀ᶠ y in F, SupportingSlope φ y (P y)) : SupportingSlope φ x p := by
  intro w
  have ht : Tendsto (fun y => φ y+⟪P y,w-y⟫_ℝ) F (𝓝 (φ x+⟪p,w-x⟫_ℝ)) :=
    ((hc.tendsto x).comp hx).add (hp.inner (tendsto_const_nhds.sub hx))
  exact le_of_tendsto ht (hs.mono (fun _ h => h w))

variable [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

include μ in

lemma exists_supportingSlope {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    {L : ℝ≥0} (hl : LipschitzWith L φ) (x : E) :
    ∃ p, ‖p‖ ≤ (L:ℝ) ∧ SupportingSlope φ x p := by
  let D := {y | DifferentiableAt ℝ φ y}
  have hd : Dense D := Measure.dense_of_ae (hl.ae_differentiableAt (μ:=μ))
  have : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hd x)
  obtain ⟨p,hp,hcluster⟩ := (isCompact_closedBall (0:E) (L:ℝ)).exists_mapClusterPt
    (f:=𝓝[D] x) (u:=gradient φ) (Filter.tendsto_principal.mpr (Eventually.of_forall
      (fun y => by simpa only [Metric.mem_closedBall,dist_zero_right] using norm_gradient_le_lipschitz hl y)))
  refine ⟨p,by simpa only [Metric.mem_closedBall,dist_zero_right] using hp,?_⟩
  let F := Filter.comap (gradient φ) (𝓝 p) ⊓ 𝓝[D] x
  have : F.NeBot := neBot_inf_comap_iff_map'.mpr hcluster
  apply supportingSlope_limit hl.continuous
    (show Tendsto (id : E → E) F (𝓝 x) from inf_le_right.trans nhdsWithin_le_nhds)
    (show Tendsto (gradient φ) F (𝓝 p) from map_le_iff_le_comap.mpr inf_le_left)
  filter_upwards [(show ∀ᶠ y in 𝓝[D] x, y ∈ D from self_mem_nhdsWithin).filter_mono
    (show F ≤ 𝓝[D] x from inf_le_right)] with y hy
  exact convex_supporting_gradient hc hy

def chosenSlope {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {L : ℝ≥0}
    (hl : LipschitzWith L φ) (x : E) : E := Classical.choose (exists_supportingSlope μ hc hl x)

end CompactMomentVariational
end

open Set MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace CompactMomentVariational

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def proximalConjugate {φ : E → ℝ} {L : ℝ≥0} (hl : LipschitzWith L φ) (y : E) : ℝ :=
  ⟪proximal hl y,y⟫_ℝ-φ (proximal hl y)-(1/2)*‖proximal hl y‖^2

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weakHessian (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ}
    (hc : ConvexOn ℝ univ φ) {L : ℝ≥0} (hl : LipschitzWith L φ) (z : E) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (chosenSlope μ hc hl) z).toLinearMap

end

end CompactMomentVariational

namespace WeakMomentBound
open CompactMomentVariational
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def secondDiff (φ : E → ℝ) (h z : E) : ℝ := φ (z+h) + φ (z-h) - 2*φ z

end WeakMomentBound

namespace WeakMomentBound
open CompactMomentVariational
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def shiftedMean (φ : E → ℝ) (h : E) (T : ℝ) (z : E) : ℝ :=
  (φ (z+h)+φ (z-h)-T)/2

def slopeMean (P : E → E) (h z : E) : E := (1/2:ℝ) • (P (z+h)+P (z-h))

end WeakMomentBound
end

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section
namespace UniformMoment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section Ball
variable [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

def ballMoment (y : E) : ℝ := ∫ x in Metric.closedBall (0:E) 1, |⟪x,y⟫_ℝ| ∂μ

end Ball

end UniformMoment

namespace C11Compactness
open Set Filter
open scoped Topology NNReal InnerProductSpace
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [ProperSpace F]

def normalizedLipschitz (R : ℝ≥0) : Set C(E,F) :=
  {f | LipschitzWith R f ∧ f 0=0}

end C11Compactness
end

open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace MomentLimits
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E)

def density (φ : E → ℝ) (x : E) : ℝ := Real.exp (-φ x)
def source (φ : E → ℝ) : Measure E :=
  μ.withDensity (fun x => ENNReal.ofReal (density φ x))

end
end MomentLimits

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section
namespace MomentLinearization
open MeasureTheory Set Filter Matrix CompactMomentVariational
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hessian (b : OrthonormalBasis ι ℝ E) (φ : E → ℝ) (z : E) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient φ) z).toLinearMap

def vectorDiff (X : E → E) (h z : E) : E := X (z+h)+X (z-h)-(2:ℝ) • X z

def matrixDiff (H : E → Matrix ι ι ℝ) (h z : E) : Matrix ι ι ℝ :=
  H (z+h)+H (z-h)-(2:ℝ) • H z

end MomentLinearization

namespace InverseElliptic
open Set Metric Matrix
open scoped InnerProductSpace Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Mat" => Matrix ι ι ℝ

def fromMatrix (b : OrthonormalBasis ι ℝ E) : Mat ≃L[ℝ] E →L[ℝ] E :=
  ((LinearMap.toMatrix b.toBasis b.toBasis).symm.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

end InverseElliptic

namespace RadialBarrier

open Set
open scoped InnerProductSpace Matrix ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def profile (p : ℝ) (x : E) : ℝ := (1+‖x‖^2)^(-p)

end RadialBarrier

namespace ABPGeometry
open Set Filter Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def upperContact (u : E → ℝ) (C : Set E) : Set E :=
  {x | x ∈ interior C ∧ ∀ y ∈ C, u y≤u x+⟪gradient u x,y-x⟫_ℝ}

end ABPGeometry

namespace ABPGeometry
open Set Filter Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

def hessianMatrix (b : OrthonormalBasis ι ℝ E) (u : E → ℝ) (x : E) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient u) x).toLinearMap


def boundedContact (u : E → ℝ) (C : Set E) (r : ℝ) : Set E :=
  upperContact u C ∩ {y | 0<u y} ∩ {y | ‖gradient u y‖≤r}

end ABPGeometry

namespace DyadicBoxes
open Set Metric Filter BoxIntegral
open scoped Topology
variable {ι : Type*} [Fintype ι]

def box (I : Box ι) : List (Set ι) → Box ι
  | [] => I
  | s::p => box (I.splitCenterBox s) p

end DyadicBoxes

namespace CubeGeometry
open Set Metric MeasureTheory BoxIntegral
open scoped Topology ENNReal Pointwise
variable {ι : Type*} [Fintype ι]

def unitBox : Box ι := ⟨fun _ => -(1/2),fun _ => 1/2,by intro i; norm_num⟩
def center (I : Box ι) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => (I.lower i+I.upper i)/2)
def side (p : List (Set ι)) : ℝ := 1/(2:ℝ)^p.length

end CubeGeometry

namespace LaminarCover
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} {I : Type*} [MeasurableSpace X] [Countable I]

def maximal (B : I → Set X) (rank : I → ℕ) (S : Set I) : Set I :=
  {i | i∈S ∧ ∀ j∈S, rank j<rank i → Disjoint (B i) (B j)}

end LaminarCover

namespace SecondDifference
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def scalar (φ : E → ℝ) (h z : E) : ℝ := φ (z+h)+φ (z-h)-2*φ z

def vector (X : E → E) (h z : E) : E := X (z+h)+X (z-h)-(2:ℝ) • X z

end SecondDifference

namespace DeficitQuotient
open Set Matrix
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hessian (b : OrthonormalBasis ι ℝ E) (φ : E → ℝ) (x : E) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient φ) x).toLinearMap

def deficit (φ : E → ℝ) (h : E) (M k : ℝ) (x : E) : ℝ :=
  M-k*SecondDifference.scalar φ h x

end DeficitQuotient

namespace OscillationEnvelope
open Set

def upper {X : Type*} (f : X → ℝ) (K : Set X) : ℝ := sSup (f '' K)
def lower {X : Type*} (f : X → ℝ) (K : Set X) : ℝ := sInf (f '' K)
def span {X : Type*} (f : X → ℝ) (K : Set X) : ℝ := upper f K-lower f K

end OscillationEnvelope

namespace HessianTail
open MeasureTheory Set Filter Metric BoxIntegral OscillationEnvelope
open scoped InnerProductSpace NNReal ENNReal Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "I₀" => (CubeGeometry.unitBox : Box ι)

def cube : Set E := {x | x.ofLp∈I₀}
def direction (φ : E → ℝ) (e : E) (x : E) : ℝ := ⟪fderiv ℝ (gradient φ) x e,e⟫_ℝ

end HessianTail

namespace FiniteElliptic
open Set Metric Matrix
open scoped MatrixOrder Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ

def quadratic (D : Mat) (e : ι → ℝ) : ℝ := e ⬝ᵥ (D *ᵥ e)

end FiniteElliptic

namespace HessianCoordinates
open Matrix
open scoped InnerProductSpace Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vector (b : OrthonormalBasis ι ℝ E) (e : ι → ℝ) : E := b.repr.symm (WithLp.toLp 2 e)

end HessianCoordinates

namespace InteriorOscillation
open Set Filter Metric Matrix MeasureTheory OscillationEnvelope FiniteElliptic
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Mat" => Matrix ι ι ℝ

def oscillation (S : Finset (ι → ℝ)) (H : E → Mat) (U : Set E) : ℝ :=
  ∑ e : {e // e∈S}, span (fun x => quadratic (H x) e.val) U

end InteriorOscillation

namespace MARescale
open Set Filter MeasureTheory Matrix
open scoped InnerProductSpace NNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def potential (φ : E → ℝ) (c : E) (r : ℝ) (x : E) : ℝ := (1/r^2)*φ (c+r • x)

def point (c : E) (r : ℝ) (x : E) : E := c+r • x

end MARescale

end

noncomputable section
namespace OscillationDecay
open Set Filter Metric OscillationEnvelope
open scoped Topology
variable {E : Type*} [MetricSpace E] {ι : Type*} [Fintype ι]

def total (f : ι → E → ℝ) (U : Set E) : ℝ := ∑ i,span (f i) U

end OscillationDecay

end

end

section

open scoped Real
namespace LocalPeetre
noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

def weight (s : ℝ) (x : E) : ℝ := (1+‖x‖^2)^(s/2)

end
end LocalPeetre

open MeasureTheory
open scoped Topology

open MeasureTheory FourierTransform Convolution
open scoped SchwartzMap

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology

noncomputable section
namespace SobolevModel
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev Model (E : Type*) (F : Type*) [NormedAddCommGroup F]
    [MeasureSpace E] : Type _ := Lp F 2 (volume : Measure E)

variable (E F) in
def embedding (s : ℝ) : Model E F →L[ℂ] 𝓢'(E,F) :=
  besselPotential E F (-s) ∘L Lp.toTemperedDistributionCLM F volume 2

variable (E F) in
def schwartzBessel (s : ℝ) : 𝓢(E,F) →L[ℂ] 𝓢(E,F) :=
  SchwartzMap.fourierMultiplierCLM F
    (fun x => Complex.ofReal ((1+‖x‖^2)^(s/2)))

@[simp] lemma schwartzBessel_zero (f : 𝓢(E,F)) : schwartzBessel E F 0 f = f := by
  simp [schwartzBessel]

variable (E F) in
def coordinate (s : ℝ) : 𝓢(E,F) →L[ℂ] Model E F :=
  SchwartzMap.toLpCLM ℂ F 2 volume ∘L schwartzBessel E F s

end SobolevModel

namespace LocalSobolev
section
open MeasureTheory FourierTransform
open scoped SchwartzMap
open LocalPeetre
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def weighted (s : ℝ) : 𝓢(E,F) →L[ℂ] 𝓢(E,F) :=
  SchwartzMap.smulLeftCLM F (fun x => Complex.ofReal (weight s x))

end

open MeasureTheory FourierTransform LocalPeetre
open scoped SchwartzMap

end LocalSobolev

namespace LocalParametrix
open MeasureTheory FourierTransform TemperedDistribution LocalPeetre LocalSobolev
open scoped SchwartzMap BigOperators
variable {E : Type*} {F : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

def coefficientGauge (s : ℝ) (a : 𝓢(E,ℂ)) : ℝ :=
  2^(|s|/2) * ‖(weighted |s| (𝓕 a)).toLp 1‖

@[simp] lemma coefficientGauge_zero (s : ℝ) : coefficientGauge s (0 : 𝓢(E,ℂ)) = 0 := by
  change 2^(|s|/2) * ‖(SchwartzMap.toLpCLM ℂ ℂ 1 volume) (weighted |s| (𝓕 (0 : 𝓢(E,ℂ))))‖ = 0
  change 2^(|s|/2) * ‖(SchwartzMap.toLpCLM ℂ ℂ 1 volume) (weighted |s| ((fourierCLM ℂ (𝓢(E,ℂ))) 0))‖ = 0
  simp only [map_zero, norm_zero, mul_zero]

def perturbation (q : E → ℂ) (p : ι → E → ℂ) (a : ι → 𝓢(E,ℂ)) :
    𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  (TemperedDistribution.fourierMultiplierCLM F q).comp
    (∑ i, (TemperedDistribution.smulLeftCLM F (a i)).comp
      (TemperedDistribution.fourierMultiplierCLM F (p i)))

end LocalParametrix
end

open MeasureTheory TemperedDistribution FourierTransform LineDeriv
open scoped SchwartzMap ContDiff
noncomputable section
namespace LocalDifferential
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def product (a b : 𝓢(E,ℂ)) : 𝓢(E,ℂ) := SchwartzMap.smulLeftCLM ℂ a b

@[simp] lemma product_apply (a b : 𝓢(E,ℂ)) (x : E) : product a b x = a x * b x := by
  exact SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth b x

def derivative : List E → 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)
  | [] => ContinuousLinearMap.id ℂ _
  | v::vs => (lineDerivOpCLM ℂ 𝓢'(E,F) v).comp (derivative vs)

@[simp] theorem derivative_nil (u : 𝓢'(E,F)) : derivative [] u = u := rfl
@[simp] theorem derivative_cons (v : E) (vs : List E) (u : 𝓢'(E,F)) :
    derivative (v::vs) u = ∂_{v} (derivative vs u) := rfl

end LocalDifferential

namespace LocalDifferential
open MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap Real
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def symbol : List E → E → ℂ
  | [] => fun _ => 1
  | v::vs => fun x => symbol vs x * ((2 * Real.pi * Complex.I) * Complex.ofReal (inner ℝ x v))

def symbolConstant : List E → ℝ
  | [] => 1
  | v::vs => symbolConstant vs * (‖(2 * Real.pi * Complex.I : ℂ)‖ * ‖v‖)

end LocalDifferential

namespace LocalSupport
open MeasureTheory TemperedDistribution LineDeriv Filter
open scoped SchwartzMap Topology
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def SupportedIn (u : 𝓢'(E,F)) (K : Set E) : Prop :=
  ∀ φ : 𝓢(E,ℂ), (∀ x ∈ K, (φ : E → ℂ) =ᶠ[𝓝 x] 0) → u φ = 0

end LocalSupport

namespace LocalOperator
open MeasureTheory TemperedDistribution FourierTransform LocalDifferential LocalSupport
open scoped SchwartzMap BigOperators
variable {E : Type*} {F : Type*} {ι : Type*} {κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]

def operator (a : ι → 𝓢(E,ℂ)) (vs : ι → List E) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  ∑ i, (smulLeftCLM F (a i)).comp (derivative (vs i))

def perturbCoefficient (c : ι → ℂ) (η : 𝓢(E,ℂ)) (a : ι → 𝓢(E,ℂ)) (i : ι) : 𝓢(E,ℂ) :=
  c i • η - a i

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def frozenSymbol (c : ι → ℂ) (vs : ι → List E) : E → ℂ :=
  (fun _ => 1) + (fun x => ∑ i, (c i • symbol (vs i)) x)

end LocalOperator
end

open Filter Function
open scoped SchwartzMap Topology ContDiff
noncomputable section
namespace LocalSchwartz

variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [NormedSpace ℂ F]

def frozenDifference (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ)
    (v : E → ℂ) (hv : ContDiff ℝ ∞ v) (x₀ : E) (r : ℝ) : 𝓢(E,ℂ) :=
  (hχ.mul_right (f':=fun x => v (x₀+r • x)-v x₀)).toSchwartzMap
    (χ.smooth'.mul ((hv.comp (contDiff_const.add (contDiff_id.const_smul r))).sub contDiff_const))

end LocalSchwartz

namespace LocalOperator
open MeasureTheory TemperedDistribution Filter LocalDifferential LocalSchwartz
open scoped SchwartzMap Topology ContDiff
variable {E : Type*} {F : Type*} {ι : Type*} {κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [Fintype ι] [Fintype κ]

def frozenCoefficient (η : 𝓢(E,ℂ)) (hη : HasCompactSupport η)
    (a : E → ℂ) (ha : ContDiff ℝ ∞ a) (x₀ : E) (r : ℝ) : 𝓢(E,ℂ) :=
  a x₀ • η + frozenDifference η hη a ha x₀ r

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma frozenCoefficient_apply (η : 𝓢(E,ℂ)) (hη : HasCompactSupport η)
    (a : E → ℂ) (ha : ContDiff ℝ ∞ a) (x₀ : E) (r : ℝ) (x : E) :
    frozenCoefficient η hη a ha x₀ r x = η x * a (x₀+r • x) := by
  change a x₀ * η x + η x * (a (x₀+r • x)-a x₀) = _
  ring

end LocalOperator

namespace AffineDistribution
section
open MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap Real Topology ENNReal
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def homothety (r : ℝ) (hr : r ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)

@[simp] lemma homothety_apply (r : ℝ) (hr : r ≠ 0) (x : E) :
    homothety (E:=E) r hr x = r • x := rfl

def translate (a : E) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.compSubConstCLM ℂ a)

@[simp] lemma translate_apply (a : E) (u : 𝓢'(E,F)) (φ : 𝓢(E,ℂ)) :
    translate a u φ = u (SchwartzMap.compSubConstCLM ℂ a φ) := rfl

def jac (r : ℝ) : ℝ := |(r ^ Module.finrank ℝ E)⁻¹|

def dilate (r : ℝ) (hr : r ≠ 0) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  (Complex.ofReal (jac (E:=E) r)) •
    PointwiseConvergenceCLM.precomp F
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (homothety (E:=E) r hr).symm)

@[simp] lemma dilate_apply (r : ℝ) (hr : r ≠ 0) (u : 𝓢'(E,F)) (φ : 𝓢(E,ℂ)) :
    dilate r hr u φ = (Complex.ofReal (jac (E:=E) r)) •
      u (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (homothety (E:=E) r hr).symm φ) := rfl

@[simp] lemma homothety_symm_apply (r : ℝ) (hr : r ≠ 0) (x : E) :
    (homothety (E:=E) r hr).symm x = r⁻¹ • x := rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
lemma memLp_dilate {p : ℝ≥0∞} {f : E → F} (hf : MemLp f p volume)
    (r : ℝ) (hr : r ≠ 0) : MemLp (fun x => f (r • x)) p volume := by
  have hh := hf.smul_measure (ENNReal.ofReal_ne_top (r:=jac (E:=E) r))
  change MemLp f p (ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| • volume) at hh
  rw [←Measure.map_addHaar_smul (E:=E) volume hr] at hh
  exact hh.comp_of_map (by fun_prop)

def scaleWeight (s r : ℝ) (x : E) : ℂ :=
  Complex.ofReal ((1+‖r • x‖^2)^(s/2) * (1+‖x‖^2)^(-s/2))

end

open MeasureTheory TemperedDistribution LineDeriv LocalDifferential
open scoped SchwartzMap
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

@[simp] lemma translate_translate (a b : E) (u : 𝓢'(E,F)) :
    translate a (translate b u) = translate (a+b) u := by
  ext φ
  simp only [translate_apply]
  congr 1
  ext x
  simp

@[simp] lemma translate_zero (u : 𝓢'(E,F)) : translate 0 u = u := by
  ext φ
  simp only [translate_apply]
  congr 1
  ext x
  simp

end AffineDistribution

namespace TranslationSobolev
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def translate (a : E) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.compSubConstCLM ℂ a)

def weighted (s : ℝ) : 𝓢(E,F) →L[ℂ] 𝓢(E,F) :=
  SchwartzMap.smulLeftCLM F (fun x => Complex.ofReal ((1+‖x‖^2)^(s/2)))

end TranslationSobolev

namespace AffineDistribution
section
open MeasureTheory TemperedDistribution LineDeriv LocalDifferential
open scoped SchwartzMap
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def transform (x₀ : E) (r : ℝ) (hr : r ≠ 0) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  (dilate r hr).comp (translate x₀)

def physicalCutoff (x₀ : E) (r : ℝ) (hr : r ≠ 0) (χ : 𝓢(E,ℂ)) : 𝓢(E,ℂ) :=
  SchwartzMap.compSubConstCLM ℂ x₀
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (homothety r hr).symm χ)

@[simp] lemma physicalCutoff_apply (x₀ : E) (r : ℝ) (hr : r ≠ 0) (χ : 𝓢(E,ℂ)) (x : E) :
    physicalCutoff x₀ r hr χ x = χ (r⁻¹ • (x-x₀)) := rfl

end

open MeasureTheory TemperedDistribution LocalDifferential LocalOperator
open scoped SchwartzMap

end AffineDistribution

namespace SobolevGerms
open MeasureTheory TemperedDistribution LocalDifferential
open scoped SchwartzMap Topology
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def At (s : ℝ) (u : 𝓢'(E,F)) (x : E) : Prop :=
  ∃ χ : 𝓢(E,ℂ), (χ : E → ℂ) =ᶠ[𝓝 x] 1 ∧ MemSobolev s 2 (smulLeftCLM F χ u)

def aggregate : List (𝓢(E,ℂ)) → 𝓢(E,ℂ)
  | [] => 0
  | a::as => a + aggregate as - product a (aggregate as)

end SobolevGerms

namespace LocalBumps
open MeasureTheory Filter Metric
open scoped SchwartzMap Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def complexBump (f : ContDiffBump (0:E)) : 𝓢(E,ℂ) :=
  (f.hasCompactSupport.comp_left (by simp : Complex.ofReal (0:ℝ) = 0)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp f.contDiff)

@[simp] lemma complexBump_apply (f : ContDiffBump (0:E)) (x : E) :
    complexBump f x = Complex.ofReal (f x) := rfl

def innerBump : ContDiffBump (0:E) := ⟨1/2, 1, by norm_num, by norm_num⟩
def outerBump : ContDiffBump (0:E) := ⟨2, 3, by norm_num, by norm_num⟩

def inner : 𝓢(E,ℂ) := complexBump innerBump
def outer : 𝓢(E,ℂ) := complexBump outerBump

end LocalBumps

end

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology ContDiff
noncomputable section

namespace DistributionExpansion
section
open MeasureTheory TemperedDistribution LocalDifferential LineDeriv
open scoped SchwartzMap
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

abbrev Term (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := 𝓢(E,ℂ) × List E

def evalTerm (t : Term E) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  smulLeftCLM F t.1 (derivative t.2 u)

def eval (ts : List (Term E)) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  (ts.map (fun t => evalTerm t u)).sum

@[simp] lemma eval_nil (u : 𝓢'(E,F)) : eval [] u = 0 := rfl
@[simp] lemma eval_cons (t : Term E) (ts : List (Term E)) (u : 𝓢'(E,F)) :
    eval (t::ts) u = evalTerm t u + eval ts u := rfl

def differentiate (v : E) (ts : List (Term E)) : List (Term E) :=
  ts.flatMap (fun t => [(∂_{v} t.1,t.2),(t.1,v::t.2)])

def lower : List E → 𝓢(E,ℂ) → List (Term E)
  | [], _ => []
  | v::vs, a => (∂_{v} a,vs) :: differentiate v (lower vs a)

end

section
open TemperedDistribution LocalDifferential LineDeriv
open scoped SchwartzMap
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def divergence {N : ℕ} (a : Fin N → 𝓢(E,ℂ)) (vs : Fin N → List E)
    (u : 𝓢'(E,F)) : 𝓢'(E,F) := ∑ i, derivative (vs i) (smulLeftCLM F (a i) u)

def lowerTerms {N M : ℕ} (a : Fin N → 𝓢(E,ℂ)) (vs : Fin N → List E)
    (b : Fin M → 𝓢(E,ℂ)) (ws : Fin M → List E) : List (Term E) :=
  (List.ofFn (fun i => lower (vs i) (a i))).flatten ++
  (List.ofFn (fun i => (b i,ws i) :: lower (ws i) (b i))).flatten

end

open MeasureTheory TemperedDistribution LocalDifferential LineDeriv
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def testDerivative : List E → 𝓢(E,ℂ) →L[ℂ] 𝓢(E,ℂ)
  | [] => ContinuousLinearMap.id ℂ _
  | v::vs => (testDerivative vs).comp (lineDerivOpCLM ℂ 𝓢(E,ℂ) v)

end DistributionExpansion

namespace SchwartzOperator
section
open LocalDifferential LineDeriv
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Term (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := 𝓢(E,ℂ) × List E

def derivative : List E → 𝓢(E,ℂ) →L[ℂ] 𝓢(E,ℂ)
  | [] => ContinuousLinearMap.id ℂ _
  | v::vs => (lineDerivOpCLM ℂ 𝓢(E,ℂ) v).comp (derivative vs)

@[simp] lemma derivative_nil (φ : 𝓢(E,ℂ)) : derivative [] φ = φ := rfl
@[simp] lemma derivative_cons (v : E) (vs : List E) (φ : 𝓢(E,ℂ)) :
    derivative (v::vs) φ = ∂_{v} (derivative vs φ) := rfl

def term (t : Term E) : 𝓢(E,ℂ) →L[ℂ] 𝓢(E,ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ t.1).comp (derivative t.2)

def operator (ts : List (Term E)) : 𝓢(E,ℂ) →L[ℂ] 𝓢(E,ℂ) := (ts.map term).sum

@[simp] lemma term_apply (t : Term E) (φ : 𝓢(E,ℂ)) :
    term t φ = product t.1 (derivative t.2 φ) := rfl
@[simp] lemma operator_nil (φ : 𝓢(E,ℂ)) : operator [] φ = 0 := rfl
@[simp] lemma operator_cons (t : Term E) (ts : List (Term E)) (φ : 𝓢(E,ℂ)) :
    operator (t::ts) φ = term t φ + operator ts φ := rfl

def differentiate (v : E) (ts : List (Term E)) : List (Term E) :=
  ts.flatMap (fun t => [(∂_{v} t.1,t.2),(t.1,v::t.2)])

def lower : List E → 𝓢(E,ℂ) → List (Term E)
  | [], _ => []
  | v::vs, a => (∂_{v} a,vs) :: differentiate v (lower vs a)

def composeLower (t s : Term E) : List (Term E) :=
  (lower t.2 s.1).map (fun r => (product t.1 r.1,r.2++s.2))

def composeTerm (t s : Term E) : List (Term E) :=
  (product t.1 s.1,t.2++s.2)::composeLower t s


def compose (ts ss : List (Term E)) : List (Term E) :=
  ts.flatMap (fun t => ss.flatMap (composeTerm t))

def principalCompose (ts ss : List (Term E)) : List (Term E) :=
  ts.flatMap (fun t => ss.map (fun s => (product t.1 s.1,t.2++s.2)))

def lowerCompose (ts ss : List (Term E)) : List (Term E) :=
  ts.flatMap (fun t => ss.flatMap (composeLower t))

def negTerms (ts : List (Term E)) : List (Term E) := ts.map (fun t => (-t.1,t.2))

def secondOrderRemainder (ts us : List (Term E)) : List (Term E) :=
  lowerCompose ts ts ++ compose ts us ++ compose us ts ++ compose us us ++ negTerms (ts++us)

end

open MeasureTheory TemperedDistribution LocalDifferential LineDeriv
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def adjointTerm (t : Term E) (u : 𝓢'(E,ℂ)) : 𝓢'(E,ℂ) :=
  LocalDifferential.derivative t.2.reverse
    (smulLeftCLM ℂ ((-1:ℂ)^t.2.length • t.1 : 𝓢(E,ℂ)) u)

def adjoint (ts : List (Term E)) (u : 𝓢'(E,ℂ)) : 𝓢'(E,ℂ) :=
  (ts.map (fun t => adjointTerm t u)).sum

end SchwartzOperator

namespace LocalSymbol
section
open Function
open scoped Real ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker, Sébastien Gouëzel

The following temperate growth theorem is adapted from Mathlib.Analysis.Distribution.TemperateGrowth.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Distribution/TemperateGrowth.lean

This code has been modified.
-/

def quadratic (A : E →L[ℝ] E) (x : E) : ℝ := inner ℝ x (A x)
def principal (A : E →L[ℝ] E) (x : E) : ℂ := Complex.ofReal (quadratic A x)^2
def regularized (A : E →L[ℝ] E) (x : E) : ℂ := 1+principal A x
def inverseSymbol (A : E →L[ℝ] E) (x : E) : ℂ :=
  Complex.ofReal (1+quadratic A x ^ 2)⁻¹

end

open Metric
open scoped Real

end LocalSymbol

namespace SchwartzOperator
section
open LocalDifferential
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def testSymbol (ts : List (Term E)) (x ξ : E) : ℂ :=
  (ts.map (fun t => t.1 x * LocalDifferential.symbol t.2 ξ)).sum

@[simp] lemma testSymbol_nil (x ξ : E) : testSymbol ([] : List (Term E)) x ξ = 0 := rfl
@[simp] lemma testSymbol_cons (t : Term E) (ts : List (Term E)) (x ξ : E) :
    testSymbol (t::ts) x ξ = t.1 x * LocalDifferential.symbol t.2 ξ + testSymbol ts x ξ := rfl

end

open MeasureTheory TemperedDistribution LocalDifferential LocalOperator
open scoped SchwartzMap Topology

end SchwartzOperator

namespace SmoothOperator
section
open LocalDifferential Filter
open scoped SchwartzMap Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Coefficient (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  fn : E → ℂ
  smooth : ContDiff ℝ ∞ fn

instance instCoeFunCoefficientForallComplex : CoeFun (Coefficient E) (fun _ => E → ℂ) := ⟨Coefficient.fn⟩
abbrev Term (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := Coefficient E × List E

def derivative : List E → (E → ℂ) → E → ℂ
  | [], f => f
  | v::vs, f => fun x => fderiv ℝ (derivative vs f) x v

def operator (ts : List (Term E)) (f : E → ℂ) : E → ℂ :=
  (ts.map (fun t => fun x => t.1 x * derivative t.2 f x)).sum

@[simp] lemma operator_nil (f : E → ℂ) : operator ([] : List (Term E)) f = 0 := rfl
@[simp] lemma operator_cons (t : Term E) (ts : List (Term E)) (f : E → ℂ) :
    operator (t::ts) f = (fun x => t.1 x * derivative t.2 f x) + operator ts f := rfl

def localizeTerm (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ) (t : Term E) : SchwartzOperator.Term E :=
  ((hχ.mul_right (f':=(t.1 : E → ℂ))).toSchwartzMap (χ.smooth'.mul t.1.smooth),t.2)

def localize (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ) (ts : List (Term E)) : List (SchwartzOperator.Term E) :=
  ts.map (localizeTerm χ hχ)

end

open MeasureTheory LocalDifferential Filter Metric TemperedDistribution
open scoped SchwartzMap Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def testSymbol (ts : List (Term E)) (x ξ : E) : ℂ :=
  (ts.map (fun t => t.1 x * LocalDifferential.symbol t.2 ξ)).sum

end SmoothOperator

namespace RealSmoothOperator
section
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Coefficient (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  fn : E → ℝ
  smooth : ContDiff ℝ ∞ fn
instance instCoeFunCoefficientForallReal : CoeFun (Coefficient E) (fun _ => E → ℝ) := ⟨Coefficient.fn⟩
abbrev Term (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := Coefficient E × List E

def derivative : List E → (E → ℝ) → E → ℝ
  | [], f => f
  | v::vs, f => fun x => fderiv ℝ (derivative vs f) x v

lemma derivative_smooth (vs : List E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (derivative vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact (ih.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

lemma derivative_compact (vs : List E) {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (derivative vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact ih.fderiv_apply ℝ v

def operator (ts : List (Term E)) (f : E → ℝ) : E → ℝ :=
  (ts.map (fun t => fun x => t.1 x * derivative t.2 f x)).sum

lemma operator_smooth (ts : List (Term E)) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (operator ts f) := by
  induction ts with
  | nil => exact contDiff_const
  | cons t ts ih => exact (t.1.smooth.mul (derivative_smooth t.2 hf)).add ih

lemma operator_compact (ts : List (Term E)) {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (operator ts f) := by
  induction ts with
  | nil => simpa only [operator,List.map_nil,List.sum_nil] using (HasCompactSupport.zero : HasCompactSupport (0 : E → ℝ))
  | cons t ts ih => exact ((derivative_compact t.2 hf).mul_left).add ih

end
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def complexifyTerm (t : Term E) : SmoothOperator.Term E :=
  (⟨fun x => (t.1 x : ℂ), Complex.ofRealCLM.contDiff.comp t.1.smooth⟩, t.2)
def complexify (ts : List (Term E)) : List (SmoothOperator.Term E) := ts.map complexifyTerm

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def pushTerm (e : E ≃L[ℝ] F) (t : Term E) : Term F :=
  (⟨t.1.fn ∘ e.symm, t.1.smooth.comp e.symm.contDiff⟩,t.2.map e)
def push (e : E ≃L[ℝ] F) (ts : List (Term E)) : List (Term F) := ts.map (pushTerm e)

end

end RealSmoothOperator
namespace MatrixOperator
section
open MeasureTheory RealSmoothOperator Matrix
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Space (ι : Type*) := ι → ℝ
abbrev Euclid (ι : Type*) := EuclideanSpace ℝ ι
def e (i : ι) : Space ι := Pi.single i 1
def A (τ : Space ι → Matrix ι ι ℝ) (f : Space ι → ℝ) (x : Space ι) : ℝ :=
  (∑ i, x i * fderiv ℝ f x (e i)) -
    ∑ i, ∑ j, τ x i j * fderiv ℝ (fun y => fderiv ℝ f y (e j)) x (e i)

def principal (τ : Space ι → Matrix ι ι ℝ)
    (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) : List (Term (Space ι)) :=
  (Finset.univ : Finset (ι×ι)).toList.map (fun p =>
    (⟨fun x => -τ x p.1 p.2,(hτ p.1 p.2).neg⟩,[e p.1,e p.2]))
def drift : List (Term (Space ι)) :=
  (Finset.univ : Finset ι).toList.map (fun i => (⟨fun x => x i,(ContinuousLinearMap.proj i : Space ι →L[ℝ] ℝ).contDiff⟩,[e i]))

def coordinates : Space ι ≃L[ℝ] Euclid ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm

def frozen (τ : Matrix ι ι ℝ) : Euclid ι →L[ℝ] Euclid ι :=
  (4*Real.pi^2) • (Matrix.toLpLin 2 2 τ).toContinuousLinearMap

end

open MeasureTheory RealSmoothOperator
open scoped ContDiff

end MatrixOperator

namespace WeightedRegularity
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [MeasurableSpace E]

def densityMeasure (μ : Measure E) (ρ : E → ℝ) : Measure E :=
  μ.withDensity (fun x => ENNReal.ofReal (ρ x))

end WeightedRegularity

end

open MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace WeightedCalculus


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def D (v : E) (f : E → ℝ) : E → ℝ := fun x => fderiv ℝ f x v

def adjoint (V : E → ℝ) (v : E) (f : E → ℝ) : E → ℝ :=
  fun x => D v V x * f x - D v f x

def weight (V : E → ℝ) : E → ℝ := fun x => Real.exp (-V x)

lemma smooth_D {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (D v f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

section FiniteDirections

variable {ι : Type*} [Fintype ι]

def divergence (V : E → ℝ) (e : ι → E) (W : ι → E → ℝ) : E → ℝ :=
  fun x => ∑ i, adjoint V (e i) (W i) x

end FiniteDirections


variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def expectation (V f : E → ℝ) : ℝ := ∫ x, f x * weight V x ∂μ


end WeightedCalculus

namespace MomentCoordinates

open WeightedCalculus Matrix
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Space (ι : Type*) := ι → ℝ

def basis (i : ι) : Space ι := Pi.single i 1

def pd (i : ι) (f : Space ι → ℝ) : Space ι → ℝ := D (basis i) f

def grad (f : Space ι → ℝ) (x : Space ι) : Space ι := fun i => pd i f x

def hess (f : Space ι → ℝ) (x : Space ι) : Matrix ι ι ℝ :=
  fun i j => pd j (pd i f) x

lemma smooth_pd {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) (i : ι) :
    ContDiff ℝ ∞ (pd i f) := smooth_D hf (basis i)

def pullA (φ f : Space ι → ℝ) : Space ι → ℝ := fun z =>
  (∑ i, grad φ z i * pd i f (grad φ z)) -
  ∑ i, ∑ j, hess φ z i j * hess f (grad φ z) i j

def P (φ f : Space ι → ℝ) (a k : ι) : Space ι → ℝ := fun z =>
  ∑ i, hess φ z a i * hess f (grad φ z) i k

def W (φ f : Space ι → ℝ) (a : ι) : Space ι → ℝ :=
  divergence φ basis (P φ f a)

def B (φ f : Space ι → ℝ) (a l : ι) : Space ι → ℝ := fun z =>
  ∑ k, P φ f a k z * hess φ z k l

def R (φ f : Space ι → ℝ) (a l : ι) : Space ι → ℝ :=
  divergence φ basis (fun k => pd l (P φ f a k))

end MomentCoordinates
end

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace MomentDifferential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def detMultilinear : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := continuous_id.matrix_det }

def md (v : E) (A : E → Matrix ι ι ℝ) (z : E) : Matrix ι ι ℝ :=
  fun i j => fderiv ℝ (fun z => A z i j) z v

end MomentDifferential

namespace MomentEquation
open WeightedCalculus MomentCoordinates MomentDifferential
open scoped ContDiff Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma smooth_hess {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ) (i j : ι) :
    ContDiff ℝ ∞ (fun z => hess φ z i j) := smooth_pd (smooth_pd hφ i) j

def C (φ : Space ι → ℝ) (i : ι) : Space ι → Matrix ι ι ℝ :=
  md (basis i) (hess φ)

end MomentEquation

namespace TargetCoordinates
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def target (Φ : Space ι ≃ₜ Space ι) (g : Space ι → ℝ) : Space ι → ℝ := g ∘ Φ.symm

def sourceMeasure (μ : Measure (Space ι)) (φ : Space ι → ℝ) : Measure (Space ι) :=
  μ.withDensity (fun z => ENNReal.ofReal (weight φ z))

def targetMeasure (μ : Measure (Space ι)) (V : Space ι → ℝ) (Z : ℝ) : Measure (Space ι) :=
  μ.withDensity (fun x => ENNReal.ofReal (weight V x / Z))

def normalizedE (μ : Measure (Space ι)) (V : Space ι → ℝ) (Z : ℝ) (F : Space ι → ℝ) : ℝ :=
  expectation μ V F / Z

end TargetCoordinates

namespace MomentOperator
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation TargetCoordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tau (Φ : Space ι ≃ₜ Space ι) (φ : Space ι → ℝ) (x : Space ι) : Matrix ι ι ℝ :=
  hess φ (Φ.symm x)

def A (Φ : Space ι ≃ₜ Space ι) (φ f : Space ι → ℝ) : Space ι → ℝ := fun x =>
  (∑ i, x i * pd i f x) - ∑ i, ∑ j, tau Φ φ x i j * hess f x i j

def flux (Φ : Space ι ≃ₜ Space ι) (φ f : Space ι → ℝ) (i : ι) : Space ι → ℝ := fun x =>
  ∑ j, tau Φ φ x i j * pd j f x

end MomentOperator

namespace DensityEnergy
open MeasureTheory Matrix WeightedCalculus
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Space (ι : Type*) := ι → ℝ
def e (i : ι) : Space ι := Pi.single i 1
def grad (f : Space ι → ℝ) (x : Space ι) : ι → ℝ := fun i => D (e i) f x
def gamma (τ : Space ι → Matrix ι ι ℝ) (f g : Space ι → ℝ) (x : Space ι) : ℝ :=
  grad f x ⬝ᵥ (τ x *ᵥ grad g x)
def A (τ : Space ι → Matrix ι ι ℝ) (f : Space ι → ℝ) (x : Space ι) : ℝ :=
  (∑ i, x i * D (e i) f x) - ∑ i, ∑ j, τ x i j * D (e i) (D (e j) f) x

end DensityEnergy
end

open scoped ContDiff Topology
noncomputable section
namespace SmoothCutoff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance dualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance dualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

def base : ContDiffBump (0:E) := ⟨1,2,by norm_num,by norm_num⟩
def cutoff (r : ℝ) (x : E) : ℝ := (base (E:=E) : E → ℝ) (r⁻¹ • x)

end SmoothCutoff

namespace SmoothCutoff
open Filter MeasureTheory
open scoped ContDiff Topology
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def seq (k : ℕ) : E → ℝ := cutoff ((k:ℝ)+1)

end

end SmoothCutoff

end

noncomputable section
namespace DensityEnergy
open MeasureTheory Matrix WeightedCalculus Filter
open scoped ContDiff Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def henergy (τ : Space ι → Matrix ι ι ℝ) (f : Space ι → ℝ) (x : Space ι) : ℝ :=
  (τ x*MomentCoordinates.hess f x*τ x*MomentCoordinates.hess f x).trace

end DensityEnergy

namespace MomentKernel

section
open MeasureTheory Matrix WeightedCalculus MomentCoordinates TargetCoordinates
open scoped ContDiff
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma smooth_tau {φ : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (Φ : Space ι ≃ₜ Space ι) (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι)) (i j : ι) :
    ContDiff ℝ ∞ (fun x => MomentOperator.tau Φ φ x i j) := (MomentEquation.smooth_hess hφ i j).comp hInv

end

end

open MeasureTheory Matrix WeightedCalculus MomentCoordinates TargetCoordinates
open scoped ContDiff


end MomentKernel

namespace RealSmoothOperator
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma derivative_add (vs : List E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    derivative vs (f+g) = derivative vs f+derivative vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change (fun x => fderiv ℝ (derivative vs (f+g)) x v) = _
    rw [ih]
    ext x
    simp only [Pi.add_apply,derivative,
      fderiv_add ((derivative_smooth vs hf).differentiable (by simp) x)
        ((derivative_smooth vs hg).differentiable (by simp) x),_root_.add_apply]

lemma derivative_smul (vs : List E) (a : ℝ) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) : derivative vs (a • f) = a • derivative vs f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change (fun x => fderiv ℝ (derivative vs (a • f)) x v) = _
    rw [ih]
    ext x
    have hh := (((derivative_smooth vs hf).differentiable (by simp) x).hasFDerivAt.const_smul a).fderiv
    change fderiv ℝ (a • derivative vs f) x v = a * fderiv ℝ (derivative vs f) x v
    rw [show fderiv ℝ (a • derivative vs f) x = a • fderiv ℝ (derivative vs f) x from hh]
    rfl

lemma operator_add (ts : List (Term E)) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    operator ts (f+g) = operator ts f+operator ts g := by
  induction ts with
  | nil => ext x; simp [operator]
  | cons t ts ih =>
    ext x
    change t.1 x*derivative t.2 (f+g) x+operator ts (f+g) x = _
    rw [derivative_add t.2 hf hg,ih]
    change t.1 x*(derivative t.2 f x+derivative t.2 g x)+
      (operator ts f x+operator ts g x) =
      (t.1 x*derivative t.2 f x+operator ts f x)+(t.1 x*derivative t.2 g x+operator ts g x)
    ring

lemma operator_smul (ts : List (Term E)) (a : ℝ) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) : operator ts (a • f) = a • operator ts f := by
  induction ts with
  | nil => ext x; simp [operator]
  | cons t ts ih =>
    ext x
    change t.1 x*derivative t.2 (a • f) x+operator ts (a • f) x = _
    rw [derivative_smul t.2 a hf,ih]
    change t.1 x*(a*derivative t.2 f x)+a*operator ts f x =
      a*(t.1 x*derivative t.2 f x+operator ts f x)
    ring

def tests : Submodule ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const,HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  smul_mem' a _f hf := ⟨hf.1.const_smul a,hf.2.smul_left⟩

lemma tests_smooth (f : tests (E:=E)) : ContDiff ℝ ∞ (f : E → ℝ) := f.property.1
lemma tests_compact (f : tests (E:=E)) : HasCompactSupport (f : E → ℝ) := f.property.2

def operatorLinear (ts : List (Term E)) : tests (E:=E) →ₗ[ℝ] tests (E:=E) where
  toFun f := ⟨operator ts f,operator_smooth ts (tests_smooth f),operator_compact ts (tests_compact f)⟩
  map_add' f g := Subtype.ext (operator_add ts (tests_smooth f) (tests_smooth g))
  map_smul' a f := Subtype.ext (operator_smul ts a (tests_smooth f))

def squareLinear (ts : List (Term E)) : tests (E:=E) →ₗ[ℝ] tests (E:=E) :=
  (operatorLinear ts).comp (operatorLinear ts-LinearMap.id)

@[simp] lemma squareLinear_coe (ts : List (Term E)) (f : tests (E:=E)) :
    ((squareLinear ts f : tests (E:=E)) : E → ℝ) = operator ts (operator ts f-f) := rfl

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

def testsLp (f : tests (E:=E)) : Lp ℝ 2 μ :=
  ((tests_smooth f).continuous.memLp_of_hasCompactSupport (tests_compact f) (p:=2)).toLp f

lemma testsLp_coe (f : tests (E:=E)) : (testsLp μ f : E → ℝ) =ᵐ[μ] (f : E → ℝ) :=
  MemLp.coeFn_toLp _

def testsLpLinear : tests (E:=E) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := testsLp μ
  map_add' f g := by
    apply Lp.ext
    filter_upwards [testsLp_coe μ (f+g),testsLp_coe μ f,testsLp_coe μ g,Lp.coeFn_add (testsLp μ f) (testsLp μ g)] with x ha hf hg hh
    rw [ha,hh]
    change (f : E → ℝ) x+(g : E → ℝ) x=(testsLp μ f : E → ℝ) x+(testsLp μ g : E → ℝ) x
    rw [hf,hg]
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [testsLp_coe μ (a • f),testsLp_coe μ f,Lp.coeFn_smul a (testsLp μ f)] with x ha hf hh
    change (testsLp μ (a • f) : E → ℝ) x=(a • testsLp μ f : Lp ℝ 2 μ) x
    rw [ha,hh]
    change a*(f : E → ℝ) x=a*(testsLp μ f : E → ℝ) x
    rw [hf]

def squareLp (ts : List (Term E)) : tests (E:=E) →ₗ[ℝ] Lp ℝ 2 μ :=
  (testsLpLinear μ).comp (squareLinear ts)

def squareRange (ts : List (Term E)) : Submodule ℝ (Lp ℝ 2 μ) := (squareLp μ ts).range

end RealSmoothOperator

namespace EvenClosure
open MeasureTheory
open scoped InnerProductSpace
variable {ι : Type*} [Fintype ι]
abbrev Space (ι : Type*) := ι → ℝ

end EvenClosure

end

open Matrix
open scoped BigOperators Kronecker
noncomputable section
namespace MetricTensor
variable {ι : Type*} [Fintype ι]
abbrev Idx (ι : Type*) := ι × ι × ι
abbrev Tensor (ι : Type*) := Idx ι → ℝ

def kernel (T : Matrix ι ι ℝ) : Matrix (Idx ι) (Idx ι) ℝ := T ⊗ₖ (T ⊗ₖ T)

def pair (T : Matrix ι ι ℝ) (A B : Tensor ι) : ℝ := A ⬝ᵥ (kernel T *ᵥ B)
def sq (T : Matrix ι ι ℝ) (A : Tensor ι) : ℝ := pair T A A

def sw : Idx ι ≃ Idx ι where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv := by rintro ⟨i,j,k⟩; rfl
  right_inv := by rintro ⟨i,j,k⟩; rfl

def cy : Idx ι ≃ Idx ι where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun p := (p.2.1, p.2.2, p.1)
  left_inv := by rintro ⟨i,j,k⟩; rfl
  right_inv := by rintro ⟨i,j,k⟩; rfl

def swap (A : Tensor ι) : Tensor ι := A ∘ sw
def cycle (A : Tensor ι) : Tensor ι := A ∘ cy
def sym (A : Tensor ι) : Tensor ι := (1/3 : ℝ) • (A + swap A + cycle A)

def act (A B C : Matrix ι ι ℝ) (X : Tensor ι) : Tensor ι :=
  (A ⊗ₖ (B ⊗ₖ C)) *ᵥ X

end MetricTensor

namespace TensorEstimate
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation Matrix MetricTensor
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cube (f : Space ι → ℝ) (z : Space ι) : Tensor ι :=
  fun p => C f p.2.2 z p.1 p.2.1

def pulledH (φ f : Space ι → ℝ) : Space ι → Matrix ι ι ℝ := hess f ∘ grad φ

def Q (φ f : Space ι → ℝ) (z : Space ι) : Matrix ι ι ℝ :=
  pulledH φ f z * hess φ z * pulledH φ f z

def slice (X : Tensor ι) (i : ι) : Matrix ι ι ℝ := fun a b => X (i,a,b)

def cross (φ f : Space ι → ℝ) (z : Space ι) : ℝ :=
  ∑ a, ∑ l, ∑ k, pd k (fun y => pulledH φ f y a l) z * pd l (P φ f a k) z

def qder (φ f : Space ι → ℝ) (z : Space ι) : ℝ :=
  ∑ i, ∑ j, ∑ d, pd d (fun y => Q φ f y i j) z *
    ∑ k, (hess φ z)⁻¹ d k * C φ i z j k

def cubic (φ f : Space ι → ℝ) (z : Space ι) : ℝ :=
  ∑ i, ∑ j, Q φ f z i j * ((hess φ z)⁻¹ * C φ i z * (hess φ z)⁻¹ * C φ j z).trace

end TensorEstimate

namespace IntegratedTensor
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation TensorEstimate Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rmat (φ f : Space ι → ℝ) (z : Space ι) : Matrix ι ι ℝ := fun a l => R φ f a l z

def bmat (φ f : Space ι → ℝ) (z : Space ι) : Matrix ι ι ℝ :=
  hess φ z * pulledH φ f z * hess φ z

def base (φ f : Space ι → ℝ) (z : Space ι) : ℝ :=
  ((hess φ z)⁻¹ * bmat φ f z * (hess φ z)⁻¹ * bmat φ f z).trace

def rterm (φ f : Space ι → ℝ) (z : Space ι) : ℝ :=
  ((hess φ z)⁻¹ * rmat φ f z * (hess φ z)⁻¹ * rmat φ f z).trace

def mixed (φ f : Space ι → ℝ) (z : Space ι) : ℝ :=
  (pulledH φ f z * rmat φ f z).trace

variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

def L (φ : Space ι → ℝ) (i j d : ι) (z : Space ι) : ℝ :=
  ∑ k, (hess φ z)⁻¹ d k * C φ i z j k

def divterm (φ f : Space ι → ℝ) (z : Space ι) : ℝ :=
  ∑ i, ∑ j, Q φ f z i j * divergence φ basis (L φ i j) z

def jacW (φ f : Space ι → ℝ) (z : Space ι) : Matrix ι ι ℝ :=
  fun a l => pd l (W φ f a) z

def traceL (φ f : Space ι → ℝ) (z : Space ι) : ℝ :=
  (jacW φ f z * (hess φ z)⁻¹ * (jacW φ f z * (hess φ z)⁻¹)).trace

def traceH (φ V f : Space ι → ℝ) (z : Space ι) : ℝ :=
  ((hess φ z)⁻¹ * bmat φ f z * hess V (grad φ z) * bmat φ f z).trace

end IntegratedTensor

namespace FullTensor
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation IntegratedTensor TargetCoordinates Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wField (Φ : Space ι ≃ₜ Space ι) (φ f : Space ι → ℝ) (a : ι) : Space ι → ℝ :=
  target Φ (W φ f a)

def bField (Φ : Space ι ≃ₜ Space ι) (φ f : Space ι → ℝ) (x : Space ι) : Matrix ι ι ℝ :=
  bmat φ f (Φ.symm x)

def mField (Φ : Space ι ≃ₜ Space ι) (φ : Space ι → ℝ) (x : Space ι) : Matrix ι ι ℝ :=
  (hess φ (Φ.symm x))⁻¹

def jacobian (Y : ι → Space ι → ℝ) (x : Space ι) : Matrix ι ι ℝ := fun a l => pd l (Y a) x

def squareTrace (Y : ι → Space ι → ℝ) (x : Space ι) : ℝ :=
  (jacobian Y x * jacobian Y x).trace

def hEnergy (Φ : Space ι ≃ₜ Space ι) (φ V f : Space ι → ℝ) (x : Space ι) : ℝ :=
  (mField Φ φ x * bField Φ φ f x * hess V x * bField Φ φ f x).trace

def wEnergy (V : Space ι → ℝ) (Y : ι → Space ι → ℝ) (x : Space ι) : ℝ :=
  ∑ j, ∑ i, hess V x i j * Y i x * Y j x

end FullTensor

namespace DualEnergy
open MeasureTheory WeightedCalculus MomentCoordinates MomentDifferential MomentEquation
  IntegratedTensor TargetCoordinates FullTensor TensorEstimate

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (μ : Measure (Space ι)) [Measure.IsAddHaarMeasure μ]

def tau (Φ : Space ι ≃ₜ Space ι) (φ : Space ι → ℝ) (x : Space ι) : Matrix ι ι ℝ := hess φ (Φ.symm x)

end

end DualEnergy

namespace SoftSlab

section
open WeightedCalculus MomentCoordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def linear (p : ι → ℝ) : Space ι →L[ℝ] ℝ :=
  ∑ i, p i • ContinuousLinearMap.proj i

def summand (p : ι → ℝ) (h : ℝ) (q : ℕ) : Space ι → ℝ := fun x =>
  (linear p x / h)^q

end

open MeasureTheory WeightedCalculus MomentCoordinates
open scoped BigOperators ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def potential (ε : ℝ) (p : κ → ι → ℝ) (h : κ → ℝ) (q : ℕ) (x : Space ι) : ℝ :=
  ε/2*(∑ j, x j^2) + ∑ i, summand (p i) (h i) q x


end SoftSlab
end

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace SoftSlab
open MeasureTheory WeightedCalculus MomentCoordinates
open scoped BigOperators ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

abbrev law (ε : ℝ) (p : κ → ι → ℝ) (h : κ → ℝ) (q : ℕ) : Measure (Space ι) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-potential ε p h q x)/
    (∫ y, Real.exp (-potential ε p h q y))))

def linearPolynomial (p : ι → ℝ) (h : ℝ) : MvPolynomial ι ℝ :=
  (∑ j, MvPolynomial.C (p j)*MvPolynomial.X j)*MvPolynomial.C h⁻¹

end SoftSlab
end

open scoped BigOperators InnerProductSpace Topology

noncomputable section

namespace LpVariance
open MeasureTheory
open scoped InnerProductSpace
variable {X : Type*} {ι : Type*} [MeasurableSpace X] [Fintype ι]
variable (μ : Measure X)

variable [IsProbabilityMeasure μ]

def sumPotential (ψ : ι → X → ℝ) (b : ι → ℝ) (x : X) : ℝ := ∑ i, b i*ψ i x

def centered (f : X → ℝ) (x : X) : ℝ := f x-∫ y, f y ∂μ

end LpVariance

end

end
section


open Set MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LogBrunnMinkowski

def MainStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (K L : Set (Space n)),
    IsConvexBody K → IsConvexBody L → OriginSymmetric K → OriginSymmetric L →
    ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
      (volume K) ^ (1 - t) * (volume L) ^ t ≤ volume (logCombination K L t)

abbrev UnitSphere (n : ℕ) := {u : Space n // ‖u‖ = 1}

def finiteSlabs {n : ℕ} (D : Finset (Space n)) (f : Space n → ℝ) : Set (Space n) :=
  {x | ∀ u ∈ D, |⟪x, u⟫_ℝ| ≤ f u}

noncomputable def directions {n : ℕ} (d : ℕ → UnitSphere n) (m : ℕ) : Finset (Space n) :=
  (Finset.univ.image (EuclideanSpace.basisFun (Fin n) ℝ)) ∪
    ((Finset.range m).image (fun i => (d i).val))

noncomputable def interpolatedSupport {n : ℕ} (K L : Set (Space n)) (t : ℝ)
    (u : Space n) : ℝ := support K u ^ (1 - t) * support L u ^ t

noncomputable def oneEquiv : Space 1 ≃ₗᵢ[ℝ] ℝ :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm

noncomputable def oneDirection : Space 1 := oneEquiv.symm 1

end LogBrunnMinkowski

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace SlabPartition
open Set MeasureTheory
open scoped BigOperators
variable {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

def derivativePoly (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (k : ℕ) (t : ℝ) :
    MvPolynomial ι ℝ := ∑ i, MvPolynomial.C (b i ^ k * Real.exp (b i * t)) * ψ i

def variation (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (k : ℕ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  MvPolynomial.eval x (derivativePoly ψ b k t)

def potential (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  ε / 2 * (∑ j, x j ^ 2) + variation ψ b 0 t x

def density (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp (-potential ε ψ b t x)

def densityFirst (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  -variation ψ b 1 t x * density ε ψ b t x

def densitySecond (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  (variation ψ b 1 t x ^ 2 - variation ψ b 2 t x) * density ε ψ b t x

def boundPoly (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (k : ℕ) (t₀ : ℝ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (|b i| ^ k * Real.exp (|b i| * (|t₀| + 1))) * ψ i

def partition (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, density ε ψ b t x

def partitionFirst (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, densityFirst ε ψ b t x

def partitionSecond (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, densitySecond ε ψ b t x

def mean (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ)
    (F : (ι → ℝ) → ℝ) : ℝ := (∫ x, F x * density ε ψ b t x) / partition ε ψ b t

def variance (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ)
    (F : (ι → ℝ) → ℝ) : ℝ :=
  mean ε ψ b t (fun x => (F x - mean ε ψ b t F)^2)

end SlabPartition

namespace SoftSlabLimits
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators
variable {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

def body (ℓ : κ → (ι → ℝ) →ₗ[ℝ] ℝ) : Set (ι → ℝ) :=
  {x | ∀ i, |ℓ i x| ≤ 1}

def gaussian (ε : ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp (-(ε / 2) * ∑ j, x j ^ 2)

def density (ℓ : κ → (ι → ℝ) →ₗ[ℝ] ℝ) (ε : ℝ) (k : ℕ) (x : ι → ℝ) : ℝ :=
  Real.exp (-(ε / 2) * ∑ j, x j ^ 2 - ∑ i, (ℓ i x) ^ (2*k+2))

end SoftSlabLimits

namespace SlabReduction
open MeasureTheory Set Filter
open scoped BigOperators Topology
variable {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

def linearPoly (p : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ j, MvPolynomial.C (p j) * MvPolynomial.X j

def feature (p : ι → ℝ) (h : ℝ) (q : ℕ) : MvPolynomial ι ℝ :=
  (MvPolynomial.C h⁻¹ * linearPoly p) ^ q

def width (h₀ h₁ t : ℝ) : ℝ := h₀ ^ (1-t) * h₁ ^ t

def normal (p : ι → ℝ) (h : ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ :=
  h⁻¹ • (dotProductBilin ℝ ℝ p)

def rate (q : ℕ) (h₀ h₁ : ℝ) : ℝ := -(q:ℝ) * Real.log (h₁/h₀)

def features (p : κ → ι → ℝ) (h : κ → ℝ) (q : ℕ) : κ → MvPolynomial ι ℝ :=
  fun i => feature (p i) (h i) q

def rates (h₀ h₁ : κ → ℝ) (q : ℕ) : κ → ℝ := fun i => rate q (h₀ i) (h₁ i)

def normals (p : κ → ι → ℝ) (h : κ → ℝ) : κ → (ι → ℝ) →ₗ[ℝ] ℝ :=
  fun i => normal (p i) (h i)

def widths (h₀ h₁ : κ → ℝ) (t : ℝ) : κ → ℝ := fun i => width (h₀ i) (h₁ i) t

end SlabReduction

namespace LogBrunnMinkowski

def SoftVarianceStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (κ : Type) (_ : Fintype κ) (_ : Nonempty κ),
  ∀ (q : ℕ), Even q → 2 ≤ q → ∀ (ε : ℝ), 0 < ε →
  ∀ (p : κ → Fin n → ℝ), (∀ i, p i ≠ 0) → ∀ (h : κ → ℝ), (∀ i, 0 < h i) →
  ∀ (b : κ → ℝ),
    SlabPartition.variance ε (SlabReduction.features p h q) (fun _ => 0) 0
      (fun x => ∑ i, b i * MvPolynomial.eval x (SlabReduction.features p h q i)) ≤
    SlabPartition.mean ε (SlabReduction.features p h q) (fun _ => 0) 0
      (fun x => ∑ i, b i^2 * MvPolynomial.eval x (SlabReduction.features p h q i))

end LogBrunnMinkowski
end


end



noncomputable section
namespace ScaledKernel
open MeasureTheory Set Filter Metric
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [MeasurableSpace E] [BorelSpace E] in
def dilate (K : 𝓢(E,ℂ)) (r : ℝ) (hr : r≠0) : 𝓢(E,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearEquiv.smulOfNeZero ℝ E r hr).toContinuousLinearEquiv K

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma dilate_apply (K : 𝓢(E,ℂ)) (r : ℝ) (hr : r≠0) (x : E) :
    dilate K r hr x=K (r • x) := rfl

def applyKernel (K : 𝓢(E,ℂ)) (r : ℝ) (f : E → ℂ) (x : E) : ℂ :=
  ∫ t,K t*f (x-r • t)

end ScaledKernel

namespace AnnularSymbol
open Set Filter Metric FourierTransform
open scoped SchwartzMap Topology InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def bump : ContDiffBump (0:E) := ⟨1,2,by norm_num,by norm_num⟩
def cutoff (x : E) : ℝ := (bump (E:=E) : E → ℝ) ((1/2:ℝ) • x)-(bump (E:=E) : E → ℝ) x

lemma contDiff_cutoff : ContDiff ℝ ∞ (cutoff : E → ℝ) :=
  ((bump (E:=E)).contDiff.comp (contDiff_const.smul contDiff_id)).sub (bump (E:=E)).contDiff
lemma compact_cutoff : HasCompactSupport (cutoff : E → ℝ) :=
  ((bump (E:=E)).hasCompactSupport.comp_smul (by norm_num : (1/2:ℝ) ≠ 0)).sub (bump (E:=E)).hasCompactSupport
lemma cutoff_zero_near : (cutoff : E → ℝ)=ᶠ[𝓝 0] 0 := by
  filter_upwards [ball_mem_nhds (0:E) zero_lt_one] with x hx
  have hx1 : ‖x‖<1 := by simpa only [mem_ball,dist_zero_right] using hx
  have h1 : x∈closedBall (0:E) (bump (E:=E)).rIn := by
    change dist x 0≤1
    simpa only [dist_zero_right] using hx1.le
  have h2 : (1/2:ℝ) • x∈closedBall (0:E) (bump (E:=E)).rIn := by
    change dist ((1/2:ℝ) • x) 0≤1
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num)]
    linarith [norm_nonneg x]
  simp only [cutoff,(bump (E:=E)).one_of_mem_closedBall h1,(bump (E:=E)).one_of_mem_closedBall h2,sub_self,Pi.zero_apply]

def multiplier (A : E →L[ℝ] E) (v w x : E) : ℂ :=
  Complex.ofReal (cutoff x*(⟪x,v⟫_ℝ *  ⟪x,w⟫_ℝ /  ⟪x,A x⟫_ℝ))
lemma multiplier_compact (A : E →L[ℝ] E) (v w : E) : HasCompactSupport (multiplier A v w) :=
  (compact_cutoff.mul_right).comp_left (by simp : Complex.ofReal (0:ℝ)=0)

lemma multiplier_smooth (A : E →L[ℝ] E)
    (hA : ∀ x:E,x≠0 → 0<⟪x,A x⟫_ℝ) (v w : E) : ContDiff ℝ ∞ (multiplier A v w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    apply (show ContDiffAt ℝ ∞ (fun _ : E => (0:ℂ)) 0 from contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [cutoff_zero_near (E:=E)] with y hy
    simp only [multiplier,hy,Pi.zero_apply,zero_mul,Complex.ofReal_zero]
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (contDiff_cutoff.contDiffAt.mul (((contDiffAt_id.inner ℝ contDiffAt_const).mul
        (contDiffAt_id.inner ℝ contDiffAt_const)).div (contDiffAt_id.inner ℝ A.contDiff.contDiffAt) (hA x hx).ne'))

def symbol (A : E →L[ℝ] E) (hA : ∀ x:E,x≠0 → 0<⟪x,A x⟫_ℝ) (v w : E) : 𝓢(E,ℂ) :=
  (multiplier_compact A v w).toSchwartzMap (multiplier_smooth A hA v w)

variable [MeasurableSpace E] [BorelSpace E]

def kernel (A : E →L[ℝ] E) (hA : ∀ x:E,x≠0 → 0<⟪x,A x⟫_ℝ) (v w : E) : 𝓢(E,ℂ) :=
  𝓕⁻ (symbol A hA v w)

end AnnularSymbol

namespace AnnularFourier
section
open Set MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def product (f g : 𝓢(E,ℂ)) : 𝓢(E,ℂ) := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma product_apply (f g : 𝓢(E,ℂ)) (x : E) : product f g x=f x*g x := rfl

def conv (f g : 𝓢(E,ℂ)) : 𝓢(E,ℂ) := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g

variable {ι : Type*} [Fintype ι]
def elliptic (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (u : 𝓢(E,ℂ)) : 𝓢(E,ℂ) :=
  ∑ i,∂_{b i} (∂_{A (b i)} u)

end
section
open Set MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def normalized (K : 𝓢(E,ℂ)) (r : ℝ) (hr : r≠0) : 𝓢(E,ℂ) :=
  (r^Module.finrank ℝ E)⁻¹ • ScaledKernel.dilate K r⁻¹ (inv_ne_zero hr)

def annulus : 𝓢(E,ℂ) :=
  (AnnularSymbol.compact_cutoff.comp_left (by simp : Complex.ofReal (0:ℝ)=0)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp AnnularSymbol.contDiff_cutoff)
omit [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma annulus_apply (x : E) : annulus x=Complex.ofReal (AnnularSymbol.cutoff x) := rfl

end
open Set MeasureTheory FourierTransform Filter LineDeriv
open scoped SchwartzMap InnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def lowBump : ContDiffBump (0:E) := ⟨1,2,by norm_num,by norm_num⟩
def lowSymbol : 𝓢(E,ℂ) :=
  ((lowBump (E:=E)).hasCompactSupport.comp_left (by simp : Complex.ofReal (0:ℝ)=0)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (lowBump (E:=E)).contDiff)

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma lowSymbol_apply (x : E) : lowSymbol x=Complex.ofReal (lowBump (E:=E) x) := rfl

def lowFilter (u : 𝓢(E,ℂ)) (r : ℝ) (hr : r≠0) : 𝓢(E,ℂ) :=
  𝓕⁻ (product (ScaledKernel.dilate lowSymbol r hr) (𝓕 u))

end AnnularFourier
namespace AnnularFourier
open Set MeasureTheory FourierTransform Filter LineDeriv Metric
open scoped SchwartzMap InnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def lowKernel : 𝓢(E,ℂ) := 𝓕⁻ (lowSymbol : 𝓢(E,ℂ))
end AnnularFourier
namespace CompactMollification
section
open Set MeasureTheory Metric Filter LineDeriv
open scoped SchwartzMap Topology InnerProductSpace Convolution ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def dd (u : E → ℂ) (v w x : E) : ℂ := fderiv ℝ (fun z => fderiv ℝ u z w) x v

def mollifier : 𝓢(E,ℂ) :=
  (((AnnularFourier.lowBump (E:=E)).hasCompactSupport_normed (μ:=volume)).comp_left
    (by simp : Complex.ofReal (0:ℝ)=0)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (AnnularFourier.lowBump (E:=E)).contDiff_normed)
end
open Set MeasureTheory Metric Filter LineDeriv
open scoped SchwartzMap Topology InnerProductSpace Convolution ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

def elliptic (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (u : E → ℂ) (x : E) : ℂ :=
  ∑ i,dd u (b i) (A (b i)) x

end CompactMollification

namespace HessianInterpolation
section
open Set Metric
open scoped ContDiff
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def hessian (u : E → F) (x : E) : E →L[ℝ] E →L[ℝ] F := fderiv ℝ (fderiv ℝ u) x

end
open Set Metric
open scoped InnerProductSpace

end HessianInterpolation
namespace CoefficientTrace
open Set Metric
open scoped InnerProductSpace
variable {E : Type*} {F : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
def trace (b : OrthonormalBasis ι ℝ E) (H : E →L[ℝ] E →L[ℝ] F) (A : E →L[ℝ] E) : F :=
  ∑ i,H (b i) (A (b i))
lemma norm_bound (b : OrthonormalBasis ι ℝ E) (H : E →L[ℝ] E →L[ℝ] F) (A : E →L[ℝ] E) :
    ‖trace b H A‖≤(Fintype.card ι:ℝ)*‖H‖*‖A‖ := by
  calc
    _ ≤ ∑ i,‖H (b i) (A (b i))‖ := norm_sum_le _ _
    _ ≤ ∑ _i:ι,‖H‖*‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h1 := (H (b i)).le_opNorm (A (b i))
      have h2 := H.le_opNorm (b i)
      have h3 := A.le_opNorm (b i)
      simp only [b.orthonormal.norm_eq_one,mul_one] at h2 h3
      exact h1.trans (mul_le_mul h2 h3 (norm_nonneg (A (b i))) (norm_nonneg H))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
end CoefficientTrace
end
noncomputable section

namespace HessianInterpolation
open Set Metric
open scoped ContDiff
variable {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def complexLift (H : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℂ :=
  (ContinuousLinearMap.compL ℝ E ℝ ℂ Complex.ofRealCLM).comp H
end HessianInterpolation

namespace HolderControl
section
open Set Metric
variable {E : Type*} {F : Type*} {G : Type*} {H : Type*} {J : Type*} [PseudoMetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def Controlled (a : ℝ) (s : Set E) (f : J → E → F) : Prop :=
  ∃ B C : ℝ,0≤B ∧ 0≤C ∧ (∀ j x,x∈s → ‖f j x‖≤B) ∧
    ∀ j x,x∈s → ∀ y,y∈s → dist (f j x) (f j y)≤C*dist x y^a

end

open Set Metric
end HolderControl

namespace HolderControl

section
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology
variable {E : Type*} {J : Type*} {J' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

end

open Set Metric
open scoped ContDiff InnerProductSpace
end HolderControl
end


noncomputable section
namespace HessianTrace
section
open Matrix InnerProductSpace
open scoped InnerProductSpace ContDiff Matrix.Norms.Elementwise
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

local instance instTopologicalSpaceMatrixReal_solutions : TopologicalSpace (Matrix ι ι ℝ) :=
  (inferInstance : PseudoMetricSpace (Matrix ι ι ℝ)).toUniformSpace.toTopologicalSpace

def fromMatrix (b : OrthonormalBasis ι ℝ E) : Matrix ι ι ℝ ≃L[ℝ] E →L[ℝ] E :=
  ((LinearMap.toMatrix b.toBasis b.toBasis).symm.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

end


open Matrix Set InnerProductSpace
open scoped InnerProductSpace Matrix.Norms.Elementwise
end HessianTrace


section
open Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace LogDetSegment
section
open Matrix Set Filter MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ
local instance instTopologicalSpaceMatrixReal_solutions : TopologicalSpace Mat := (inferInstance : PseudoMetricSpace Mat).toUniformSpace.toTopologicalSpace

def segmentMatrix (A B : Mat) (t : ℝ) : Mat := A+t • (B-A)

def meanInverse (A B : Mat) : Mat := ∫ t in (0:ℝ)..1,(segmentMatrix A B t)⁻¹

def traceRight (D : Mat) : Mat →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (M*D).trace
      map_add' := by intro M N; simp only [Matrix.add_mul,Matrix.trace_add]
      map_smul' := by intro c M; simp only [Matrix.smul_mul,Matrix.trace_smul,RingHom.id_apply] }

end
section
open Matrix Set Filter MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ
local instance instTopologicalSpaceMatrixReal_solutions_1 : TopologicalSpace Mat := (inferInstance : PseudoMetricSpace Mat).toUniformSpace.toTopologicalSpace

end
open Matrix Set Metric MeasureTheory
open scoped Matrix.Norms.Elementwise Topology
end LogDetSegment

end

namespace LogDetSegment
open Matrix Set Metric MeasureTheory
open scoped Matrix.Norms.Elementwise Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ
local instance instTopologicalSpaceMatrixReal_solutions_3 : TopologicalSpace Mat := (inferInstance : PseudoMetricSpace Mat).toUniformSpace.toTopologicalSpace

end LogDetSegment


namespace LogDetSegment
open Matrix Set Metric
open scoped Matrix.Norms.Elementwise Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Mat" => Matrix ι ι ℝ
local instance instTopologicalSpaceMatrixReal_solutions_4 : TopologicalSpace Mat := (inferInstance : PseudoMetricSpace Mat).toUniformSpace.toTopologicalSpace
end LogDetSegment


namespace FiniteDifference
section
open Set Metric MeasureTheory
open scoped ContDiff
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def increment (g : E → F) (v x : E) : F := g (x+v)-g x

end


open Set Metric
variable {E : Type*} {F : Type*} {J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def normalized (g : E → F) (v x : E) : F := ‖v‖⁻¹ • increment g v x

end FiniteDifference


namespace MomentQuotient
section
open Matrix Set InnerProductSpace
open scoped ContDiff Matrix.Norms.Elementwise InnerProductSpace
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

def quotient (u : E → ℝ) (v x : E) : ℝ := ‖v‖⁻¹*(u (x+v)-u x)

def matrixHessian (b : OrthonormalBasis ι ℝ E) (u : E → ℝ) (x : E) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient u) x).toLinearMap

local instance instTopologicalSpaceMatrixReal_solutions_r3f7403_1 : TopologicalSpace (Matrix ι ι ℝ) :=
  (inferInstance : PseudoMetricSpace (Matrix ι ι ℝ)).toUniformSpace.toTopologicalSpace
def coefficient (b : OrthonormalBasis ι ℝ E) (u : E → ℝ) (v x : E) : E →L[ℝ] E :=
  HessianTrace.fromMatrix b (LogDetSegment.meanInverse (matrixHessian b u x) (matrixHessian b u (x+v)))

end


open Set Metric InnerProductSpace
open scoped ContDiff
variable {E : Type*} {J : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

end MomentQuotient



namespace MomentQuotient
open Set Metric InnerProductSpace
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_2 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_2 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_3 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instTopologicalSpaceMatrixReal_solutions_1 : TopologicalSpace (Matrix ι ι ℝ) :=
  (inferInstance : PseudoMetricSpace (Matrix ι ι ℝ)).toUniformSpace.toTopologicalSpace

end MomentQuotient


namespace CoefficientTrace
open scoped InnerProductSpace
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedSpaceRealContinuousLinearMapId_solutions_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1_r3f7403_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
def bilinear (b:OrthonormalBasis ι ℝ E) :
    (E→L[ℝ]E→L[ℝ]ℝ) →L[ℝ] (E→L[ℝ]E) →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ (fun (H:E→L[ℝ]E→L[ℝ]ℝ) (A:E→L[ℝ]E) => trace b H A)
    (by intros; simp only [trace,add_apply,Finset.sum_add_distrib])
    (by intros; simp only [trace,_root_.smul_apply,smul_eq_mul,Finset.mul_sum])
    (by intros; simp only [trace,add_apply,map_add,Finset.sum_add_distrib])
    (by intros; simp only [trace,_root_.smul_apply,map_smul,smul_eq_mul,Finset.mul_sum])).mkContinuous₂
      (Fintype.card ι) (norm_bound b)
end CoefficientTrace

namespace LinearSchauder
open Set Metric InnerProductSpace MomentQuotient
open scoped ContDiff InnerProductSpace
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

end LinearSchauder
end



noncomputable section
namespace HolderJets
open Set Metric
open scoped ContDiff
universe u
variable {E F G H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

def Local (f:E→F) : Prop := ∀c:E,∃a r:ℝ,0<a ∧ a<1 ∧ 0<r ∧
  HolderControl.Controlled a (closedBall c r) (fun _:Unit => f)

def Regular (n:ℕ) {F:Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (f:E→F) : Prop :=
  match n with
  | 0 => Continuous f ∧ Local f
  | n+1 => Differentiable ℝ f ∧ Regular n (fderiv ℝ f)
termination_by structural n

end HolderJets


namespace LinearSchauder
open Set Metric HolderJets
open scoped ContDiff InnerProductSpace
variable {E:Type} {ι:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_2 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_2 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_3 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_3 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_4 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_4 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_5 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_5 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

end LinearSchauder


namespace MomentSchauder
open Set Metric Matrix InnerProductSpace HolderJets MomentQuotient
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
variable {E:Type} {ι:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instTopologicalSpaceMatrixReal_solutions : TopologicalSpace (Matrix ι ι ℝ) :=
  (inferInstance : PseudoMetricSpace (Matrix ι ι ℝ)).toUniformSpace.toTopologicalSpace
local notation "Mat" => Matrix ι ι ℝ

def scalarToVector : (E→L[ℝ]E→L[ℝ]ℝ) →L[ℝ] (E→L[ℝ]E) :=
  ContinuousLinearMap.compL ℝ E (E→L[ℝ]ℝ) E
    (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

def scalarToMatrix (b:OrthonormalBasis ι ℝ E) : (E→L[ℝ]E→L[ℝ]ℝ) →L[ℝ] Mat :=
  (HessianTrace.fromMatrix b).symm.toContinuousLinearMap.comp scalarToVector

end MomentSchauder


namespace CompactMomentVariational
open Set Metric Matrix Filter MeasureTheory HolderJets
open scoped InnerProductSpace NNReal ENNReal ContDiff Matrix.Norms.Elementwise
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local instance instNormedAddCommGroupContinuousLinearMapRealIdEuclideanSpace_solutions : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdEuclideanSpace_solutions : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealIdEuclideanSpace_solutions_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdEuclideanSpace_solutions_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

end CompactMomentVariational
end



noncomputable section
namespace MomentCoordinatesBridge
open MeasureTheory Set Matrix MomentCoordinates
open scoped InnerProductSpace ContDiff
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => (ι → ℝ)
def coord : E ≃L[ℝ] P := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
def ob : OrthonormalBasis ι ℝ E := EuclideanSpace.basisFun ι ℝ
end MomentCoordinatesBridge


end

end OAI
end


