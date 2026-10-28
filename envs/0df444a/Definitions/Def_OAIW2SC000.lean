-- Prove2me | Definitions.Def_OAIW2SC000
-- name    : OAIW2SC000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T02:32:45.207973+00:00
-- url     : https://prove2.me/theorems/331e1d49-361b-43f0-9fc4-12b9b9c47232
-- title:
--   Definitions bundle OAIW2SC000 of the split of OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.StructuralCrouzeixReference.challenge`, carved from OpenAI's openai/math development (OpenAI, *The complete Crouzeix theorem: optimal similarity and a common positive boundary representation*, OpenAI Math Release, September 23, 2026, result family 325, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 309 declarations of OpenAI's Lean: 118 definitions, 4 inductive types or structures and 187 theorems. The definitions and types are `OAI.CompleteCrouzeix.AdmissibleDomain`, `OAI.CompleteCrouzeix.AdmissibleDomain.G`, `OAI.CompleteCrouzeix.AdmissibleDomain.analyticRangeMaximum`, `OAI.CompleteCrouzeix.AdmissibleDomain.cauchy`, `OAI.CompleteCrouzeix.AdmissibleDomain.kernel`, `OAI.CompleteCrouzeix.AdmissibleDomain.positiveDensity`, `OAI.CompleteCrouzeix.AdmissibleDomain.resolventField`, `OAI.CompleteCrouzeix.AdmissibleDomain.trace`, `OAI.CompleteCrouzeix.AdmissibleDomain.ψ`, `OAI.CompleteCrouzeix.AnalyticBidiskKernel`, `OAI.CompleteCrouzeix.AnalyticBidiskKernel.circleB`, `OAI.CompleteCrouzeix.AnalyticBidiskKernel.kernel`, `OAI.CompleteCrouzeix.AnalyticBidiskKernel.matrixM`, `OAI.CompleteCrouzeix.AnalyticBidiskKernel.rowB`, `OAI.CompleteCrouzeix.AnalyticBidiskKernel.rowKernel`, `OAI.CompleteCrouzeix.AnalyticBidiskKernel.scalarM`, `OAI.CompleteCrouzeix.AnalyticBidiskKernel.toMarkovKernel`, `OAI.CompleteCrouzeix.CircleL2`, `OAI.CompleteCrouzeix.FourierResolution`, `OAI.CompleteCrouzeix.FourierResolution.cauchy`, `OAI.CompleteCrouzeix.FourierResolution.cauchyAdjoint`, `OAI.CompleteCrouzeix.HSMatrix`, `OAI.CompleteCrouzeix.HermitianMatrix`, `OAI.CompleteCrouzeix.LocalAnalyticBoundary`, `OAI.CompleteCrouzeix.LocalClosedAnalyticBoundary`, `OAI.CompleteCrouzeix.MarkovKernel`, `OAI.CompleteCrouzeix.MarkovKernel.applyFun`, `OAI.CompleteCrouzeix.MarkovKernel.applyLp`, `OAI.CompleteCrouzeix.MarkovKernel.toCLM`, `OAI.CompleteCrouzeix.MatrixCircleL2`, `OAI.CompleteCrouzeix.MetricDualSpace`, `OAI.CompleteCrouzeix.NormalizedUnivalent`, `OAI.CompleteCrouzeix.StrictPositive`, `OAI.CompleteCrouzeix.VectorL2`, `OAI.CompleteCrouzeix.actualExteriorKernel`, `OAI.CompleteCrouzeix.analyticCircleTrace`, `OAI.CompleteCrouzeix.baseAmplification`, `OAI.CompleteCrouzeix.baseMatrixHom`, `OAI.CompleteCrouzeix.basisProjection`, `OAI.CompleteCrouzeix.basisResolution` and 82 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `NumericalRange_BoundaryCalculus`, `NumericalRange_BoundaryNormals`, `NumericalRange_BoundaryRepresentation`, `NumericalRange_CauchyEvaluation`, `NumericalRange_CauchyProjection`, `NumericalRange_CircleIntegrals`, `NumericalRange_CompleteResolvent`, `NumericalRange_ConformalGluing`, `NumericalRange_ConformalWinding`, `NumericalRange_ConvexBarrier`, `NumericalRange_ConvexExterior`, `NumericalRange_DensityAdjoints`, `NumericalRange_DensityIdentification`, `NumericalRange_DensityTransport`, `NumericalRange_DilationDensity`, `NumericalRange_DiskCalculus`, `NumericalRange_DiskMapping`, `NumericalRange_DomainCalculus`, `NumericalRange_DualSeparation`, `NumericalRange_ExteriorKernel`, `NumericalRange_ExteriorProjection`, `NumericalRange_FourierExtension`, `NumericalRange_FourierResolution`, `NumericalRange_HerglotzReflection`, `NumericalRange_HilbertSchmidt`, `NumericalRange_HolomorphicEvaluation`, `NumericalRange_MarkovOperator`, `NumericalRange_MetricFeasibility`, `NumericalRange_OrderedDensities`, `NumericalRange_OrderedMultiplication`, `NumericalRange_OuterNeighborhood`, `NumericalRange_PoissonBoundary`, `NumericalRange_PolynomialCalculus`, `NumericalRange_PositiveDensity`, `NumericalRange_PulledDensity`, `NumericalRange_TestingAlgebra`, `NumericalRange_UnitaryRealization`, `StructuralCrouzeix_ExteriorSupport`, `StructuralCrouzeix_GeometryBasics`, `StructuralCrouzeix_Main`, `StructuralCrouzeix_SharedDensity`, `StructuralCrouzeix_SharedMaximum`.
--
--   **Imports.** It imports the published bundle `Def_StructuralCrouzeix`.
--
--   **Imported by** (directly, in this split): the statements `OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound`, `OAI.CompleteCrouzeix.AdmissibleDomain.ordered_modules`, `OAI.CompleteCrouzeix.AdmissibleDomain.positive_ordered`, `OAI.CompleteCrouzeix.AdmissibleDomain.resolvent_density_identification` and `OAI.StructuralCrouzeix.optimal_metric_bundle`; the proofs of `OAI.CompleteCrouzeix.AdmissibleDomain.extremal_condition_bound`, `OAI.CompleteCrouzeix.AdmissibleDomain.ordered_modules`, `OAI.CompleteCrouzeix.AdmissibleDomain.positive_ordered`, `OAI.CompleteCrouzeix.AdmissibleDomain.resolvent_density_identification`, `OAI.StructuralCrouzeixReference.challenge` and `OAI.StructuralCrouzeix.optimal_metric_bundle`.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_StructuralCrouzeix

section
-- module Solutions.OAIW2_StructCrouzeix.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
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
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PoissonBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
section

def poissonExtension (f : ℂ → ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (fun t => poissonKernel 0 w t * f t) 0 1

def diskDirichlet (f : ℂ → ℝ) (w : ℂ) : ℝ :=
  if ‖w‖ < 1 then poissonExtension f w else f w

end

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate

def upperDisk : Set ℂ := ball 0 1 ∩ {z | 0 < z.im}
def upperClosedDisk : Set ℂ := closedBall 0 1 ∩ {z | 0 ≤ z.im}

def oddBoundary (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  if 0 ≤ z.im then u z else -u (conj z)


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HerglotzReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
section

def herglotzExtension (f : ℂ → ℝ) (w : ℂ) : ℂ :=
  Real.circleAverage (fun t => herglotzRieszKernel 0 w t • (f t : ℂ)) 0 1


open Set Filter Metric Complex
open scoped Topology

def upperLogNorm (g : ℂ → ℂ) (z : ℂ) : ℝ :=
  if z.im = 0 then 0 else Real.log ‖g z‖

end

open Set Filter Metric
open scoped Topology


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConformalGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_1 u_2

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology

open Set Filter Metric Complex
open scoped Topology

open Set Filter Metric Complex
open scoped Topology

open Set Metric Filter Topology

def NormalizedUnivalent (U : Set ℂ) (a : ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ InjOn f U ∧ MapsTo f U (ball 0 1) ∧ f a = 0


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DiskMapping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology

open Set Metric Filter Topology
section

def diskAut (b z : ℂ) : ℂ := (z-b)/(1-star b*z)

end

open Set Filter Topology Complex

open Complex


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConvexBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
namespace CompleteCrouzeix

section

section


open Set Filter Metric Complex
open scoped Topology

def LocalAnalyticBoundary (U : Set ℂ) (p : ℂ) : Prop :=
  ∃ χ : ℂ → ℂ, χ 0 = p ∧ AnalyticAt ℂ χ 0 ∧ deriv χ 0 ≠ 0 ∧
    (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ U ↔ 0 < z.im) ∧
    (∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier U)

end

open Set Filter Metric Complex
open scoped Topology
namespace DiskCoordinate
variable {U : Set ℂ} {a : ℂ} (D : DiskCoordinate U a)

lemma closure_maps : MapsTo D.toDisk (closure U) (closedBall 0 1) := by
  intro z hz
  have he := mem_closure_image (D.analytic_to z (D.closure_subset hz)).continuousAt hz
  rwa [D.image_domain,closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at he

lemma inverse_ball (w : ℂ) (hw : w ∈ ball 0 1) : D.fromDisk w ∈ U := by
  obtain ⟨z,hz,he⟩ := D.image_domain.symm ▸ hw
  rw [← he,D.left_inverse z (D.closure_subset (subset_closure hz))]
  exact hz

lemma inverse_image_ball : D.fromDisk '' ball 0 1 = U := by
  apply Subset.antisymm
  · rintro z ⟨w,hw,rfl⟩; exact D.inverse_ball w hw
  · intro z hz
    refine ⟨D.toDisk z,?_,D.left_inverse z (D.closure_subset (subset_closure hz))⟩
    exact D.image_domain ▸ mem_image_of_mem D.toDisk hz

lemma inverse_closed (w : ℂ) (hw : w ∈ closedBall 0 1) : D.fromDisk w ∈ closure U := by
  have he := mem_closure_image (D.analytic_from w (D.closedDisk_subset hw)).continuousAt
    (show w ∈ closure (ball (0 : ℂ) 1) by rwa [closure_ball (0 : ℂ) one_ne_zero])
  rwa [D.inverse_image_ball] at he

lemma inverse_mem_domain_iff {w : ℂ} (hw : w ∈ D.toDisk '' D.outer) :
    D.fromDisk w ∈ U ↔ w ∈ ball 0 1 := by
  constructor
  · intro h
    have he := D.image_domain ▸ mem_image_of_mem D.toDisk h
    rwa [D.right_inverse w hw] at he
  · exact D.inverse_ball w

lemma inverse_sphere_frontier (hU : IsOpen U) :
    D.fromDisk '' sphere 0 1 = frontier U := by
  apply Subset.antisymm
  · rintro z ⟨w,hw,rfl⟩
    rw [hU.frontier_eq]
    have hwc : w ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hw
    refine ⟨D.inverse_closed w hwc,?_⟩
    intro h
    have he := (D.inverse_mem_domain_iff (D.closedDisk_subset hwc)).mp h
    exact (not_lt_of_ge (le_of_eq (mem_sphere_zero_iff_norm.mp hw).symm)) (mem_ball_zero_iff.mp he)
  · intro z hz
    have hzo := D.closure_subset hz.1
    refine ⟨D.toDisk z,?_,D.left_inverse z hzo⟩
    rw [mem_sphere_zero_iff_norm]
    apply le_antisymm (mem_closedBall_zero_iff.mp (D.closure_maps hz.1))
    by_contra hn
    have ht : D.toDisk z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (lt_of_not_ge hn)
    have hu := D.inverse_ball (D.toDisk z) ht
    rw [D.left_inverse z hzo] at hu
    exact (hU.frontier_eq ▸ hz).2 hu
end DiskCoordinate
end

open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConvexExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_23 u_24 u_25

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open Set Filter Metric Complex
open scoped Topology
section

def invertedExterior (K : Set ℂ) (a : ℂ) : Set ℂ :=
  {w | w = 0 ∨ a+w⁻¹ ∉ K}

@[simp] lemma zero_mem_invertedExterior (K : Set ℂ) (a : ℂ) :
    0 ∈ invertedExterior K a := Or.inl rfl

end

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_BoundaryNormals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_26 u_27

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology

section

def exteriorCorrection (G : ℂ → ℂ) (w t : ℂ) : ℂ :=
  t * deriv (dslope G w) t / dslope G w t

lemma analyticOnNhd_dslope {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) {w : ℂ} (hw : w ∈ U) :
    AnalyticOnNhd ℂ (dslope G w) U := by
  apply (differentiableOn_dslope (hU.mem_nhds hw)).mpr hG.differentiableOn |>.analyticOnNhd hU

lemma dslope_ne_zero_of_injOn {G : ℂ → ℂ} {U : Set ℂ}
    (hi : InjOn G U) {w t : ℂ} (hw : w ∈ U) (ht : t ∈ U)
    (hd : deriv G w ≠ 0) : dslope G w t ≠ 0 := by
  by_cases htw : t = w
  · subst t; simpa using hd
  · rw [dslope_of_ne _ htw, slope_def_field]
    exact div_ne_zero (sub_ne_zero.mpr (fun he => htw (hi ht hw he)))
      (sub_ne_zero.mpr htw)


open Set Filter Metric Complex
open scoped Topology

end

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

lemma complex_real_decomposition {N : ℂ} (hN : N ≠ 0) (z : ℂ) :
    z = (z/N).re • N + (z/N).im • (I*N) := by
  rw [Complex.real_smul,Complex.real_smul]
  calc
    z = (z/N)*N := (div_mul_cancel₀ z hN).symm
    _ = _ := by
      conv_lhs => rw [← re_add_im (z/N)]
      simp only [div_eq_mul_inv]
      ring

lemma real_linear_normal {L : ℂ →L[ℝ] ℝ} {N : ℂ} (hN : N ≠ 0)
    (htan : L (I*N) = 0) (z : ℂ) :
    L z = (L N / ‖N‖^2)*(conj N*z).re := by
  have he := congrArg L (complex_real_decomposition hN z)
  rw [map_add,map_smul,map_smul,htan,smul_zero,add_zero] at he
  rw [he,smul_eq_mul]
  rw [Complex.div_re,Complex.normSq_eq_norm_sq]
  simp only [mul_re,conj_re,conj_im,neg_mul,sub_neg_eq_add]
  ring


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_OuterNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_28 u_29

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology

section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate

lemma exteriorCoordinate_analytic {U : Set ℂ} (E : ExteriorCoordinate U) :
    AnalyticOnNhd ℂ (exteriorMap E.leading E.constant E.regular)
      {t | E.radius⁻¹ < ‖t‖} := by
  intro t ht
  have hr : 0 < E.radius := zero_lt_one.trans E.radius_gt
  have ht0 : t ≠ 0 := by intro he; simp only [mem_ofPred_eq,he,norm_zero] at ht; exact (not_lt_of_ge (inv_nonneg.mpr hr.le)) ht
  have hi : t⁻¹ ∈ ball (0:ℂ) E.radius := by
    rw [mem_ball_zero_iff,norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr ht0) hr).mpr ht
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).add
    ((E.analytic_regular t⁻¹ hi).comp (analyticAt_id.inv ht0))

end

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

structure AdmissibleDomain where
  domain : Set ℂ
  isOpen : IsOpen domain
  convex : Convex ℝ domain
  compact_closure : IsCompact (closure domain)
  base : ℂ
  base_mem : base ∈ domain
  interior : DiskCoordinate domain base
  exterior : ExteriorCoordinate domain
  support : ∀ t ∈ sphere (0:ℂ) 1, ∀ z ∈ closure domain,
    0 ≤ (conj (t*deriv (exteriorMap exterior.leading exterior.constant exterior.regular) t)*
      (exteriorMap exterior.leading exterior.constant exterior.regular t-z)).re


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ExteriorKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
namespace CompleteCrouzeix

theorem exteriorCorrection_eq {G : ℂ → ℂ} {w t : ℂ}
    (htw : t ≠ w) (hG : DifferentiableAt ℂ G t) (hne : G t ≠ G w) :
    exteriorCorrection G w t =
      t * deriv G t / (G t - G w) - t / (t-w) := by
  have he := dslope_eventuallyEq_slope_of_ne G htw
  have hd : deriv (dslope G w) t =
      (deriv G t * (t-w) - (G t-G w)) / (t-w)^2 := by
    rw [he.deriv_eq]
    rw [show slope G w = (fun z => (G z-G w)/(z-w)) from
      funext (fun z => slope_def_field G w z)]
    simpa only [id_eq, mul_one] using
      ((hG.hasDerivAt.sub_const (G w)).fun_div
        ((hasDerivAt_id t).sub_const w) (sub_ne_zero.mpr htw)).deriv
  rw [exteriorCorrection, hd, dslope_of_ne _ htw, slope_def_field]
  field_simp

lemma exteriorCorrection_eq_left {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ z ∈ U, deriv G z ≠ 0) {w t : ℂ} (hw : w ∈ U) (ht : t ∈ U) :
    exteriorCorrection G w t =
      -t * dslope (fun z => deriv G t / dslope G t z) t w := by
  have hdt := hd t ht
  have hq := analyticOnNhd_dslope hU hG ht
  by_cases hwt : w = t
  · subst w
    rw [dslope_same]
    have he : deriv (fun z => deriv G t / dslope G t z) t =
        -(deriv G t) * deriv (dslope G t) t / (deriv G t)^2 := by
      simpa using ((hasDerivAt_const t (deriv G t)).fun_div
        (hq t ht).differentiableAt.hasDerivAt (by simpa using hdt)).deriv
    rw [he, exteriorCorrection, dslope_same]
    field_simp
  · rw [exteriorCorrection_eq (Ne.symm hwt) (hG t ht).differentiableAt
      (fun he => hwt (hi hw ht he.symm)), dslope_of_ne _ hwt,
      slope_def_field, dslope_same, div_self hdt, dslope_of_ne _ hwt,
      slope_def_field]
    have hne : G w - G t ≠ 0 := sub_ne_zero.mpr (fun he => hwt (hi hw ht he))
    have hdist : w-t ≠ 0 := sub_ne_zero.mpr hwt
    have hne' : G t - G w ≠ 0 := sub_ne_zero.mpr (fun he => hwt (hi hw ht he.symm))
    have hdist' : t-w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwt)
    field_simp
    ring

theorem exteriorCorrection_analytic_left {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) {t : ℂ} (ht : t ∈ U) :
    AnalyticOnNhd ℂ (fun w => exteriorCorrection G w t) U := by
  have hq := analyticOnNhd_dslope hU hG ht
  have hh : AnalyticOnNhd ℂ (fun z => deriv G t / dslope G t z) U := by
    intro z hz
    exact analyticAt_const.div (hq z hz)
      (dslope_ne_zero_of_injOn hi ht hz (hd t ht))
  have hs := analyticOnNhd_dslope hU hh ht
  intro w hw
  apply (analyticAt_const.mul (hs w hw)).congr
  filter_upwards [hU.mem_nhds hw] with z hz
  exact (exteriorCorrection_eq_left hU hG hi hd hz ht).symm

lemma dslope_comm (f : ℂ → ℂ) (x y : ℂ) : dslope f x y = dslope f y x := by
  by_cases h : x = y
  · subst y; rfl
  · rw [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ h, slope_def_field,
      slope_def_field, div_eq_div_iff (sub_ne_zero.mpr (Ne.symm h)) (sub_ne_zero.mpr h)]
    ring

lemma deriv_dslope_eq_iterated {H : ℂ → ℂ} {x y : ℂ}
    (hH : DifferentiableAt ℂ H y) :
    deriv (dslope H x) y = dslope (dslope H y) y x := by
  by_cases h : x = y
  · subst x; simp
  · rw [dslope_of_ne _ h, slope_def_field, dslope_same,
      dslope_of_ne _ h, slope_def_field]
    rw [(dslope_eventuallyEq_slope_of_ne H (Ne.symm h)).deriv_eq]
    rw [show slope H x = (fun z => (H z-H x)/(z-x)) from
      funext (fun z => slope_def_field H x z)]
    have hd := ((hH.hasDerivAt.sub_const (H x)).fun_div
      ((hasDerivAt_id y).sub_const x) (sub_ne_zero.mpr (Ne.symm h))).deriv
    simp only [id_eq, mul_one] at hd
    rw [hd]
    have hxy : x-y ≠ 0 := sub_ne_zero.mpr h
    have hyx : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    field_simp
    ring

def exteriorDividedDifference (a : ℂ) (h : ℂ → ℂ) (x y : ℂ) : ℂ :=
  a-x*y*dslope h x y

def reciprocalCorrection (a : ℂ) (h : ℂ → ℂ) (x y : ℂ) : ℂ :=
  x*y*dslope (dslope (fun z => z*h z) y) y x / exteriorDividedDifference a h x y

@[simp] lemma reciprocalCorrection_zero_left (a : ℂ) (h : ℂ → ℂ) (y : ℂ) :
    reciprocalCorrection a h 0 y = 0 := by simp [reciprocalCorrection]

@[simp] lemma reciprocalCorrection_zero_right (a : ℂ) (h : ℂ → ℂ) (x : ℂ) :
    reciprocalCorrection a h x 0 = 0 := by simp [reciprocalCorrection]

lemma reciprocalCorrection_eq_deriv {a : ℂ} {h : ℂ → ℂ} {x y : ℂ}
    (hy : DifferentiableAt ℂ h y) :
    reciprocalCorrection a h x y =
      x*y*deriv (dslope (fun z => z*h z) x) y / exteriorDividedDifference a h x y := by
  have hh : DifferentiableAt ℂ (fun z => z*h z) y := by fun_prop
  rw [deriv_dslope_eq_iterated hh]
  rfl

lemma reciprocalCorrection_analytic_left {a : ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hh : AnalyticOnNhd ℂ h U)
    (hne : ∀ x ∈ U, ∀ y ∈ U, exteriorDividedDifference a h x y ≠ 0)
    {y : ℂ} (hy : y ∈ U) :
    AnalyticOnNhd ℂ (fun x => reciprocalCorrection a h x y) U := by
  have hh' : AnalyticOnNhd ℂ (fun z => z*h z) U := analyticOnNhd_id.mul hh
  have hs := analyticOnNhd_dslope hU (analyticOnNhd_dslope hU hh' hy) hy
  have hq := analyticOnNhd_dslope hU hh hy
  intro x hx
  have hqa : AnalyticAt ℂ (fun x => exteriorDividedDifference a h x y) x := by
    have he : (fun x => exteriorDividedDifference a h x y) =
        (fun x => a-x*y*dslope h y x) := by
      funext z; rw [exteriorDividedDifference, dslope_comm h z y]
    rw [he]
    exact analyticAt_const.sub ((analyticAt_id.mul analyticAt_const).mul (hq x hx))
  exact ((analyticAt_id.mul analyticAt_const).mul (hs x hx)).div hqa (hne x hx y hy)

lemma reciprocalCorrection_analytic_right {a : ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hh : AnalyticOnNhd ℂ h U)
    (hne : ∀ x ∈ U, ∀ y ∈ U, exteriorDividedDifference a h x y ≠ 0)
    {x : ℂ} (hx : x ∈ U) :
    AnalyticOnNhd ℂ (reciprocalCorrection a h x) U := by
  have hh' : AnalyticOnNhd ℂ (fun z => z*h z) U := analyticOnNhd_id.mul hh
  have hs := analyticOnNhd_dslope hU hh' hx
  have hq := analyticOnNhd_dslope hU hh hx
  intro y hy
  have hqa : AnalyticAt ℂ (exteriorDividedDifference a h x) y :=
    analyticAt_const.sub ((analyticAt_const.mul analyticAt_id).mul (hq y hy))
  apply (((analyticAt_const.mul analyticAt_id).mul (hs.deriv y hy)).div hqa
    (hne x hx y hy)).congr
  filter_upwards [hU.mem_nhds hy] with z hz
  exact (reciprocalCorrection_eq_deriv (hh z hz).differentiableAt).symm

lemma hasDerivAt_exteriorMap {a b : ℂ} {h : ℂ → ℂ} {t : ℂ}
    (ht : t ≠ 0) (hh : DifferentiableAt ℂ h t⁻¹) :
    HasDerivAt (exteriorMap a b h) (a - (t^2)⁻¹ * deriv h t⁻¹) t := by
  convert! (((hasDerivAt_id t).const_mul a).add_const b).fun_add
      (hh.hasDerivAt.comp t (hasDerivAt_inv ht)) using 1
  ring

lemma dslope_exteriorMap {a b : ℂ} {h : ℂ → ℂ} {x y : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hh : DifferentiableAt ℂ h x) :
    dslope (exteriorMap a b h) x⁻¹ y⁻¹ = exteriorDividedDifference a h x y := by
  by_cases hxy : x = y
  · subst y
    rw [dslope_same, (hasDerivAt_exteriorMap (inv_ne_zero hx) (by simpa using hh)).deriv]
    simp [exteriorDividedDifference, sq]
  · have hyx : y⁻¹ ≠ x⁻¹ := fun he => hxy (inv_injective he).symm
    rw [dslope_of_ne _ hyx, slope_def_field, exteriorDividedDifference,
      dslope_of_ne _ (Ne.symm hxy), slope_def_field]
    simp only [exteriorMap, inv_inv]
    have hdist : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have hinvdist : y⁻¹-x⁻¹ ≠ 0 := sub_ne_zero.mpr hyx
    field_simp
    ring

lemma dividedDifference_ne_zero {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hR : 0 < R) :
    ∀ x ∈ ball (0 : ℂ) R, ∀ y ∈ ball (0 : ℂ) R,
      exteriorDividedDifference a h x y ≠ 0 := by
  intro x hx y hy
  by_cases hx0 : x = 0
  · subst x; simpa [exteriorDividedDifference] using ha
  by_cases hy0 : y = 0
  · subst y; simpa [exteriorDividedDifference] using ha
  have hix : R⁻¹ < ‖x⁻¹‖ := by
    rw [norm_inv]
    exact inv_lt_inv₀ hR (norm_pos_iff.mpr hx0) |>.mpr (by simpa using hx)
  have hiy : R⁻¹ < ‖y⁻¹‖ := by
    rw [norm_inv]
    exact inv_lt_inv₀ hR (norm_pos_iff.mpr hy0) |>.mpr (by simpa using hy)
  rw [← dslope_exteriorMap hx0 hy0 (hh x hx).differentiableAt]
  exact dslope_ne_zero_of_injOn hi hix hiy (hd _ hix)

lemma dslope_id_mul {h : ℂ → ℂ} {x : ℂ} (hh : DifferentiableAt ℂ h x) :
    dslope (fun z => z*h z) x = fun z => z*dslope h x z+h x := by
  funext y
  by_cases hy : y = x
  · subst y
    simp only [dslope_same]
    have hd := (hasDerivAt_id x).fun_mul hh.hasDerivAt
    simpa only [id_eq, one_mul, mul_one, add_comm] using hd.deriv
  · rw [dslope_of_ne _ hy, dslope_of_ne _ hy, slope_def_field, slope_def_field]
    have hdist : y-x ≠ 0 := sub_ne_zero.mpr hy
    field_simp
    ring

lemma reciprocalCorrection_eq_logDeriv {a : ℂ} {h : ℂ → ℂ} {x y : ℂ}
    (hx : DifferentiableAt ℂ h x) (hy : DifferentiableAt ℂ h y)
    (hs : DifferentiableAt ℂ (dslope h x) y) :
    reciprocalCorrection a h x y = x*y*(dslope h x y+y*deriv (dslope h x) y) /
      exteriorDividedDifference a h x y := by
  rw [reciprocalCorrection_eq_deriv hy, dslope_id_mul hx]
  have hd := ((hasDerivAt_id y).fun_mul hs.hasDerivAt).add_const (h x)
  have he : deriv (fun z => z*dslope h x z+h x) y =
      dslope h x y+y*deriv (dslope h x) y := by simpa using hd.deriv
  rw [he]

theorem exteriorCorrection_eq_reciprocal {a b : ℂ} {h : ℂ → ℂ} {x y : ℂ}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : DifferentiableAt ℂ h x) (hy : DifferentiableAt ℂ h y)
    (hs : DifferentiableAt ℂ (dslope h x) y) :
    exteriorCorrection (exteriorMap a b h) x⁻¹ y⁻¹ = reciprocalCorrection a h x y := by
  have he : dslope (exteriorMap a b h) x⁻¹ =ᶠ[𝓝 y⁻¹]
      fun t => exteriorDividedDifference a h x t⁻¹ := by
    filter_upwards [eventually_ne_nhds (inv_ne_zero hy0)] with t ht
    simpa using dslope_exteriorMap (a := a) (b := b) hx0 (inv_ne_zero ht) hx
  have hq : HasDerivAt (exteriorDividedDifference a h x)
      (-x*(dslope h x y+y*deriv (dslope h x) y)) y := by
    have hd := (((hasDerivAt_id y).fun_mul hs.hasDerivAt).const_mul x).const_sub a
    convert! hd using 1
    · funext z; simp [exteriorDividedDifference, mul_assoc]
    · simp only [id_eq, one_mul]; ring
  have hq' : HasDerivAt (exteriorDividedDifference a h x)
      (-x*(dslope h x y+y*deriv (dslope h x) y)) y⁻¹⁻¹ := by
    simpa only [inv_inv] using hq
  have hi := hq'.comp y⁻¹ (hasDerivAt_inv (inv_ne_zero hy0))
  have hd : deriv (dslope (exteriorMap a b h) x⁻¹) y⁻¹ =
      x*(dslope h x y+y*deriv (dslope h x) y)*y^2 := by
    rw [he.deriv_eq]
    convert! hi.deriv using 1
    simp only [inv_pow, inv_inv]
    ring
  rw [exteriorCorrection, hd, dslope_exteriorMap hx0 hy0 hx,
    reciprocalCorrection_eq_logDeriv hx hy hs]
  congr 1
  field_simp

theorem continuousOn_of_analytic_left_offDiagonal {B : ℂ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hB : ∀ y ∈ U, AnalyticOnNhd ℂ (fun x => B x y) U)
    (hc : ContinuousOn (Function.uncurry B)
      {p : ℂ × ℂ | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2}) :
    ContinuousOn (Function.uncurry B) (U ×ˢ U) := by
  have ho : IsOpen {p : ℂ × ℂ | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2} := by
    exact (hU.preimage continuous_fst).inter
      ((hU.preimage continuous_snd).inter (isOpen_ne_fun continuous_fst continuous_snd))
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  by_cases hxy : x = y
  · subst y
    obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    let r := ε / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrc : closedBall x r ⊆ U := by
      intro z hz
      apply hεU
      have hz' : dist z x ≤ r := hz
      exact lt_of_le_of_lt hz' (by dsimp [r]; linarith)
    let V := ball x (r/2) ×ˢ ball x (r/2)
    have hxV : (x,x) ∈ V := by simp [V, hr]
    have hVU : ∀ p : V, p.val.1 ∈ U ∧ p.val.2 ∈ U := by
      intro p
      have hs : ball x (r/2) ⊆ closedBall x r :=
        (ball_subset_ball (by linarith : r/2 ≤ r)).trans ball_subset_closedBall
      exact ⟨hrc (hs p.property.1),hrc (hs p.property.2)⟩
    have hcircleU (θ : ℝ) : circleMap x r θ ∈ U :=
      hrc (sphere_subset_closedBall (circleMap_mem_sphere x hr.le θ))
    have hcircle_ne (p : V) (θ : ℝ) :
        circleMap x r θ ≠ p.val.1 ∧ circleMap x r θ ≠ p.val.2 := by
      have hz : dist (circleMap x r θ) x = r := (circleMap_mem_sphere x hr.le θ)
      constructor
      · intro he
        rw [he] at hz
        have hp := p.property.1
        change dist p.val.1 x < r/2 at hp
        linarith
      · intro he
        rw [he] at hz
        have hp := p.property.2
        change dist p.val.2 x < r/2 at hp
        linarith
    have hk : Continuous (fun q : V × ℝ =>
        ((circleMap x r q.2-x)/(circleMap x r q.2-q.1.val.1)) *
          B (circleMap x r q.2) q.1.val.2) := by
      apply Continuous.mul
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · intro q
          exact sub_ne_zero.mpr (hcircle_ne q.1 q.2).1
      · apply hc.comp_continuous (f := fun q : V × ℝ =>
          (circleMap x r q.2,q.1.val.2))
        · fun_prop
        · intro q
          exact ⟨hcircleU q.2,(hVU q.1).2,(hcircle_ne q.1 q.2).2⟩
    have hi : Continuous (fun p : V =>
        Real.circleAverage (fun z => ((z-x)/(z-p.val.1))*B z p.val.2) x r) := by
      exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hk 0 (2*Real.pi)).const_smul _
    have he (p : V) :
        Real.circleAverage (fun z => ((z-x)/(z-p.val.1))*B z p.val.2) x r =
          B p.val.1 p.val.2 := by
      have ha := (hB p.val.2 (hVU p).2).mono hrc
      have hd : DiffContOnCl ℂ (fun z => B z p.val.2) (ball x |r|) := by
        constructor
        · rw [abs_of_pos hr]
          exact ha.differentiableOn.mono ball_subset_closedBall
        · simpa only [abs_of_pos hr, closure_ball x (ne_of_gt hr)] using ha.continuousOn
      have hp : p.val.1 ∈ ball x |r| := by
        rw [abs_of_pos hr]
        exact ball_subset_ball (by linarith : r/2 ≤ r) p.property.1
      exact hd.circleAverage_smul_div hp
    have hv : ContinuousOn (Function.uncurry B) V := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hi.congr he
    exact (hv.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds hxV)).continuousWithinAt
  · exact ((hc (x,y) ⟨hx,hy,hxy⟩).continuousAt
      (ho.mem_nhds ⟨hx,hy,hxy⟩)).continuousWithinAt

theorem exteriorCorrection_continuousOn {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) :
    ContinuousOn (Function.uncurry (exteriorCorrection G)) (U ×ˢ U) := by
  apply continuousOn_of_analytic_left_offDiagonal hU
    (fun t ht => exteriorCorrection_analytic_left hU hG hi hd ht)
  let V := {p : ℂ × ℂ | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2}
  have hg1 : ContinuousOn (fun p : ℂ × ℂ => G p.1) V :=
    hG.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have hg2 : ContinuousOn (fun p : ℂ × ℂ => G p.2) V :=
    hG.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have hd2 : ContinuousOn (fun p : ℂ × ℂ => deriv G p.2) V :=
    hG.deriv.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have hc : ContinuousOn (fun p : ℂ × ℂ =>
      p.2 * deriv G p.2 / (G p.2-G p.1) - p.2/(p.2-p.1)) V := by
    apply ContinuousOn.sub
    · exact (continuousOn_snd.mul hd2).div (hg2.sub hg1)
        (fun p hp => sub_ne_zero.mpr (fun he => hp.2.2 (hi hp.1 hp.2.1 he.symm)))
    · exact continuousOn_snd.div (continuousOn_snd.sub continuousOn_fst)
        (fun p hp => sub_ne_zero.mpr (Ne.symm hp.2.2))
  apply hc.congr
  intro p hp
  exact exteriorCorrection_eq (Ne.symm hp.2.2) (hG p.2 hp.2.1).differentiableAt
    (fun he => hp.2.2 (hi hp.1 hp.2.1 he.symm))

def exteriorMarkovKernel (G : ℂ → ℂ) (w t : Circle) : ℝ :=
  1 + 2 * (exteriorCorrection G w t).re

lemma two_re_circle_div (w t : Circle) (hne : w ≠ t) :
    2 * ((t : ℂ) / ((t : ℂ)-w)).re = 1 := by
  have hn : normSq ((t : ℂ)-w) ≠ 0 :=
    normSq_eq_zero.not.mpr (sub_ne_zero.mpr (fun he => hne (Circle.ext he).symm))
  have hw := Circle.normSq_coe w
  have ht := Circle.normSq_coe t
  rw [div_re]
  field_simp
  simp only [normSq_apply, sub_re, sub_im] at *
  nlinarith

lemma re_div_eq_support (N z : ℂ) :
    (N/z).re = (conj N*z).re / normSq z := by
  simp only [div_re, mul_re, conj_re, conj_im]
  ring

theorem exteriorMarkovKernel_nonneg {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ z ∈ U, deriv G z ≠ 0) (hTU : ∀ t : Circle, (t : ℂ) ∈ U)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv G t)*(G t-G w)).re) (w t : Circle) :
    0 ≤ exteriorMarkovKernel G w t := by
  have hoff (v : Circle) (hvt : v ≠ t) : 0 ≤ exteriorMarkovKernel G v t := by
    have hne : (t : ℂ) ≠ v := fun he => hvt (Circle.ext he).symm
    have hg : G (t : ℂ) ≠ G v := fun he => hne (hi (hTU t) (hTU v) he)
    rw [exteriorMarkovKernel, exteriorCorrection_eq hne (hG t (hTU t)).differentiableAt hg,
      sub_re]
    have hunit := two_re_circle_div v t hvt
    have hpos : 0 ≤ (((t : ℂ)*deriv G t)/(G t-G v)).re := by
      rw [re_div_eq_support]
      exact div_nonneg (hsupport v t) (normSq_nonneg _)
    linarith
  let : Nontrivial Circle := ⟨⟨-1,1,Circle.neg_ne_self 1⟩⟩
  have hc : Continuous (fun v : Circle => exteriorMarkovKernel G v t) := by
    have hb : Continuous (fun v : Circle => exteriorCorrection G v t) :=
      (exteriorCorrection_continuousOn hU hG hi hd).comp_continuous
        (continuous_subtype_val.prodMk continuous_const) (fun v => ⟨hTU v,hTU t⟩)
    exact continuous_const.add (continuous_const.mul (continuous_re.comp hb))
  exact closure_minimal (fun v hv => hoff v hv) (isClosed_le continuous_const hc)
    ((dense_compl_singleton t) w)

end CompleteCrouzeix
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CircleIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_30 u_31 u_32 u_33 u_34

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real
section
local instance instFactLtRealOfNat_solutions : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma unitAddCircle_integral_eq_circleAverage {E : Type u_30}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ t : UnitAddCircle, f (t.toCircle : ℂ) ∂AddCircle.haarAddCircle) =
      Real.circleAverage f 0 1 := by
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [inv_one, one_smul, zero_add]
  have he : (fun t : ℝ => f ((AddCircle.toCircle (T := 1) (t : UnitAddCircle)) : ℂ)) =
      (fun t : ℝ => f (circleMap 0 1 (2*Real.pi*t))) := by
    funext t
    congr 1
    simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap,
      ofReal_one, one_mul, zero_add, div_one]
  rw [he, Real.circleAverage]
  have hpi : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  simpa using intervalIntegral.integral_comp_mul_left
    (fun t : ℝ => f (circleMap 0 1 t)) hpi (a := 0) (b := 1)

lemma integral_analytic_circle {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) :
    (∫ t : UnitAddCircle, f (t.toCircle : ℂ) ∂AddCircle.haarAddCircle) = f 0 := by
  rw [unitAddCircle_integral_eq_circleAverage]
  have hd : DiffContOnCl ℂ f (Metric.ball 0 |(1:ℝ)|) := by
    constructor
    · simp only [abs_one]
      exact hf.differentiableOn.mono Metric.ball_subset_closedBall
    · simpa only [abs_one, closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)] using hf.continuousOn
  exact hd.circleAverage

lemma integral_reciprocal_analytic {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) :
    (∫ t : UnitAddCircle, f (t.toCircle : ℂ)⁻¹
      ∂AddCircle.haarAddCircle) = f 0 := by
  rw [unitAddCircle_integral_eq_circleAverage (fun z => f z⁻¹),
    Real.circleAverage_zero_one_congr_inv,
    ← unitAddCircle_integral_eq_circleAverage]
  exact integral_analytic_circle hf

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology
section

def physicalCauchy (G : ℂ → ℂ) (u : UnitAddCircle → ℂ) (z : ℂ) : ℂ :=
  ∫ t : UnitAddCircle, u t *
    ((t.toCircle : ℂ)*deriv G (t.toCircle : ℂ)/(G (t.toCircle : ℂ)-z))
    ∂AddCircle.haarAddCircle

local instance instFactLtRealOfNat_solutions_1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology
local instance instFactLtRealOfNat_solutions_2 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def cauchyCorrectionIntegral (G : ℂ → ℂ) (u : UnitAddCircle → ℂ) (w : ℂ) : ℂ :=
  ∫ t : UnitAddCircle, u t * exteriorCorrection G w (t.toCircle : ℂ)
    ∂AddCircle.haarAddCircle


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_MarkovOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_35 u_36 u_37 u_38 u_39

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
namespace CompleteCrouzeix

section

section Jensen
variable {X : Type u_35} {E : Type u_36} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma weighted_norm_integral_sq_le {k : X → ℝ} {f : X → E}
    (hk : Integrable k μ) (hk0 : ∀ x, 0 ≤ k x) (hk1 : ∫ x, k x ∂μ = 1)
    (hf : Integrable (fun x => k x • f x) μ)
    (hf2 : Integrable (fun x => k x * ‖f x‖^2) μ) :
    ‖∫ x, k x • f x ∂μ‖^2 ≤ ∫ x, k x * ‖f x‖^2 ∂μ := by
  let v := ∫ x, k x • f x ∂μ
  have hl : Integrable (fun x => 2 * inner ℝ v (k x • f x) - k x * ‖v‖^2) μ :=
    ((hf.const_inner v).const_mul 2).sub (hk.mul_const _)
  have hle : ∫ x, (2 * inner ℝ v (k x • f x) - k x * ‖v‖^2) ∂μ ≤
      ∫ x, k x * ‖f x‖^2 ∂μ := by
    apply integral_mono hl hf2
    intro x
    dsimp only
    rw [real_inner_smul_right]
    have hs := norm_sub_sq_real v (f x)
    have h := mul_nonneg (hk0 x) (sq_nonneg ‖v-f x‖)
    rw [hs] at h
    nlinarith
  rw [integral_sub ((hf.const_inner v).const_mul 2) (hk.mul_const _),
    integral_const_mul, integral_mul_const, integral_inner hf, hk1,
    real_inner_self_eq_norm_sq] at hle
  dsimp [v] at *
  linarith
end Jensen

variable {X : Type u_37} [MeasurableSpace X] (μ : Measure X)

structure MarkovKernel where
  kernel : X → X → ℝ
  measurable : Measurable (Function.uncurry kernel)
  nonneg : ∀ x y, 0 ≤ kernel x y
  bound : ∃ C : ℝ, ∀ x y, ‖kernel x y‖ ≤ C
  row : ∀ x, ∫ y, kernel x y ∂μ = 1
  column : ∀ y, ∫ x, kernel x y ∂μ = 1

namespace MarkovKernel
variable {μ} (K : MarkovKernel μ) [instIsFiniteMeasureΜ : IsFiniteMeasure μ]
  {E : Type u_38} [NormedAddCommGroup E] [instInnerProductSpaceℂE : InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

lemma row_measurable
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (K : CompleteCrouzeix.MarkovKernel μ) [MeasureTheory.IsFiniteMeasure μ] (x : X) :
    Measurable (K.kernel x) :=
  K.measurable.comp measurable_prodMk_left

lemma row_integrable (x : X) : Integrable (K.kernel x) μ := by
  obtain ⟨C,hC⟩ := K.bound
  exact Integrable.of_bound (K.row_measurable x).aestronglyMeasurable C
    (Filter.Eventually.of_forall (hC x))

lemma integrable_row_smul
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (K : CompleteCrouzeix.MarkovKernel μ) [MeasureTheory.IsFiniteMeasure μ] {E : Type u_38}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : Lp E 2 μ) (x : X) :
    Integrable (fun y => K.kernel x y • u y) μ := by
  obtain ⟨C,hC⟩ := K.bound
  exact ((Lp.memLp u).integrable (by norm_num)).bdd_smul (𝕜 := ℝ) (φ := K.kernel x) C
    (K.row_measurable x).aestronglyMeasurable (Filter.Eventually.of_forall (hC x))

lemma integrable_sq_norm
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ] {E : Type u_38} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (u : Lp E 2 μ) : Integrable (fun y => ‖u y‖^2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)

lemma integrable_row_sq (u : Lp E 2 μ) (x : X) :
    Integrable (fun y => K.kernel x y * ‖u y‖^2) μ := by
  obtain ⟨C,hC⟩ := K.bound
  exact (integrable_sq_norm u).bdd_mul (K.row_measurable x).aestronglyMeasurable
    (Filter.Eventually.of_forall (hC x))

lemma integrable_prod_smul
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (K : CompleteCrouzeix.MarkovKernel μ) [MeasureTheory.IsFiniteMeasure μ] {E : Type u_38}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : Lp E 2 μ) :
    Integrable (fun p : X × X => K.kernel p.1 p.2 • u p.2) (μ.prod μ) := by
  obtain ⟨C,hC⟩ := K.bound
  exact (((Lp.memLp u).integrable (by norm_num)).comp_snd μ).bdd_smul (𝕜 := ℝ) (φ := Function.uncurry K.kernel) C
    K.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun p => hC p.1 p.2)

lemma integrable_prod_sq (u : Lp E 2 μ) :
    Integrable (fun p : X × X => K.kernel p.1 p.2 * ‖u p.2‖^2) (μ.prod μ) := by
  obtain ⟨C,hC⟩ := K.bound
  exact ((integrable_sq_norm u).comp_snd μ).bdd_mul
    K.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun p => hC p.1 p.2)

def applyFun (u : Lp E 2 μ) (x : X) : E := ∫ y, K.kernel x y • u y ∂μ

lemma applyFun_aestronglyMeasurable (u : Lp E 2 μ) :
    AEStronglyMeasurable (K.applyFun u) μ :=
  (K.integrable_prod_smul u).aestronglyMeasurable.integral_prod_right'

lemma applyFun_sq_le (u : Lp E 2 μ) (x : X) :
    ‖K.applyFun u x‖^2 ≤ ∫ y, K.kernel x y * ‖u y‖^2 ∂μ := by
  let := InnerProductSpace.rclikeToReal ℂ E
  exact weighted_norm_integral_sq_le (K.row_integrable x) (K.nonneg x) (K.row x)
    (K.integrable_row_smul u x) (K.integrable_row_sq u x)

lemma applyFun_memLp (u : Lp E 2 μ) : MemLp (K.applyFun u) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (K.applyFun_aestronglyMeasurable u)).mpr
  apply (K.integrable_prod_sq u).integral_prod_left.mono'
    ((K.applyFun_aestronglyMeasurable u).norm.pow 2)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact K.applyFun_sq_le u x

def applyLp (u : Lp E 2 μ) : Lp E 2 μ :=
  (K.applyFun_memLp u).toLp (K.applyFun u)

lemma applyLp_ae (u : Lp E 2 μ) : ⇑(K.applyLp u) =ᵐ[μ] K.applyFun u :=
  (K.applyFun_memLp u).coeFn_toLp

lemma l2_norm_sq
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ] {E : Type u_38} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (u : Lp E 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  let := InnerProductSpace.rclikeToReal ℂ E
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma applyLp_norm_sq_le (u : Lp E 2 μ) : ‖K.applyLp u‖^2 ≤ ‖u‖^2 := by
  rw [l2_norm_sq, l2_norm_sq]
  have he : ∫ x, ‖K.applyLp u x‖^2 ∂μ = ∫ x, ‖K.applyFun u x‖^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [K.applyLp_ae u] with x hx using congrArg (fun z : E => ‖z‖^2) hx
  rw [he]
  calc _ ≤ ∫ x, ∫ y, K.kernel x y * ‖u y‖^2 ∂μ ∂μ := by
         apply integral_mono
         · exact (memLp_two_iff_integrable_sq_norm
             (K.applyFun_aestronglyMeasurable u)).mp (K.applyFun_memLp u)
         · exact (K.integrable_prod_sq u).integral_prod_left
         · exact K.applyFun_sq_le u
       _ = ∫ y, ‖u y‖^2 ∂μ := by
         rw [integral_integral_swap (K.integrable_prod_sq u)]
         congr 1
         funext y
         rw [integral_mul_const, K.column y, one_mul]

lemma applyLp_norm_le (u : Lp E 2 μ) : ‖K.applyLp u‖ ≤ ‖u‖ := by
  have h := K.applyLp_norm_sq_le u
  nlinarith [norm_nonneg (K.applyLp u), norm_nonneg u]

lemma applyFun_add (u v : Lp E 2 μ) (x : X) :
    K.applyFun (u+v) x = K.applyFun u x + K.applyFun v x := by
  unfold applyFun
  calc _ = ∫ y, K.kernel x y • (u y+v y) ∂μ := by
         apply integral_congr_ae
         filter_upwards [Lp.coeFn_add u v] with y hy
         rw [hy]; rfl
       _ = _ := by
         simp_rw [smul_add]
         exact integral_add (K.integrable_row_smul u x) (K.integrable_row_smul v x)

lemma applyFun_smul
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (K : CompleteCrouzeix.MarkovKernel μ) [MeasureTheory.IsFiniteMeasure μ] {E : Type u_38}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (c : ℂ) (u : Lp E 2 μ)
    (x : X) :
    K.applyFun (c • u) x = c • K.applyFun u x := by
  unfold applyFun
  calc _ = ∫ y, c • (K.kernel x y • u y) ∂μ := by
         apply integral_congr_ae
         filter_upwards [Lp.coeFn_smul c u] with y hy
         rw [hy]
         exact smul_comm _ _ _
       _ = _ := integral_smul c _

lemma applyLp_add (u v : Lp E 2 μ) : K.applyLp (u+v) = K.applyLp u+K.applyLp v := by
  apply Lp.ext
  filter_upwards [K.applyLp_ae (u+v), K.applyLp_ae u, K.applyLp_ae v,
    Lp.coeFn_add (K.applyLp u) (K.applyLp v)] with x huv hu hv ha
  rw [huv,ha]
  change K.applyFun (u+v) x = K.applyLp u x+K.applyLp v x
  rw [hu,hv,K.applyFun_add]

lemma applyLp_smul (c : ℂ) (u : Lp E 2 μ) : K.applyLp (c • u) = c • K.applyLp u := by
  apply Lp.ext
  filter_upwards [K.applyLp_ae (c • u), K.applyLp_ae u,
    Lp.coeFn_smul c (K.applyLp u)] with x hcu hu hc
  rw [hcu,hc]
  change K.applyFun (c • u) x = c • K.applyLp u x
  rw [hu,K.applyFun_smul]

def toCLM : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := K.applyLp
      map_add' := K.applyLp_add
      map_smul' := K.applyLp_smul }
    1 (fun u => by simpa using K.applyLp_norm_le u)

@[simp] lemma toCLM_apply (u : Lp E 2 μ) : K.toCLM u = K.applyLp u := rfl

end MarkovKernel
end
open MeasureTheory Set Metric Complex ComplexConjugate
open scoped Topology Real
local instance instFactLtRealOfNat_solutions_3 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

structure AnalyticBidiskKernel where
  B : ℂ → ℂ → ℂ
  continuous : ContinuousOn (Function.uncurry B)
    (closedBall 0 1 ×ˢ closedBall 0 1)
  left : ∀ y ∈ closedBall 0 1, AnalyticOnNhd ℂ (fun x => B x y) (closedBall 0 1)
  right : ∀ x ∈ closedBall 0 1, AnalyticOnNhd ℂ (B x) (closedBall 0 1)
  zero_left : ∀ y, B 0 y = 0
  zero_right : ∀ x, B x 0 = 0
  positive : ∀ w t : Circle, 0 ≤ 1 + 2 * (B (w : ℂ)⁻¹ (t : ℂ)⁻¹).re

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

def circleB (w t : UnitAddCircle) : ℂ := K.B (w.toCircle : ℂ)⁻¹ (t.toCircle : ℂ)⁻¹

def kernel (w t : UnitAddCircle) : ℝ := 1 + 2 * (K.circleB w t).re

lemma norm_inv_circle (t : UnitAddCircle) : ‖(t.toCircle : ℂ)⁻¹‖ = 1 := by
  simp [Circle.norm_coe]

lemma inv_circle_mem (t : UnitAddCircle) : (t.toCircle : ℂ)⁻¹ ∈ closedBall 0 1 := by
  rw [mem_closedBall, dist_zero_right, norm_inv_circle]

lemma continuous_circleB : Continuous (Function.uncurry K.circleB) := by
  have hi : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)⁻¹) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle.inv
  apply K.continuous.comp_continuous ((hi.comp continuous_fst).prodMk (hi.comp continuous_snd))
  intro p
  exact ⟨inv_circle_mem p.1, inv_circle_mem p.2⟩

lemma continuous_kernel : Continuous (Function.uncurry K.kernel) :=
  continuous_const.add (continuous_const.mul (Complex.continuous_re.comp K.continuous_circleB))

lemma circleB_row_integral (w : UnitAddCircle) :
    (∫ t, K.circleB w t ∂AddCircle.haarAddCircle) = 0 := by
  unfold circleB
  rw [integral_reciprocal_analytic (K.right _ (inv_circle_mem w)), K.zero_right]

lemma circleB_column_integral (t : UnitAddCircle) :
    (∫ w, K.circleB w t ∂AddCircle.haarAddCircle) = 0 := by
  unfold circleB
  rw [integral_reciprocal_analytic (K.left _ (inv_circle_mem t)), K.zero_left]

lemma kernel_row_integral (w : UnitAddCircle) :
    (∫ t, K.kernel w t ∂AddCircle.haarAddCircle) = 1 := by
  have hc : Continuous (K.circleB w) :=
    K.continuous_circleB.comp (continuous_const.prodMk continuous_id)
  have hi := hc.integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  change (∫ t, (1 + 2 * (K.circleB w t).re) ∂AddCircle.haarAddCircle) = 1
  have hir : Integrable (fun t => (K.circleB w t).re) AddCircle.haarAddCircle := hi.re
  have he : (∫ t, (K.circleB w t).re ∂AddCircle.haarAddCircle) =
      (∫ t, K.circleB w t ∂AddCircle.haarAddCircle).re := integral_re hi
  rw [integral_add (integrable_const (1 : ℝ))
    (hir.const_mul 2), integral_const_mul, he, K.circleB_row_integral]
  simp

lemma kernel_column_integral (t : UnitAddCircle) :
    (∫ w, K.kernel w t ∂AddCircle.haarAddCircle) = 1 := by
  have hc : Continuous (fun w => K.circleB w t) :=
    K.continuous_circleB.comp (continuous_id.prodMk continuous_const)
  have hi := hc.integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  change (∫ w, (1 + 2 * (K.circleB w t).re) ∂AddCircle.haarAddCircle) = 1
  have hir : Integrable (fun w => (K.circleB w t).re) AddCircle.haarAddCircle := hi.re
  have he : (∫ w, (K.circleB w t).re ∂AddCircle.haarAddCircle) =
      (∫ w, K.circleB w t ∂AddCircle.haarAddCircle).re := integral_re hi
  rw [integral_add (integrable_const (1 : ℝ))
    (hir.const_mul 2), integral_const_mul, he, K.circleB_column_integral]
  simp

def toMarkovKernel : MarkovKernel (@AddCircle.haarAddCircle 1 inferInstance) where
  kernel := K.kernel
  measurable := K.continuous_kernel.measurable
  nonneg w t := K.positive w.toCircle t.toCircle
  bound := by
    obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn K.continuous_kernel.continuousOn
    exact ⟨C, fun w t => hC (w,t) (mem_univ _)⟩
  row := K.kernel_row_integral
  column := K.kernel_column_integral

end AnalyticBidiskKernel
end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_FourierResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_40 u_41 u_42 u_43

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace

open scoped ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

section

section

variable {E : Type u_40} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

structure FourierResolution (E : Type u_41) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  proj : Fin 3 → E →L[ℂ] E
  selfAdjoint : ∀ i, (proj i).adjoint = proj i
  product : ∀ i j, (proj i).comp (proj j) = if i = j then proj i else 0
  total : proj 0 + proj 1 + proj 2 = ContinuousLinearMap.id ℂ E

namespace FourierResolution
variable (D : FourierResolution E)

lemma decompose (u : E) : D.proj 0 u + D.proj 1 u + D.proj 2 u = u := by
  exact congrArg (fun T : E →L[ℂ] E => T u) D.total

@[simp] lemma proj_proj (i j : Fin 3) (u : E) :
    D.proj i (D.proj j u) = if i = j then D.proj i u else 0 := by
  have h := congrArg (fun T : E →L[ℂ] E => T u) (D.product i j)
  split_ifs with hij <;> simpa [hij] using h

def cauchy (M : E →L[ℂ] E) : E →L[ℂ] E :=
  D.proj 0 + D.proj 1 + M.comp (D.proj 1)

def cauchyAdjoint (M : E →L[ℂ] E) : E →L[ℂ] E :=
  D.proj 0 + D.proj 1 + M.adjoint.comp (D.proj 2)

end FourierResolution
end

open scoped lp
variable {ι : Type u_42} {E : Type u_43} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

def modeMask (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) : ℓ²(ι, ℂ) :=
  ⟨fun n => if c n = j then u n else 0, (lp.memℓp u).mono' (by
    intro n; split_ifs <;> simp)⟩

@[simp] lemma modeMask_apply (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) (n : ι) :
    modeMask c j u n = if c n = j then u n else 0 := rfl

lemma modeMask_norm (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) :
    ‖modeMask c j u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num)
  intro n
  simp only [modeMask_apply]
  split_ifs <;> simp

def modeMaskL (c : ι → Fin 3) (j : Fin 3) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  LinearMap.mkContinuous
  { toFun := modeMask c j
    map_add' u v := by ext n; simp only [modeMask_apply, lp.coeFn_add, Pi.add_apply]; split_ifs <;> simp
    map_smul' a u := by ext n; simp only [modeMask_apply, lp.coeFn_smul, Pi.smul_apply]; split_ifs <;> simp }
    1 (by intro u; simpa using modeMask_norm c j u)

@[simp] lemma modeMaskL_apply (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) (n : ι) :
    modeMaskL c j u n = if c n = j then u n else 0 := rfl

def basisProjection (b : HilbertBasis ι ℂ E) (c : ι → Fin 3) (j : Fin 3) : E →L[ℂ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((modeMaskL c j).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] lemma basisProjection_repr
    {ι : Type u_42} {E : Type u_43} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (c : ι → Fin 3)
    (j : Fin 3) (u : E) (n : ι) :
    b.repr (basisProjection b c j u) n = if c n = j then b.repr u n else 0 := by
  simp [basisProjection]

lemma basisProjection_inner (b : HilbertBasis ι ℂ E) (c : ι → Fin 3)
    (j : Fin 3) (u v : E) :
    inner ℂ (basisProjection b c j u) v = inner ℂ u (basisProjection b c j v) := by
  rw [← b.repr.inner_map_map, ← b.repr.inner_map_map]
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [basisProjection_repr]
  split_ifs <;> simp

def basisResolution (b : HilbertBasis ι ℂ E) (c : ι → Fin 3) : FourierResolution E where
  proj := basisProjection b c
  selfAdjoint i := by
    symm
    exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (basisProjection_inner b c i)
  product i j := by
    ext u
    apply b.repr.injective
    ext n
    by_cases hij : i = j
    · subst j
      simp only [ContinuousLinearMap.comp_apply, basisProjection_repr]
      by_cases hc : c n = i <;> simp [hc]
    · simp only [ite_eq_right hij, zero_apply, map_zero, lp.coeFn_zero, Pi.zero_apply,
        ContinuousLinearMap.comp_apply, basisProjection_repr]
      by_cases hc : c n = i
      · simp [hc, hij]
      · simp [hc]

  total := by
    ext u
    apply b.repr.injective
    ext n
    simp only [add_apply, map_add, lp.coeFn_add, Pi.add_apply,
      basisProjection_repr, ContinuousLinearMap.id_apply]
    have h : c n = 0 ∨ c n = 1 ∨ c n = 2 := by omega
    rcases h with h | h | h <;> simp [h]

def frequencyPart (n : ℤ) : Fin 3 := if n = 0 then 0 else if 0 < n then 1 else 2

open MeasureTheory
local instance instFactLtRealOfNat_solutions_4 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
abbrev CircleL2 := Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance)

def scalarFourier : FourierResolution CircleL2 :=
  basisResolution fourierBasis frequencyPart

end

open MeasureTheory ComplexConjugate
open scoped Topology
local instance instFactLtRealOfNat_solutions_5 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

def scalarM : CircleL2 →L[ℂ] CircleL2 := K.toMarkovKernel.toCLM

end AnalyticBidiskKernel
end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CauchyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_44

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace

namespace CompleteCrouzeix

section
open MeasureTheory Set Complex
open scoped Topology InnerProductSpace ComplexConjugate
local instance instFactLtRealOfNat_solutions_6 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def circleTest (f : C(UnitAddCircle,ℂ)) : CircleL2 →L[ℂ] ℂ :=
  innerSL ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (star f))

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

def rowB (w : UnitAddCircle) : C(UnitAddCircle,ℂ) :=
  ⟨K.circleB w,K.continuous_circleB.comp (continuous_const.prodMk continuous_id)⟩

def rowKernel (w : UnitAddCircle) : C(UnitAddCircle,ℂ) :=
  ⟨fun t => (K.kernel w t : ℂ), Complex.continuous_ofReal.comp
    (K.continuous_kernel.comp (continuous_const.prodMk continuous_id))⟩

end AnalyticBidiskKernel
end

open MeasureTheory Set Complex
open scoped Topology
local instance instFactLtRealOfNat_solutions_7 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def analyticCircleTrace (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) :
    C(UnitAddCircle,ℂ) :=
  ⟨fun t => f (t.toCircle : ℂ), hf.continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle)
    (fun t => Metric.sphere_subset_closedBall t.toCircle.property)⟩

end CompleteCrouzeix

open Set Metric Filter Complex
open scoped Topology
namespace CompleteCrouzeix

section

section


open Set Metric Complex MeasureTheory
open scoped Topology
local instance instFactLtRealOfNat_solutions_8 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open MeasureTheory Set Metric Complex
open scoped Topology
local instance instFactLtRealOfNat_solutions_9 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end


theorem reciprocalCorrection_continuousOn {a : ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hh : AnalyticOnNhd ℂ h U)
    (hne : ∀ x ∈ U, ∀ y ∈ U, exteriorDividedDifference a h x y ≠ 0) :
    ContinuousOn (Function.uncurry (reciprocalCorrection a h)) (U ×ˢ U) := by
  apply continuousOn_of_analytic_left_offDiagonal hU
    (fun y hy => reciprocalCorrection_analytic_left hU hh hne hy)
  let V := {p : ℂ × ℂ | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2}
  let H := fun z : ℂ => z*h z
  have hH : AnalyticOnNhd ℂ H U := analyticOnNhd_id.mul hh
  have ch1 : ContinuousOn (fun p : ℂ × ℂ => h p.1) V :=
    hh.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have ch2 : ContinuousOn (fun p : ℂ × ℂ => h p.2) V :=
    hh.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have cH1 : ContinuousOn (fun p : ℂ × ℂ => H p.1) V :=
    hH.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have cH2 : ContinuousOn (fun p : ℂ × ℂ => H p.2) V :=
    hH.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have cdH2 : ContinuousOn (fun p : ℂ × ℂ => deriv H p.2) V :=
    hH.deriv.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have cz : ∀ p ∈ V, p.1-p.2 ≠ 0 := fun p hp => sub_ne_zero.mpr hp.2.2
  have cq : ContinuousOn (fun p : ℂ × ℂ => (h p.1-h p.2)/(p.1-p.2)) V :=
    (ch1.sub ch2).div (continuousOn_fst.sub continuousOn_snd) cz
  have cr : ContinuousOn (fun p : ℂ × ℂ =>
      ((H p.1-H p.2)/(p.1-p.2)-deriv H p.2)/(p.1-p.2)) V :=
    (((cH1.sub cH2).div (continuousOn_fst.sub continuousOn_snd) cz).sub cdH2).div
      (continuousOn_fst.sub continuousOn_snd) cz
  have cqeq (p : ℂ × ℂ) (hp : p ∈ V) :
      exteriorDividedDifference a h p.1 p.2 =
        a-p.1*p.2*((h p.1-h p.2)/(p.1-p.2)) := by
    rw [exteriorDividedDifference, dslope_comm h p.1 p.2,
      dslope_of_ne _ hp.2.2, slope_def_field]
  have cc : ContinuousOn (fun p : ℂ × ℂ =>
      p.1*p.2*(((H p.1-H p.2)/(p.1-p.2)-deriv H p.2)/(p.1-p.2)) /
        (a-p.1*p.2*((h p.1-h p.2)/(p.1-p.2)))) V :=
    ((continuousOn_fst.mul continuousOn_snd).mul cr).div
      (continuousOn_const.sub ((continuousOn_fst.mul continuousOn_snd).mul cq))
      (fun p hp => (cqeq p hp) ▸ hne p.1 hp.1 p.2 hp.2.1)
  apply cc.congr
  intro p hp
  change reciprocalCorrection a h p.1 p.2 = _
  rw [reciprocalCorrection, cqeq p hp, dslope_of_ne _ hp.2.2, slope_def_field,
    dslope_of_ne _ hp.2.2, slope_def_field, dslope_same]

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ExteriorProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_45

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology

section
open Set Metric Complex
open scoped ComplexConjugate

lemma analyticOnNhd_exteriorMap {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hh : AnalyticOnNhd ℂ h (ball 0 R)) :
    AnalyticOnNhd ℂ (exteriorMap a b h) {t | R⁻¹ < ‖t‖} := by
  intro t ht
  change R⁻¹ < ‖t‖ at ht
  have ht0 : t ≠ 0 := by
    intro he; simp only [he, norm_zero] at ht
    exact (not_lt_of_ge (inv_nonneg.mpr hR.le)) ht
  have hi : t⁻¹ ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right, norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr ht0) hR).mpr ht
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).add
    ((hh _ hi).comp (analyticAt_id.inv ht0))

def actualExteriorKernel {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re) : AnalyticBidiskKernel := by
  have hR0 : 0 < R := lt_trans zero_lt_one hR
  have hn := dividedDifference_ne_zero ha hh hi hd hR0
  have hs : closedBall (0 : ℂ) 1 ⊆ ball 0 R := closedBall_subset_ball hR
  have hTU : ∀ t : Circle, R⁻¹ < ‖(t : ℂ)‖ := by
    intro t; rw [Circle.norm_coe]
    exact (inv_lt_one₀ hR0).mpr hR
  refine { B := reciprocalCorrection a h
           continuous := (reciprocalCorrection_continuousOn isOpen_ball hh hn).mono
             (prod_mono hs hs)
           left := fun y hy => (reciprocalCorrection_analytic_left isOpen_ball hh hn (hs hy)).mono hs
           right := fun x hx => (reciprocalCorrection_analytic_right isOpen_ball hh hn (hs hx)).mono hs
           zero_left := reciprocalCorrection_zero_left a h
           zero_right := reciprocalCorrection_zero_right a h
           positive := ?_ }
  intro w t
  have hw : (w : ℂ)⁻¹ ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right, norm_inv, Circle.norm_coe, inv_one] using hR
  have ht : (t : ℂ)⁻¹ ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right, norm_inv, Circle.norm_coe, inv_one] using hR
  have he := exteriorCorrection_eq_reciprocal (a := a) (b := b)
    (inv_ne_zero (Circle.coe_ne_zero w)) (inv_ne_zero (Circle.coe_ne_zero t))
    (hh _ hw).differentiableAt (hh _ ht).differentiableAt
    ((analyticOnNhd_dslope isOpen_ball hh hw) _ ht).differentiableAt
  simp only [inv_inv] at he
  rw [← he]
  exact exteriorMarkovKernel_nonneg (isOpen_lt continuous_const continuous_norm)
    (analyticOnNhd_exteriorMap hR0 hh) hi hd hTU hsupport w t

end

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology
section
local instance instFactLtRealOfNat_solutions_10 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def reciprocalResolventDenom (a b : ℂ) (h : ℂ → ℂ) (z s : ℂ) : ℂ :=
  a+s*(b+h s-z)

def reciprocalResolvent (a b : ℂ) (h : ℂ → ℂ) (z s : ℂ) : ℂ :=
  (a-s^2*deriv h s) / reciprocalResolventDenom a b h z s

end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance instFactLtRealOfNat_solutions_11 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_FourierExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_46 u_47

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology

open Set Filter Metric Complex
open scoped Topology

section
open Set Metric Complex MeasureTheory
open scoped Topology
local instance instFactLtRealOfNat_solutions_13 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def physicalAnalyticTrace {G : ℂ → ℂ} {Ω : Set ℂ}
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hboundary : MapsTo G (sphere 0 1) (closure Ω))
    (v : ℂ → ℂ) (hv : AnalyticOnNhd ℂ v (closure Ω)) : C(UnitAddCircle,ℂ) :=
  ⟨fun t => v (G t.toCircle), (hv.comp hG hboundary).continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property)⟩

end

section
open Set Metric Complex MeasureTheory
open scoped Topology
local instance instFactLtRealOfNat_solutions_14 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open MeasureTheory
variable {α : Type u_46} {ι : Type u_47} [MeasurableSpace α] {μ : Measure α}
  [Fintype ι] [instDecidableEqΙ : DecidableEq ι]

abbrev VectorL2 := Lp (EuclideanSpace ℂ ι) 2 μ

def l2Coordinate (i : ι) : VectorL2 (μ := μ) (ι := ι) →L[ℂ] Lp ℂ 2 μ :=
  (EuclideanSpace.proj i).compLpL 2 μ

def singleCLM (i : ι) : ℂ →L[ℂ] EuclideanSpace ℂ ι :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single i 1)

@[simp] lemma singleCLM_apply (i : ι) (z : ℂ) :
    singleCLM i z = EuclideanSpace.single i z := by
  ext k
  by_cases h : k = i <;> simp [singleCLM, h]

def l2Embedding (i : ι) : Lp ℂ 2 μ →L[ℂ] VectorL2 (μ := μ) (ι := ι) :=
  (singleCLM i).compLpL 2 μ

lemma l2Coordinate_ae
    {α : Type u_46} {ι : Type u_47} [MeasurableSpace α] {μ : Measure α}
    [Fintype ι] [DecidableEq ι] (i : ι) (u : VectorL2 (μ := μ) (ι := ι)) :
    l2Coordinate i u =ᵐ[μ] fun t => u t i := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL u

lemma l2Embedding_ae (i : ι) (u : Lp ℂ 2 μ) :
    l2Embedding i u =ᵐ[μ] fun t => EuclideanSpace.single i (u t) := by
  simpa only [l2Embedding, singleCLM_apply] using (singleCLM i).coeFn_compLpL u

lemma l2Coordinate_injective {u v : VectorL2 (μ := μ) (ι := ι)}
    (h : ∀ i, l2Coordinate i u = l2Coordinate i v) : u = v := by
  apply Lp.ext
  have hh : ∀ᵐ t ∂μ, ∀ i, (u t) i = (v t) i := by
    rw [ae_all_iff]
    intro i
    filter_upwards [l2Coordinate_ae i u, l2Coordinate_ae i v] with t hu hv
    rw [← hu, ← hv, h i]
  filter_upwards [hh] with t ht
  exact PiLp.ext ht

@[simp] lemma coordinate_embedding (i j : ι) (u : Lp ℂ 2 μ) :
    l2Coordinate i (l2Embedding j u) = if i = j then u else 0 := by
  by_cases hij : i = j
  · subst j; rw [ite_eq_left rfl]
    apply Lp.ext
    filter_upwards [l2Coordinate_ae i (l2Embedding i u), l2Embedding_ae i u]
      with t ht hu
    simp [ht, hu]
  · rw [ite_eq_right hij]
    apply Lp.ext
    filter_upwards [l2Coordinate_ae i (l2Embedding j u), l2Embedding_ae j u,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with t ht hu hz
    rw [ht, hu]
    simp only [PiLp.single_apply, ite_eq_right hij]
    exact hz.symm

lemma embedding_inner (i : ι) (u : Lp ℂ 2 μ) (v : VectorL2 (μ := μ) (ι := ι)) :
    inner ℂ (l2Embedding i u) v = inner ℂ u (l2Coordinate i v) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Embedding_ae i u, l2Coordinate_ae i v] with t ht hv
  rw [ht, hv, EuclideanSpace.inner_single_left]
  simp [RCLike.inner_apply, mul_comm]

lemma coordinate_inner (i : ι) (u : VectorL2 (μ := μ) (ι := ι)) (v : Lp ℂ 2 μ) :
    inner ℂ (l2Coordinate i u) v = inner ℂ u (l2Embedding i v) := by
  have h := congrArg (starRingEnd ℂ) (embedding_inner i v u)
  simpa only [inner_conj_symm] using h.symm

def entrywiseL2 (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    VectorL2 (μ := μ) (ι := ι) →L[ℂ] VectorL2 (μ := μ) (ι := ι) :=
  ∑ i : ι, (l2Embedding i).comp (T.comp (l2Coordinate i))

@[simp] lemma coordinate_entrywise (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (u : VectorL2 (μ := μ) (ι := ι)) (i : ι) :
    l2Coordinate i (entrywiseL2 T u) = T (l2Coordinate i u) := by
  simp [entrywiseL2, sum_apply, map_sum]

lemma entrywise_inner (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (u v : VectorL2 (μ := μ) (ι := ι)) :
    inner ℂ (entrywiseL2 T u) v = inner ℂ u (entrywiseL2 T.adjoint v) := by
  simp only [entrywiseL2, sum_apply, ContinuousLinearMap.comp_apply,
    sum_inner, inner_sum, embedding_inner, ← coordinate_inner]
  apply Finset.sum_congr rfl
  intro i hi
  exact (ContinuousLinearMap.adjoint_inner_right T _ _).symm

def vectorResolution (D : FourierResolution (Lp ℂ 2 μ)) :
    FourierResolution (VectorL2 (μ := μ) (ι := ι)) where
  proj j := entrywiseL2 (D.proj j)
  selfAdjoint j := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro u v
    rw [entrywise_inner, D.selfAdjoint]
  product i j := by
    ext1 u
    apply l2Coordinate_injective
    intro k
    by_cases hij : i = j
    · subst j
      simp [coordinate_entrywise, D.proj_proj]
    · simp [hij, coordinate_entrywise, D.proj_proj]
  total := by
    ext1 u
    apply l2Coordinate_injective
    intro k
    simpa using D.decompose (l2Coordinate k u)


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HilbertSchmidt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_48 u_49 u_50 u_51 u_52 u_53

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section

variable {m : Type u_48} [Fintype m] [instDecidableEqM : DecidableEq m]

def hsSq (A : Matrix m m ℂ) : ℝ := (Matrix.trace (Aᴴ * A)).re

abbrev HSMatrix (m : Type u_49) [Fintype m] := EuclideanSpace ℂ (m × m)

def toHS (A : Matrix m m ℂ) : HSMatrix m := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
def fromHS (A : HSMatrix m) : Matrix m m ℂ := fun i j => A (i,j)

@[simp] theorem fromHS_toHS
    {m : Type u_48} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) : fromHS (toHS A) = A := rfl
@[simp] theorem toHS_fromHS
    {m : Type u_48} [Fintype m] [DecidableEq m] (A : HSMatrix m) : toHS (fromHS A) = A := rfl

lemma hsSq_eq_sum
    {m : Type u_48} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) :
    hsSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [hsSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.sq_norm]
  rfl

lemma norm_toHS_sq (A : Matrix m m ℂ) : ‖toHS A‖ ^ 2 = hsSq A := by
  rw [hsSq_eq_sum, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

def hsStar : HSMatrix m ≃ₗᵢ⋆[ℂ] HSMatrix m where
  toFun A := toHS (fromHS A)ᴴ
  invFun A := toHS (fromHS A)ᴴ
  left_inv A := by simp
  right_inv A := by simp
  map_add' A B := by apply PiLp.ext; intro ij; simp [toHS, fromHS, Matrix.conjTranspose_apply]
  map_smul' c A := by apply PiLp.ext; intro ij; simp [toHS, fromHS, Matrix.conjTranspose_apply]
  norm_map' A := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖toHS (fromHS A)ᴴ‖ ^ 2 = ‖A‖ ^ 2
    rw [norm_toHS_sq, hsSq_eq_sum, ← toHS_fromHS A, norm_toHS_sq, hsSq_eq_sum]
    simp only [Matrix.conjTranspose_apply, norm_star, fromHS_toHS]
    rw [Finset.sum_comm]

@[simp] lemma hsStar_apply (A : HSMatrix m) : hsStar A = toHS (fromHS A)ᴴ := rfl

lemma hsStar_involutive : Function.Involutive (hsStar : HSMatrix m → HSMatrix m) := by
  intro A; simp

open MeasureTheory
variable {α : Type u_50} [MeasurableSpace α] {μ : Measure α}

lemma l2_norm_sq
    {m : Type u_48} [Fintype m] [DecidableEq m] {α : Type u_50} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} (u : Lp (HSMatrix m) 2 μ) :
    ‖u‖ ^ 2 = ∫ t, ‖u t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

def l2StarL : Lp (HSMatrix m) 2 μ →L⋆[ℂ] Lp (HSMatrix m) 2 μ :=
  hsStar.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ

lemma l2StarL_ae (u : Lp (HSMatrix m) 2 μ) :
    l2StarL u =ᵐ[μ] fun t => hsStar (u t) :=
  (hsStar (m := m)).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL u

lemma l2StarL_involutive : Function.Involutive (l2StarL : Lp (HSMatrix m) 2 μ → _) := by
  intro u
  apply Lp.ext
  filter_upwards [l2StarL_ae (l2StarL u), l2StarL_ae u] with t ht hu
  rw [ht, hu, hsStar_involutive]

lemma l2StarL_norm (u : Lp (HSMatrix m) 2 μ) : ‖l2StarL u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq, l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [l2StarL_ae u] with t ht
  rw [ht, hsStar.norm_map]

def l2Star : Lp (HSMatrix m) 2 μ ≃ₗᵢ⋆[ℂ] Lp (HSMatrix m) 2 μ where
  toFun := l2StarL
  invFun := l2StarL
  left_inv := l2StarL_involutive
  right_inv := l2StarL_involutive
  map_add' := map_add l2StarL
  map_smul' := l2StarL.map_smulₛₗ
  norm_map' := l2StarL_norm

@[simp] lemma l2Star_apply (u : Lp (HSMatrix m) 2 μ) : l2Star u = l2StarL u := rfl

end

section
open scoped InnerProductSpace
variable {m : Type u_51} [Fintype m] [instDecidableEqM : DecidableEq m]

def hsLeft (A : Matrix m m ℂ) : HSMatrix m →L[ℂ] HSMatrix m :=
  LinearMap.toContinuousLinearMap
  { toFun B := toHS (A * fromHS B)
    map_add' B C := by
      apply PiLp.ext; intro ij
      simp [toHS, fromHS, Matrix.mul_apply, Finset.sum_add_distrib, mul_add]
    map_smul' c B := by
      apply PiLp.ext; intro ij
      simp [toHS, fromHS, Matrix.mul_apply, Finset.mul_sum, mul_left_comm] }

def hsRight (A : Matrix m m ℂ) : HSMatrix m →L[ℂ] HSMatrix m :=
  LinearMap.toContinuousLinearMap
  { toFun B := toHS (fromHS B * A)
    map_add' B C := by
      apply PiLp.ext; intro ij
      simp [toHS, fromHS, Matrix.mul_apply, Finset.sum_add_distrib, add_mul]
    map_smul' c B := by
      apply PiLp.ext; intro ij
      simp [toHS, fromHS, Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

@[simp] lemma hsLeft_apply
    {m : Type u_51} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (B : HSMatrix m) :
    hsLeft A B = toHS (A * fromHS B) := rfl
@[simp] lemma hsRight_apply
    {m : Type u_51} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (B : HSMatrix m) :
    hsRight A B = toHS (fromHS B * A) := rfl

def hsLeftL : Matrix m m ℂ →L[ℂ] HSMatrix m →L[ℂ] HSMatrix m :=
  LinearMap.toContinuousLinearMap
  { toFun := hsLeft
    map_add' A B := by
      ext C ij
      simp [hsLeft, toHS, fromHS, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
    map_smul' c A := by
      ext C ij
      simp [hsLeft, toHS, fromHS, Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

def hsRightL : Matrix m m ℂ →L[ℂ] HSMatrix m →L[ℂ] HSMatrix m :=
  LinearMap.toContinuousLinearMap
  { toFun := hsRight
    map_add' A B := by
      ext C ij
      simp [hsRight, toHS, fromHS, Matrix.mul_apply, mul_add, Finset.sum_add_distrib]
    map_smul' c A := by
      ext C ij
      simp [hsRight, toHS, fromHS, Matrix.mul_apply, Finset.mul_sum, mul_left_comm] }

end

open MeasureTheory
variable {α : Type u_52} {E : Type u_53} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : α → E →L[ℂ] E) (hB : AEStronglyMeasurable B μ)
  (hBn : ∀ᵐ t ∂μ, ‖B t‖ ≤ 1)

include hB hBn in
lemma pointwise_memLp (u : Lp E 2 μ) : MemLp (fun t => B t (u t)) 2 μ := by
  apply (Lp.memLp u).of_le
  · exact (ContinuousLinearMap.id ℂ (E →L[ℂ] E)).aestronglyMeasurable_comp₂
      hB (Lp.aestronglyMeasurable u)
  · filter_upwards [hBn] with t ht
    simpa using (B t).le_of_opNorm_le ht (u t)

def pointwiseL2 (u : Lp E 2 μ) : Lp E 2 μ :=
  (pointwise_memLp B hB hBn u).toLp _

lemma pointwiseL2_ae (u : Lp E 2 μ) :
    pointwiseL2 B hB hBn u =ᵐ[μ] fun t => B t (u t) :=
  MemLp.coeFn_toLp _

lemma pointwiseL2_norm (u : Lp E 2 μ) : ‖pointwiseL2 B hB hBn u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [pointwiseL2_ae B hB hBn u, hBn] with t hu ht
  rw [hu]
  simpa using (B t).le_of_opNorm_le ht (u t)

def pointwiseL2L : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  LinearMap.mkContinuous
  { toFun := pointwiseL2 B hB hBn
    map_add' u v := by
      apply Lp.ext
      filter_upwards [pointwiseL2_ae B hB hBn (u + v),
        pointwiseL2_ae B hB hBn u, pointwiseL2_ae B hB hBn v,
        Lp.coeFn_add u v, Lp.coeFn_add (pointwiseL2 B hB hBn u) (pointwiseL2 B hB hBn v)]
        with t huv hu hv hadd hout
      rw [huv, hout, hadd]
      simp only [Pi.add_apply]
      rw [hu, hv, map_add]
    map_smul' c u := by
      apply Lp.ext
      filter_upwards [pointwiseL2_ae B hB hBn (c • u), pointwiseL2_ae B hB hBn u,
        Lp.coeFn_smul c u, Lp.coeFn_smul c (pointwiseL2 B hB hBn u)] with t hcu hu hin hout
      change pointwiseL2 B hB hBn (c • u) t = (c • pointwiseL2 B hB hBn u) t
      rw [hcu, hout, hin]
      simp only [Pi.smul_apply]
      rw [hu]
      exact (B t).map_smul c (u t) }
    1 (by intro u; simpa using pointwiseL2_norm B hB hBn u)


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_OrderedMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_54 u_55 u_56 u_57 u_58 u_59 u_60

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace CompleteCrouzeix

section

section

section

open MeasureTheory
local instance instFactLtRealOfNat_solutions_15 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {m : Type u_55} [Fintype m] [DecidableEq m]
abbrev MatrixCircleL2 := Lp (HSMatrix m) 2 (@AddCircle.haarAddCircle 1 inferInstance)

def matrixFourier : FourierResolution (MatrixCircleL2 (m := m)) :=
  vectorResolution scalarFourier

end

open MeasureTheory
namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)
variable {m : Type u_56} [Fintype m] [instDecidableEqM : DecidableEq m]

local instance instFactLtRealOfNat_solutions_16_r2e26d2_1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
def matrixM : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m) :=
  K.toMarkovKernel.toCLM

end AnalyticBidiskKernel
end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance instFactLtRealOfNat_solutions_17 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance instFactLtRealOfNat_solutions_18 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_HolomorphicEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_61 u_62 u_63 u_64

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
section

variable {A : Type u_61} [Ring A] [Algebra ℂ A]

lemma aeval_nilpotent {N : A} {s : ℕ} (hs : N ^ s = 0) (p : ℂ[X]) :
    Polynomial.aeval N p = ∑ i ∈ range s, p.coeff i • N ^ i := by
  rw [Polynomial.aeval_eq_sum_range]
  rcases le_total (p.natDegree+1) s with h | h
  · apply Finset.sum_subset (Finset.range_mono h)
    intro i _ hn
    have hi' : p.natDegree < i := by simpa using hn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi', zero_smul]
  · symm
    apply Finset.sum_subset (Finset.range_mono h)
    intro i _ hn
    have hi' : s ≤ i := by simpa using hn
    rw [pow_eq_zero_of_le hi' hs, smul_zero]

lemma iteratedDeriv_polynomial (p : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun z => p.eval z) = fun z => ((Polynomial.derivative^[k]) p).eval z := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun z => p.eval z) = fun z => p.derivative.eval z :=
      funext fun z => p.deriv
    rw [hd, ih]
    rfl

lemma taylor_coeff_iteratedDeriv (p : ℂ[X]) (β : ℂ) (k : ℕ) :
    (Polynomial.taylor β p).coeff k =
      iteratedDeriv k (fun z => p.eval z) β / (k.factorial : ℂ) := by
  rw [Polynomial.taylor_coeff, iteratedDeriv_polynomial]
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero k)).mpr
  have h := congrArg (fun q : ℂ[X] => q.eval β)
    (congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) k) p)
  simpa [nsmul_eq_mul, mul_comm] using h

lemma scalarJetEval_polynomial {N : A} {s : ℕ} (hs : N ^ s = 0)
    (β : ℂ) (p : ℂ[X]) :
    scalarJetEval β N s (fun z => p.eval z) =
      Polynomial.aeval (N + algebraMap ℂ A β) p := by
  have he : Polynomial.aeval N (Polynomial.taylor β p) =
      Polynomial.aeval (N + algebraMap ℂ A β) p := by
    rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [← he, aeval_nilpotent hs]
  unfold scalarJetEval
  apply Finset.sum_congr rfl
  intro i _
  rw [taylor_coeff_iteratedDeriv]

lemma scalarJetEval_eventuallyEq {f g : ℂ → ℂ} {β : ℂ}
    (h : f =ᶠ[nhds β] g) (N : A) (s : ℕ) :
    scalarJetEval β N s f = scalarJetEval β N s g := by
  unfold scalarJetEval
  apply Finset.sum_congr rfl
  intro i _
  rw [h.iteratedDeriv_eq i]

def jetPolynomial (β : ℂ) (s : ℕ) (f : ℂ → ℂ) : ℂ[X] :=
  ∑ i ∈ range s, C (iteratedDeriv i f β / (i.factorial : ℂ)) * (X - C β) ^ i

lemma jetPolynomial_eval (β z : ℂ) (s : ℕ) (f : ℂ → ℂ) :
    (jetPolynomial β s f).eval z =
      ∑ i ∈ range s, ((z-β)^i / (i.factorial : ℂ)) * iteratedDeriv i f β := by
  simp only [jetPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma analytic_taylor_remainder {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (s : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R β ∧ ∀ᶠ z in nhds β,
      f z = (jetPolynomial β s f).eval z + (z-β)^s * R z := by
  have hshift : AnalyticAt ℂ (fun z => f (z+β)) 0 :=
    (show AnalyticAt ℂ f ((fun z : ℂ => z+β) 0) from by simpa using hf).comp
      (f := fun z : ℂ => z+β) (by fun_prop)
  obtain ⟨R, hR, hEq⟩ := hshift.exists_eventuallyEq_sum_add_pow_mul s
  refine ⟨fun z => R (z-β), ?_, ?_⟩
  · exact (show AnalyticAt ℂ R ((fun z : ℂ => z-β) β) from by simpa using hR).comp
      (f := fun z : ℂ => z-β) (by fun_prop)
  · have ht : Filter.Tendsto (fun z : ℂ => z-β) (nhds β) (nhds 0) := by
      simpa only [ContinuousAt, sub_self] using
        (continuous_sub_right β).continuousAt (x := β)
    have he := ht.eventually hEq
    filter_upwards [he] with z hz
    simpa only [Function.comp_apply, sub_add_cancel, iteratedDeriv_comp_add_const,
      zero_add, smul_eq_mul, jetPolynomial_eval] using hz

lemma scalarJetEval_eq_of_remainder {f g R : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β) (hR : AnalyticAt ℂ R β)
    (N : A) (s : ℕ)
    (he : ∀ᶠ z in nhds β, f z - g z = (z-β)^s * R z) :
    scalarJetEval β N s f = scalarJetEval β N s g := by
  have hord : (s : ℕ∞) ≤ analyticOrderAt (fun z => f z - g z) β :=
    (natCast_le_analyticOrderAt (hf.fun_sub hg)).mpr ⟨R, hR, by simpa using he⟩
  have hd := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hf.fun_sub hg)).mp hord
  apply Finset.sum_congr rfl
  intro i hi
  have h := hd i (Finset.mem_range.mp hi)
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, sub_eq_zero] at h
  rw [h]

lemma scalarJetEval_taylor {f : ℂ → ℂ} {β : ℂ} (hf : AnalyticAt ℂ f β)
    {N : A} {s : ℕ} (hs : N^s = 0) :
    scalarJetEval β N s f = Polynomial.aeval (N + algebraMap ℂ A β)
      (jetPolynomial β s f) := by
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hf s
  rw [← scalarJetEval_polynomial hs]
  apply scalarJetEval_eq_of_remainder hf
    (AnalyticOnNhd.eval_polynomial (jetPolynomial β s f) β (Set.mem_univ β)) hR
  filter_upwards [he] with z hz
  rw [hz]
  ring

lemma scalarJetEval_mul {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β)
    {N : A} {s : ℕ} (hs : N^s = 0) :
    scalarJetEval β N s (fun z => f z * g z) =
      scalarJetEval β N s f * scalarJetEval β N s g := by
  let p := jetPolynomial β s f
  let q := jetPolynomial β s g
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hf s
  obtain ⟨S, hS, hj⟩ := analytic_taylor_remainder hg s
  have hp : AnalyticAt ℂ (fun z => p.eval z) β :=
    AnalyticOnNhd.eval_polynomial p β (Set.mem_univ β)
  have hpq : AnalyticAt ℂ (fun z => (p*q).eval z) β :=
    AnalyticOnNhd.eval_polynomial (p*q) β (Set.mem_univ β)
  have hpoly : scalarJetEval β N s (fun z => f z * g z) =
      scalarJetEval β N s (fun z => (p*q).eval z) := by
    apply scalarJetEval_eq_of_remainder (hf.fun_mul hg) hpq
      (show AnalyticAt ℂ (fun z => R z * g z + p.eval z * S z) β from by fun_prop)
    filter_upwards [he, hj] with z hz hw
    change f z = p.eval z + (z-β)^s * R z at hz
    change g z = q.eval z + (z-β)^s * S z at hw
    simp only [Polynomial.eval_mul]
    rw [hz, hw]
    ring
  rw [hpoly, scalarJetEval_polynomial hs, map_mul,
    scalarJetEval_taylor hf hs, scalarJetEval_taylor hg hs]

lemma scalarJetEval_sub {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β) (N : A) (s : ℕ) :
    scalarJetEval β N s (fun z => f z - g z) =
      scalarJetEval β N s f - scalarJetEval β N s g := by
  unfold scalarJetEval
  simp only [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt,
    sub_div, sub_smul, Finset.sum_sub_distrib]

end

open Module Set
open scoped DirectSum
variable {V : Type u_63} [AddCommGroup V] [Module ℂ V] [instFiniteDimensionalℂV : FiniteDimensional ℂ V]

lemma primaryEquiv_coe (T : Module.End ℂ V) (β : ℂ) (x : T.maxGenEigenspace β) :
    primaryEquiv T (x : V) = DirectSum.lof ℂ ℂ (fun β => T.maxGenEigenspace β) β x := by
  classical
  apply (primaryEquiv T).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change (x : V) = DirectSum.coeLinearMap T.maxGenEigenspace
    (DirectSum.lof ℂ ℂ (fun β => T.maxGenEigenspace β) β x)
  simp

lemma primaryEquiv_symm_lof (T : Module.End ℂ V) (β : ℂ) (x : T.maxGenEigenspace β) :
    (primaryEquiv T).symm (DirectSum.lof ℂ ℂ (fun β => T.maxGenEigenspace β) β x) = x := by
  classical
  change DirectSum.coeLinearMap T.maxGenEigenspace
    (DirectSum.lof ℂ ℂ (fun β => T.maxGenEigenspace β) β x) = (x : V)
  simp

lemma primaryNilpotent_pow (T : Module.End ℂ V) (β : ℂ) :
    primaryNilpotent T β ^ finrank ℂ V = 0 := by
  ext x
  have hx := x.property
  simp only [T.maxGenEigenspace_eq_genEigenspace_finrank β,
    Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hx
  dsimp only [primaryNilpotent]
  rw [Module.End.pow_restrict]
  change ((T - algebraMap ℂ (Module.End ℂ V) β) ^ finrank ℂ V) (x : V) = 0
  simpa only [Algebra.algebraMap_eq_smul_one] using hx

lemma primaryEval_coe (T : Module.End ℂ V) (f : ℂ → ℂ)
    (β : ℂ) (x : T.maxGenEigenspace β) :
    primaryEval T f (x : V) =
      ((scalarJetEval β (primaryNilpotent T β) (finrank ℂ V) f x :
        T.maxGenEigenspace β) : V) := by
  classical
  simp only [primaryEval, LinearMap.comp_apply, LinearEquiv.coe_coe,
    primaryEquiv_coe, DirectSum.lmap_lof, primaryEquiv_symm_lof]

lemma primary_end_ext {T F G : Module.End ℂ V}
    (h : ∀ β (x : T.maxGenEigenspace β), F x = G x) : F = G := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ ⨆ β, T.maxGenEigenspace β := by rw [T.iSup_maxGenEigenspace_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun x => F x = G x) hx
    (fun β x hx => h β ⟨x,hx⟩) ?_ ?_
  · simp
  · intro x y hx hy
    simp [hx, hy]

lemma aeval_primary_restrict
    {V : Type u_63} [AddCommGroup V] [_root_.Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (β : ℂ) (p : ℂ[X])
    (x : T.maxGenEigenspace β) :
    ((Polynomial.aeval (primaryNilpotent T β +
      algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) β) p) x : V) =
      (Polynomial.aeval T p) (x : V) := by
  have hid (y : T.maxGenEigenspace β) :
      ((primaryNilpotent T β + algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) β) y : V) =
      T (y : V) := by
    change (T - algebraMap ℂ (Module.End ℂ V) β) (y : V) + β • (y : V) = T (y : V)
    simp [algebraMap_end_apply]
  have hpow (k : ℕ) (y : T.maxGenEigenspace β) :
      (((primaryNilpotent T β + algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) β)^k) y : V) =
      (T^k) (y : V) := by
    induction k generalizing y with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, hid, ih]
  simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul, hpow]

lemma primaryEval_polynomial (T : Module.End ℂ V) (p : ℂ[X]) :
    primaryEval T (fun z => p.eval z) = Polynomial.aeval T p := by
  apply primary_end_ext (T := T)
  intro β x
  rw [primaryEval_coe, scalarJetEval_polynomial (primaryNilpotent_pow T β)]
  exact aeval_primary_restrict T β p x

lemma primaryEval_mul (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ f β)
    (hg : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ g β) :
    primaryEval T (fun z => f z * g z) = primaryEval T f * primaryEval T g := by
  apply primary_end_ext (T := T)
  intro β x
  rw [Module.End.mul_apply, primaryEval_coe, primaryEval_coe, primaryEval_coe]
  by_cases hβ : β ∈ spectrum ℂ T
  · rw [scalarJetEval_mul (hf β hβ) (hg β hβ) (primaryNilpotent_pow T β),
      Module.End.mul_apply]
  · have hspace : T.maxGenEigenspace β = ⊥ := by
      by_contra hn
      have he : T.HasGenEigenvalue β (finrank ℂ V) := by
        rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
      exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
    have hx : x = 0 := by
      apply Subtype.ext
      simpa [hspace] using x.property
    simp [hx]

lemma primary_end_ext_spectrum {T F G : Module.End ℂ V}
    (h : ∀ β ∈ spectrum ℂ T, ∀ x : T.maxGenEigenspace β, F x = G x) : F = G := by
  apply primary_end_ext (T := T)
  intro β x
  by_cases hβ : β ∈ spectrum ℂ T
  · exact h β hβ x
  · have hspace : T.maxGenEigenspace β = ⊥ := by
      by_contra hn
      have he : T.HasGenEigenvalue β (finrank ℂ V) := by
        rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
      exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
    have hx : x = 0 := by
      apply Subtype.ext
      simpa [hspace] using x.property
    simp [hx]

lemma primaryEval_const (T : Module.End ℂ V) (c : ℂ) :
    primaryEval T (fun _ => c) = algebraMap ℂ (Module.End ℂ V) c := by
  simpa using primaryEval_polynomial T (C c)

lemma primaryEval_sub (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ f β)
    (hg : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ g β) :
    primaryEval T (fun z => f z - g z) = primaryEval T f - primaryEval T g := by
  apply primary_end_ext_spectrum (T := T)
  intro β hβ x
  rw [LinearMap.sub_apply, primaryEval_coe, primaryEval_coe, primaryEval_coe,
    scalarJetEval_sub (hf β hβ) (hg β hβ)]
  rfl

lemma primaryEval_eventuallyEq (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (h : ∀ β ∈ spectrum ℂ T, f =ᶠ[nhds β] g) :
    primaryEval T f = primaryEval T g := by
  apply primary_end_ext_spectrum (T := T)
  intro β hβ x
  rw [primaryEval_coe, primaryEval_coe, scalarJetEval_eventuallyEq (h β hβ)]


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DiskCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72 u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset

open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

open MeasureTheory
variable {n : Type u_73} [instFintypeN : Fintype n] [instDecidableEqN : DecidableEq n]

open scoped Kronecker

variable {m : Type u_74} [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

def entryCLM (i j : n) : Matrix n n ℂ →L[ℂ] ℂ :=
  (show Matrix n n ℂ →ₗ[ℂ] ℂ from
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

def kronCLM (B : Matrix m m ℂ) : Matrix n n ℂ →L[ℂ] Matrix (n×m) (n×m) ℂ :=
  (show Matrix n n ℂ →ₗ[ℂ] Matrix (n×m) (n×m) ℂ from
    { toFun := fun A => A ⊗ₖ B
      map_add' := fun A C => Matrix.add_kronecker A C B
      map_smul' := fun c A => Matrix.smul_kronecker c A B }).toContinuousLinearMap

def conjTransposeRCLM : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (show Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ from
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun c A => by simp }).toContinuousLinearMap


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CompleteResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_81 u_82 u_83 u_84 u_85 u_86 u_87 u_88 u_89 u_90

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator
variable {n : Type u_82} [Fintype n] [DecidableEq n]

lemma stable_spectrum_norm_lt_one {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {z : ℂ} (hz : z ∈ spectrum ℂ D) : ‖z‖ < 1 := by
  have hle : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ D := by
    rw [spectralRadius]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ D) => (‖k‖₊ : ℝ≥0∞)) z hz
  have hl : (‖z‖₊ : ℝ≥0∞) < 1 := hle.trans_lt hD
  exact_mod_cast hl

end

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker

variable {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixAnalyticEval_const (D : Matrix n n ℂ) (c : ℂ) :
    matrixAnalyticEval D (fun _ => c) = algebraMap ℂ (Matrix n n ℂ) c := by
  apply Matrix.toLinAlgEquiv'.injective
  simp [matrixAnalyticEval, primaryEval_const]

lemma matrixAnalyticEval_mul (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ g z) :
    matrixAnalyticEval D (fun z => f z * g z) = matrixAnalyticEval D f * matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, map_mul, AlgEquiv.apply_symm_apply]
  exact primaryEval_mul _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixAnalyticEval_eventuallyEq (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (h : ∀ z ∈ spectrum ℂ D, f =ᶠ[nhds z] g) :
    matrixAnalyticEval D f = matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  exact primaryEval_eventuallyEq _ (fun z hz => h z (by simpa using hz))

lemma matrixAnalyticEval_sub (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ g z) :
    matrixAnalyticEval D (fun z => f z - g z) = matrixAnalyticEval D f - matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, map_sub, AlgEquiv.apply_symm_apply]
  exact primaryEval_sub _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma scalar_matrix_inverse_analytic {a : Matrix m m ℂ} {z : ℂ}
    (hunit : IsUnit (1-z • a)) :
    AnalyticAt ℂ (fun w : ℂ => (1-w • a)⁻¹) z := by
  have ha : AnalyticAt ℂ (fun w : ℂ => (1-w • a : Matrix m m ℂ)) z := by fun_prop
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse] using
    (show AnalyticAt ℂ Ring.inverse (1-z • a) from by
      simpa only [hunit.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hunit.unit)).comp
        (f := fun w : ℂ => (1-w • a : Matrix m m ℂ)) ha


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PolynomialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_91 u_92 u_93 u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105 u_106 u_107

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_91} [Fintype n] [DecidableEq n]

def vectorize {m : Type u_92} (X : Matrix n m ℂ) : EuclideanSpace ℂ (n × m) :=
  WithLp.toLp 2 (fun p => X p.1 p.2)

def vectorizeCLM {m : Type u_93} [Fintype m] : Matrix n m ℂ →L[ℂ] EuclideanSpace ℂ (n × m) :=
  ({ toFun := vectorize
     map_add' := by intro X Y; rfl
     map_smul' := by intro z X; rfl } : Matrix n m ℂ →ₗ[ℂ] EuclideanSpace ℂ (n × m)).toContinuousLinearMap

@[simp] lemma vectorizeCLM_apply
    {n : Type u_91} [Fintype n] [DecidableEq n] {m : Type u_94} [Fintype m] (X : Matrix n m ℂ) :
    vectorizeCLM X = vectorize X := rfl

def transposedTransfer (a b c d : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  dᵀ + ((z • bᵀ) * (1-z • aᵀ)⁻¹) * cᵀ

end

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_98} {m : Type u_99} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def baseMatrixHom : Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix m m ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, one_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_CauchyEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section IntegralJets
open MeasureTheory Set Metric Complex Filter
open scoped Topology
variable {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]

def cauchyJet (s v : α → ℂ) (k : ℕ) (z : ℂ) (t : α) : ℂ :=
  (k.factorial : ℂ)*v t/(s t-z)^(k+1)

end IntegralJets

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator
variable {α : Type u_111} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {n : Type u_112} [Fintype n] [DecidableEq n]

lemma matrix_resolvent_analytic (A : Matrix n n ℂ) {s : ℂ} (hs : s ∉ spectrum ℂ A) :
    AnalyticAt ℂ (fun z : ℂ => (z • (1 : Matrix n n ℂ)-A)⁻¹) s := by
  have hu : IsUnit (s • (1 : Matrix n n ℂ)-A) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using spectrum.notMem_iff.mp hs
  have ha : AnalyticAt ℂ (fun z : ℂ => z • (1 : Matrix n n ℂ)-A) s := by fun_prop
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse] using
    (show AnalyticAt ℂ Ring.inverse (s • (1 : Matrix n n ℂ)-A) from by
      simpa only [hu.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hu.unit)).comp
      (f := fun z : ℂ => z • (1 : Matrix n n ℂ)-A) ha

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker
variable {α : Type u_113} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {n : Type u_114} {m : Type u_115} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma matrix_resolvent_continuous
    {α : Type u_113} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {n : Type u_114} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) {s : α → ℂ}
    (hs : Continuous s) (hn : ∀ t, s t ∉ spectrum ℂ A) :
    Continuous (fun t => (s t • (1 : Matrix n n ℂ)-A)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (matrix_resolvent_analytic A (hn t)).continuousAt.comp hs.continuousAt


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_BoundaryRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_116 u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128 u_129 u_130 u_131 u_132 u_133 u_134 u_135 u_136 u_137 u_138 u_139 u_140 u_141 u_142 u_143 u_144 u_145 u_146 u_147 u_148 u_149 u_150 u_151 u_152 u_153

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset


open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder


open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_150} {m : Type u_151} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma stable_disk_inverse_isUnit {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : IsUnit (1-z • D) := by
  apply spectrum.isUnit_one_sub_smul_of_lt_inv_radius
  have he : (1 : ℝ≥0∞) < (spectralRadius ℂ D)⁻¹ := by
    simpa only [inv_one] using ENNReal.inv_lt_inv.mpr hD
  exact lt_of_le_of_lt (by exact_mod_cast hz) he

lemma stable_star_disk_inverse_isUnit {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    IsUnit (1-z • Dᴴ) := by
  have hu := (stable_disk_inverse_isUnit hD (z := conj z) (by simpa using hz)).star
  simpa only [star_sub, star_one, star_smul, star_star, Matrix.star_eq_conjTranspose,
    starRingEnd_apply] using hu

def boundaryDiskDensity (D : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (1-z⁻¹ • D)⁻¹ + ((1-z⁻¹ • D)⁻¹)ᴴ - 1

lemma boundaryDiskDensity_eq {D : Matrix n n ℂ} (hD : spectralRadius ℂ D < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    boundaryDiskDensity D z =
      z • (z • (1 : Matrix n n ℂ)-D)⁻¹ + (1-z • Dᴴ)⁻¹ - 1 := by
  have hzn : z ≠ 0 := by intro h; simp [h] at hz
  have he : 1-z⁻¹ • D = z⁻¹ • (z • (1 : Matrix n n ℂ)-D) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hzn, one_smul]
  have hi : star z⁻¹ = z := by
    rw [star_inv₀]
    change (conj z)⁻¹ = z
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, norm_conj, hz]
    simp
  have hu : IsUnit (z • (1 : Matrix n n ℂ)-D) := by
    have hn : z ∉ spectrum ℂ D := by
      intro hs
      have hh := stable_spectrum_norm_lt_one hD hs
      linarith
    simpa only [Algebra.algebraMap_eq_smul_one] using (spectrum.notMem_iff.mp hn)
  let : Invertible z := invertibleOfNonzero hzn
  unfold boundaryDiskDensity
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hi,
    he, Matrix.inv_smul _ _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hu), invOf_eq_inv, inv_inv]

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PulledDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_154 u_155 u_156

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_154} [Fintype n] [DecidableEq n]

def pulledDiskDensity (D : Matrix n n ℂ) (ψ : ℂ → ℂ) (t : UnitAddCircle) : Matrix n n ℂ :=
  (((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ))) •
    boundaryDiskDensity D (ψ (t.toCircle : ℂ))

lemma pulledDiskDensity_continuous {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1) :
    Continuous (pulledDiskDensity D ψ) := by
  let s : UnitAddCircle → ℂ := fun t => ψ (t.toCircle : ℂ)
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by
    simp [Circle.norm_coe]
  have hc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) := by fun_prop
  have hs : Continuous s := hψ.continuousOn.comp_continuous hc ht
  have hv : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)) :=
    hc.mul (hψ.deriv.continuousOn.comp_continuous hc ht)
  have hn (t : UnitAddCircle) : s t ∉ spectrum ℂ D := by
    intro he
    have hh := stable_spectrum_norm_lt_one hD he
    rw [show ‖s t‖ = 1 from hb _ (ht t)] at hh
    linarith
  have hR : AnalyticOnNhd ℂ (fun z : ℂ => (1-z • Dᴴ)⁻¹) (closedBall 0 1) := by
    intro z hz
    exact scalar_matrix_inverse_analytic (stable_star_disk_inverse_isUnit hD (by simpa using hz))
  have hQ : Continuous (fun t : UnitAddCircle => boundaryDiskDensity D (s t)) := by
    apply ((hs.smul (matrix_resolvent_continuous D hs hn)).add
      (hR.continuousOn.comp_continuous hs (fun t => by simpa using (hb _ (ht t)).le))).sub
        continuous_const |>.congr
    intro t
    exact (boundaryDiskDensity_eq hD (hb _ (ht t))).symm
  exact (hv.div hs (fun t => norm_ne_zero_iff.mp (by rw [show ‖s t‖ = 1 from hb _ (ht t)]; norm_num))).smul hQ

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_UnitaryRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_157 u_158 u_159 u_160 u_161 u_162 u_163 u_164 u_165 u_166 u_167 u_168 u_169 u_170 u_171 u_172 u_173 u_174 u_175 u_176

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset


open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
section
variable {n : Type u_175} [Fintype n] [DecidableEq n]

def transfer (a b c d : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  d + z • (c * (1-z • a)⁻¹ * b)

end

open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology

open Set Filter Metric Topology


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_MetricFeasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_177 u_178 u_179 u_180 u_181 u_182 u_183

section
section
section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology

section
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
section

section Metric
variable {n : Type u_180} [Fintype n] [DecidableEq n]

def steinTerm (T : Matrix n n ℂ) (j : ℕ) : Matrix n n ℂ :=
  (T ^ j)ᴴ * T ^ j

def steinMetric (T : Matrix n n ℂ) : Matrix n n ℂ := ∑' j : ℕ, steinTerm T j

end Metric

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : Type u_182} [Fintype n] [DecidableEq n]
abbrev HermitianMatrix (n : Type u_183) [Fintype n] [DecidableEq n] :=
  selfAdjoint (Matrix n n ℂ)
def fromHSL : HSMatrix n →ₗ[ℝ] Matrix n n ℂ where
  toFun := fromHS
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def hermTrace (B A : HermitianMatrix n) : ℝ :=
  (Matrix.trace ((B : Matrix n n ℂ) * (A : Matrix n n ℂ))).re

end
end
end
end
end

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DualSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_184 u_185 u_186 u_187

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n]

def StrictPositive (H : HermitianMatrix n) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r • (1 : HermitianMatrix n) ≤ H

def metricStein (T : Matrix n n ℂ) : HermitianMatrix n →ₗ[ℝ] HermitianMatrix n where
  toFun J := ⟨(J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T,
    J.property.sub (Matrix.isHermitian_conjTranspose_mul_mul T J.property)⟩
  map_add' J K := by
    apply Subtype.ext
    change (J : Matrix n n ℂ) + K - Tᴴ * ((J : Matrix n n ℂ) + K) * T =
      ((J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T) +
      ((K : Matrix n n ℂ) - Tᴴ * (K : Matrix n n ℂ) * T)
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' a J := by
    apply Subtype.ext
    change a • (J : Matrix n n ℂ) - Tᴴ * (a • (J : Matrix n n ℂ)) * T =
      a • ((J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T)
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

abbrev MetricDualSpace (n : Type u_185) [Fintype n] [DecidableEq n] :=
  ℝ × HermitianMatrix n × HermitianMatrix n × HermitianMatrix n

def metricLinear (T : Matrix n n ℂ) :
    (ℝ × HermitianMatrix n) →ₗ[ℝ] MetricDualSpace n where
  toFun x := (x.1, x.2, x.1 • 1-x.2, metricStein T x.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul, Prod.mk_add_mk]
    congr 2
    abel_nf
  map_smul' a x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, smul_smul,
      smul_eq_mul, Prod.smul_mk, RingHom.id_apply]

def metricOffset : MetricDualSpace n := (0,-1,0,0)
def metricAffine (T : Matrix n n ℂ) (x : ℝ × HermitianMatrix n) : MetricDualSpace n :=
  metricOffset + metricLinear T x

def metricOpen (τ : ℝ) : Set (MetricDualSpace n) :=
  {x | x.1 < τ ∧ StrictPositive x.2.1 ∧ StrictPositive x.2.2.1 ∧ StrictPositive x.2.2.2}

def metricAxis0 : ℝ →ₗ[ℝ] MetricDualSpace n where
  toFun s := (s,0,0,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def metricAxis1 : HermitianMatrix n →ₗ[ℝ] MetricDualSpace n where
  toFun U := (0,U,0,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def metricAxis2 : HermitianMatrix n →ₗ[ℝ] MetricDualSpace n where
  toFun V := (0,0,V,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def metricAxis3 : HermitianMatrix n →ₗ[ℝ] MetricDualSpace n where
  toFun W := (0,0,0,W)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp] lemma hermTrace_zero_right
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (B : HermitianMatrix n) :
    hermTrace B 0 = 0 := by
  change (Matrix.trace ((B : Matrix n n ℂ) * 0)).re = 0
  simp

def metricPush (T : Matrix n n ℂ) (Z : HermitianMatrix n) : HermitianMatrix n :=
  ⟨T * (Z : Matrix n n ℂ) * Tᴴ, Matrix.isHermitian_mul_mul_conjTranspose T Z.property⟩


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DilationDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_191 u_192 u_193 u_194 u_195 u_196 u_197 u_198 u_199 u_200 u_201 u_202 u_203 u_204 u_205 u_206 u_207 u_208 u_209 u_210 u_211 u_212 u_213 u_214

open MeasureTheory
open scoped ENNReal

section
variable {T : Type u_193} {H : Type u_194} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def dilationField (S : C(T, H →L[ℂ] H)) (x : H) : C(T,H) :=
  ⟨fun t => S t x, by fun_prop⟩

def dilationLM (S : C(T, H →L[ℂ] H)) : H →ₗ[ℂ] Lp H 2 μ where
  toFun x := ContinuousMap.toLp 2 μ ℂ (dilationField S x)
  map_add' x y := by
    rw [← map_add]; congr 1
    ext t
    exact map_add (S t) x y
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul]; congr 1
    ext t
    exact map_smul (S t) c x

lemma dilationLM_coe
    {T : Type u_193} {H : Type u_194} [TopologicalSpace T] [CompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] {μ : MeasureTheory.Measure T}
    [MeasureTheory.IsFiniteMeasure μ] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : C(T,H →L[ℂ] H)) (x : H) :
    dilationLM (μ := μ) S x =ᵐ[μ] fun t => S t x :=
  ContinuousMap.coeFn_toLp (μ := μ) (dilationField S x)

lemma dilationLM_inner (S : C(T,H →L[ℂ] H)) (x y : H) :
    inner ℂ (dilationLM (μ := μ) S x) (dilationLM (μ := μ) S y) =
      inner ℂ x ((∫ t, (S t).adjoint * S t ∂μ) y) := by
  rw [L2.inner_def]
  have hcont : Continuous (fun t => (S t).adjoint * S t) := by fun_prop
  have hi : Integrable (fun t => (S t).adjoint * S t) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ t, inner ℂ (S t x) (S t y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [dilationLM_coe (μ := μ) S x, dilationLM_coe (μ := μ) S y]
        with t hx hy
      rw [hx,hy]
    _ = ∫ t, inner ℂ x (((S t).adjoint * S t) y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
    _ = _ := by
      have hiy : Integrable (fun t => ((S t).adjoint * S t) y) μ :=
        (ContinuousLinearMap.apply ℂ H y).integrable_comp hi
      rw [integral_inner hiy, ← ContinuousLinearMap.integral_apply hi]

def positiveDilation (S : C(T,H →L[ℂ] H))
    (hmass : (∫ t, (S t).adjoint * S t ∂μ) = 1) : H →ₗᵢ[ℂ] Lp H 2 μ :=
  (dilationLM S).isometryOfInner fun x y => by
    rw [dilationLM_inner (μ := μ) S x y, hmass]
    rfl

section MatrixDensity
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker
variable {n : Type u_195} {m : Type u_196} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def baseAmplification : Matrix n n ℂ →L[ℂ]
    (EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
  (show Matrix n n ℂ →ₗ[ℂ]
    (EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) from
    { toFun := fun A => Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix m m ℂ))
      map_add' := fun A B => by simp [Matrix.add_kronecker]
      map_smul' := fun c A => by simp [Matrix.smul_kronecker] }).toContinuousLinearMap

@[simp] lemma baseAmplification_one :
    baseAmplification (n := n) (m := m) (1 : Matrix n n ℂ) = 1 := by
  change Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) ((1 : Matrix n n ℂ) ⊗ₖ (1 : Matrix m m ℂ)) = 1
  rw [Matrix.one_kronecker_one, map_one]

def densityRootField (L : C(T,Matrix n n ℂ)) (hL : ∀ t, 0 ≤ L t) :
    C(T,EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
  ⟨fun t => baseAmplification (CFC.sqrt (L t)),
    baseAmplification.continuous.comp
      (CFC.continuousOn_sqrt.comp_continuous L.continuous hL)⟩

end MatrixDensity

end

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker

section
variable {n : Type u_197} {m : Type u_198} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def coefficientMatrixHom : Matrix m m ℂ →⋆ₐ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun B := (1 : Matrix n n ℂ) ⊗ₖ B
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ A B
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, one_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  map_star' B := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]

def coefficientAmplification : Matrix m m ℂ →L[ℂ]
    (EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
  ((Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.comp
    coefficientMatrixHom.toAlgHom.toLinearMap).toContinuousLinearMap

end

section
open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker
variable {T : Type u_199} [TopologicalSpace T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  {n : Type u_200} {m : Type u_201} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def coefficientMultiplierField (F : C(T,Matrix m m ℂ)) :
    C(T,EuclideanSpace ℂ (n × m) →L[ℂ] EuclideanSpace ℂ (n × m)) :=
  ⟨fun t => coefficientAmplification (F t), coefficientAmplification.continuous.comp F.continuous⟩

end

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
section
variable {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def weightedDensity (L : Matrix n n ℂ) (X Y : Matrix n m ℂ) : Matrix m m ℂ :=
  (Xᴴ * L * Y)ᵀ

def weightedDensityCLM (X Y : Matrix n m ℂ) : Matrix n n ℂ →L[ℂ] Matrix m m ℂ :=
  (show Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ from
    { toFun := fun L => weightedDensity L X Y
      map_add' := fun L M => by simp [weightedDensity,Matrix.mul_add,Matrix.add_mul]
      map_smul' := fun c L => by simp [weightedDensity] }).toContinuousLinearMap

lemma continuous_weightedDensity
    {n : Type u_206} {m : Type u_207} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {T : Type u_211} [TopologicalSpace T]
    {L : T → Matrix n n ℂ} (hL : Continuous L) (X Y : Matrix n m ℂ) :
    Continuous (fun t => weightedDensity (L t) X Y) :=
  (weightedDensityCLM X Y).continuous.comp hL

end

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DensityTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


universe u_215 u_216 u_217 u_218 u_219 u_220 u_221 u_222 u_223 u_224 u_225 u_226 u_227 u_228 u_229 u_230 u_231 u_232 u_233 u_234 u_235 u_236 u_237 u_238 u_239 u_240

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Metric Complex Filter
open scoped Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace

open scoped ComplexConjugate InnerProductSpace

open Set Metric Filter Complex
open scoped Topology


open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology

open Set Filter Metric Complex
open scoped Topology


open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator


open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open MeasureTheory

namespace CompleteCrouzeix

section
open MeasureTheory
open scoped Matrix.Norms.L2Operator Kronecker ComplexConjugate InnerProductSpace
variable {T : Type u_236} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
  [BorelSpace T] {μ : Measure T} [IsFiniteMeasure μ]
  {n : Type u_237} {m : Type u_238} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def toHSCLM : Matrix m m ℂ →L[ℂ] HSMatrix m :=
  LinearMap.toContinuousLinearMap
  { toFun := toHS
    map_add' := by intros; ext ⟨i,j⟩; rfl
    map_smul' := by intros; ext ⟨i,j⟩; rfl }

def densityField (L : C(T,Matrix n n ℂ)) (X Y : Matrix n m ℂ) :
    Lp (HSMatrix m) 2 μ :=
  ContinuousMap.toLp 2 μ ℂ
    ⟨fun t => toHS (weightedDensity (L t) X Y),
      toHSCLM.continuous.comp (continuous_weightedDensity L.continuous X Y)⟩

def tensorTesting (X Y : Matrix n m ℂ) : Matrix (n × m) (n × m) ℂ →L[ℂ] ℂ :=
  (innerSL ℂ (vectorize Y)).comp
    ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (n × m)) (vectorize X)).comp
      (Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.toContinuousLinearMap)

end

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate Matrix.Norms.L2Operator Kronecker
local instance instFactLtRealOfNat_solutions_52 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {m : Type u_239} {n : Type u_240} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def hsTraceLp (u : C(UnitAddCircle,Matrix m m ℂ)) : MatrixCircleL2 (m := m) :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    ⟨fun t => toHS (u t),toHSCLM.continuous.comp u.continuous⟩

def matrixFourierTrace (ij : m × m) (k : ℤ) : C(UnitAddCircle,Matrix m m ℂ) :=
  ⟨fun t => Matrix.single ij.1 ij.2 (fourier k t),by
    apply continuous_matrix
    intro i j
    simp only [Matrix.single_apply]
    split_ifs <;> fun_prop⟩

end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_ConformalWinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CompleteCrouzeix


open Set Filter Metric Complex
open scoped Topology ComplexConjugate

open MeasureTheory Set Complex
open scoped Topology Real

open MeasureTheory Set Complex
open scoped Topology

open MeasureTheory Set Complex Metric
open scoped Topology
local instance instFactLtRealOfNat_solutions_54 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DomainCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_244

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
def G : ℂ → ℂ := exteriorMap D.exterior.leading D.exterior.constant D.exterior.regular
def ψ : ℂ → ℂ := D.interior.toDisk ∘ D.G
lemma circle_collar {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) : D.exterior.radius⁻¹ < ‖t‖ := by
  rw [mem_sphere_zero_iff_norm.mp ht]
  exact inv_lt_one_of_one_lt₀ D.exterior.radius_gt
lemma G_analytic : AnalyticOnNhd ℂ D.G (sphere 0 1) :=
  (exteriorCoordinate_analytic D.exterior).mono (fun _ ht => D.circle_collar ht)
lemma G_boundary {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) : D.G t ∈ frontier D.domain :=
  D.exterior.boundary_image ▸ mem_image_of_mem D.G ht
lemma toDisk_maps : MapsTo D.interior.toDisk D.domain (ball 0 1) := by
  intro z hz
  exact D.interior.image_domain ▸ mem_image_of_mem D.interior.toDisk hz
lemma disk_boundary {z : ℂ} (hz : z ∈ frontier D.domain) :
    D.interior.toDisk z ∈ sphere (0:ℂ) 1 := by
  obtain ⟨w,hw,he⟩ := D.interior.inverse_sphere_frontier D.isOpen ▸ hz
  rw [← he,D.interior.right_inverse w (D.interior.closedDisk_subset (sphere_subset_closedBall hw))]
  exact hw
lemma ψ_analytic : AnalyticOnNhd ℂ D.ψ (sphere 0 1) := by
  intro t ht
  exact (D.interior.analytic_to _ (D.interior.closure_subset (D.G_boundary ht).1)).comp
    (D.G_analytic t ht)
lemma ψ_boundary {t : ℂ} (ht : t ∈ sphere (0:ℂ) 1) : ‖D.ψ t‖ = 1 :=
  mem_sphere_zero_iff_norm.mp (D.disk_boundary (D.G_boundary ht))
lemma G_ne_interior {z : ℂ} (hz : z ∈ D.domain) {t : ℂ} (ht : 1 ≤ ‖t‖) : D.G t ≠ z := by
  intro he
  rcases lt_or_eq_of_le ht with hlt|heq
  · apply D.exterior.outside t hlt
    change D.G t ∈ closure D.domain
    rw [he]
    exact subset_closure hz
  · have hb := D.G_boundary (mem_sphere_zero_iff_norm.mpr heq.symm)
    rw [D.isOpen.frontier_eq] at hb
    exact hb.2 (he.symm ▸ hz)
lemma support_circle (w t : Circle) :
    0 ≤ (conj ((t:ℂ)*deriv D.G t)*(D.G t-D.G w)).re :=
  D.support t t.2 _ (D.G_boundary w.2).1
end AdmissibleDomain

variable {n : Type u_244} [Fintype n] [DecidableEq n]
lemma spectrum_matrixAnalyticEval_subset (A : Matrix n n ℂ) {f : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z) :
    spectrum ℂ (matrixAnalyticEval A f) ⊆ f '' spectrum ℂ A := by
  intro w hw
  by_contra hn
  have hne (z : ℂ) (hz : z ∈ spectrum ℂ A) : w-f z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hn ⟨z,hz,h.symm⟩)
  have hg (z : ℂ) (hz : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun v => w-f v) z :=
    analyticAt_const.sub (hf z hz)
  have hh (z : ℂ) (hz : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun v => (w-f v)⁻¹) z :=
    (hg z hz).inv (hne z hz)
  have he : matrixAnalyticEval A (fun v => (w-f v)*(w-f v)⁻¹) = 1 := by
    rw [matrixAnalyticEval_eventuallyEq A (g := fun _ => 1)]
    · simp [matrixAnalyticEval_const]
    · intro z hz
      filter_upwards [(hg z hz).continuousAt.eventually_ne (hne z hz)] with v hv
      exact mul_inv_cancel₀ hv
  rw [matrixAnalyticEval_mul A hg hh,matrixAnalyticEval_sub A (fun _ _ => analyticAt_const) hf,
    matrixAnalyticEval_const] at he
  have hu : IsUnit (algebraMap ℂ (Matrix n n ℂ) w-matrixAnalyticEval A f) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det he
    rw [Matrix.det_mul,hz,zero_mul,Matrix.det_one] at hh
    exact zero_ne_one hh
  exact (spectrum.notMem_iff.mpr hu) hw

lemma matrixAnalyticEval_stable [Nonempty n] (A : Matrix n n ℂ) {f : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hb : ∀ z ∈ spectrum ℂ A, ‖f z‖ < 1) :
    spectralRadius ℂ (matrixAnalyticEval A f) < 1 := by
  apply spectrum.spectralRadius_lt_of_forall_lt (matrixAnalyticEval A f) (r := 1)
  intro z hz
  obtain ⟨w,hw,rfl⟩ := spectrum_matrixAnalyticEval_subset A hf hz
  exact_mod_cast hb w hw
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_BoundaryCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_245 u_246

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance instFactLtRealOfNat : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
def kernel : AnalyticBidiskKernel := actualExteriorKernel D.exterior.radius_gt
  D.exterior.leading_ne D.exterior.analytic_regular D.exterior.injective
  D.exterior.noncritical D.support_circle
variable {n : Type u_245} {m : Type u_246} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
def cauchy : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m) := matrixFourier.cauchy D.kernel.matrixM
def trace (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    C(UnitAddCircle,Matrix m m ℂ) :=
  ⟨fun t => v (D.G t.toCircle), (hv.comp D.G_analytic (fun _ ht => (D.G_boundary ht).1)).continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property)⟩

def resolventField (A : Matrix n n ℂ) (t : UnitAddCircle) : Matrix n n ℂ :=
  ((t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ)) •
    (D.G t.toCircle • (1:Matrix n n ℂ)-A)⁻¹
lemma curve_continuous : Continuous (fun t : UnitAddCircle => D.G t.toCircle) :=
  D.G_analytic.continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property)
lemma normal_continuous : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)*deriv D.G t.toCircle) :=
  (continuous_subtype_val.comp AddCircle.continuous_toCircle).mul
    (D.G_analytic.deriv.continuousOn.comp_continuous
      (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property))
lemma resolvent_continuous (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    Continuous (D.resolventField A) :=
  D.normal_continuous.smul (matrix_resolvent_continuous A D.curve_continuous
    (fun t hz => D.G_ne_interior (hA hz) (by simp [Circle.norm_coe]) rfl))
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DensityAdjoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_247 u_248

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
local instance instFactLtRealOfNat_solutions_55 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_TestingAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_249 u_250

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type u_249} {m : Type u_250} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def hermitianField (K : C(UnitAddCircle,Matrix n n ℂ)) : C(UnitAddCircle,Matrix n n ℂ) :=
  ⟨fun t => K t+(K t)ᴴ,by fun_prop⟩
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_DensityIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_251 u_252

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance instFactLtRealOfNat_1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_PositiveDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u_253 u_254

namespace CompleteCrouzeix
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace AdmissibleDomain

section
variable (D : AdmissibleDomain)
local instance instFactLtRealOfNat_2 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {n : Type u_253} {m : Type u_254} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype m] [DecidableEq m]
lemma coordinate_analytic_spectrum (D : AdmissibleDomain)
    {n : Type u_253} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ D.interior.toDisk z :=
  fun z hz => D.interior.analytic_to z (D.interior.closure_subset (subset_closure (hA hz)))
lemma coordinate_stable (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    spectralRadius ℂ (matrixAnalyticEval A D.interior.toDisk) < 1 :=
  matrixAnalyticEval_stable A (D.coordinate_analytic_spectrum A hA)
    (fun _z hz => mem_ball_zero_iff.mp (D.toDisk_maps (hA hz)))
def positiveDensity (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    C(UnitAddCircle,Matrix n n ℂ) :=
  ⟨pulledDiskDensity (matrixAnalyticEval A D.interior.toDisk) D.ψ,
    pulledDiskDensity_continuous (D.coordinate_stable A hA) D.ψ_analytic (fun _ ht => D.ψ_boundary ht)⟩
end
end AdmissibleDomain
end CompleteCrouzeix

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.NumericalRange_OrderedDensities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_255 u_256

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
local instance instFactLtRealOfNat_solutions_56 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
end CompleteCrouzeix

end

end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_ExteriorSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology ComplexConjugate

lemma convex_exteriorCoordinate_support {U : Set ℂ}
    (hU : IsOpen U) (hcv : Convex ℝ U) (hne : U.Nonempty)
    (E : ExteriorCoordinate U) :
    ∀ t ∈ sphere (0 : ℂ) 1, ∀ z ∈ closure U,
      0 ≤ (conj (t * deriv (exteriorMap E.leading E.constant E.regular) t) *
        (exteriorMap E.leading E.constant E.regular t - z)).re := by
  let G := exteriorMap E.leading E.constant E.regular
  have hreg : interior (closure U) = U :=
    (hcv.interior_closure_eq_interior_of_nonempty_interior
      (by rwa [hU.interior_eq])).trans hU.interior_eq
  have hbound (w : ℂ) (hw : ‖w‖ = 1) : G w ∈ frontier U :=
    E.boundary_image ▸ mem_image_of_mem G (mem_sphere_zero_iff_norm.mpr hw)
  intro t ht z hz
  have htn : ‖t‖ = 1 := mem_sphere_zero_iff_norm.mp ht
  have htX : E.radius⁻¹ < ‖t‖ := by
    rw [htn]
    exact inv_lt_one_of_one_lt₀ E.radius_gt
  have hGt : DifferentiableAt ℂ G t :=
    (exteriorCoordinate_analytic E t htX).differentiableAt
  have hpnot : G t ∉ interior (closure U) := by
    rw [hreg]
    exact (hU.frontier_eq ▸ hbound t htn).2
  obtain ⟨L, hLne, hL⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hcv.closure hpnot (by rwa [hreg])
  let N := t * deriv G t
  have hN : N ≠ 0 := mul_ne_zero
    (by intro he; simp [he] at htn) (E.noncritical t htX)
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => exp ((s:ℂ)*I)*t)
      (exp ((s:ℂ)*I)*I*t) s := by
    simpa using (((hasDerivAt_id s).ofReal_comp.mul_const I).cexp.mul_const t)
  have he : HasDerivAt (fun s : ℝ => G (exp ((s:ℂ)*I)*t)) (I*N) 0 := by
    simpa only [N,ofReal_zero,zero_mul,Complex.exp_zero,one_mul,
      Function.comp_def,smul_eq_mul,mul_assoc] using
      (show HasDerivAt G (deriv G t) (exp (((0:ℝ):ℂ)*I)*t)
        from by simpa using hGt.hasDerivAt).scomp 0 (hd 0)
  have heL : HasDerivAt (fun s : ℝ => L (G (exp ((s:ℂ)*I)*t))) (L (I*N)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 he
  have hmL : IsLocalMax (fun s : ℝ => L (G (exp ((s:ℂ)*I)*t))) 0 := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [ofReal_zero,zero_mul,Complex.exp_zero,one_mul] using
      hL _ (hbound _ (by rw [norm_mul,norm_exp_ofReal_mul_I,htn,one_mul])).1
  have htan : L (I*N) = 0 := hmL.hasDerivAt_eq_zero heL
  have hdr : HasDerivAt (fun r : ℝ => (r:ℂ)*t) t 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).ofReal_comp.mul_const t
  have hger : HasDerivAt (fun r : ℝ => G ((r:ℂ)*t)) N 1 := by
    simpa only [N,ofReal_one,one_mul,Function.comp_def,smul_eq_mul] using
      (show HasDerivAt G (deriv G t) (((1:ℝ):ℂ)*t)
        from by simpa using hGt.hasDerivAt).scomp 1 hdr
  have hgrL : HasDerivAt (fun r : ℝ => L (G ((r:ℂ)*t))) (L N) 1 :=
    L.hasFDerivAt.comp_hasDerivAt 1 hger
  have hrc : ContinuousAt (fun r : ℝ => ‖(r:ℂ)*t‖) 1 := by fun_prop
  have hnear : ∀ᶠ r : ℝ in 𝓝 1, E.radius⁻¹ < ‖(r:ℂ)*t‖ :=
    hrc.eventually (lt_mem_nhds (by simpa using htX))
  have hm : IsLocalMaxOn (fun r : ℝ => L (G ((r:ℂ)*t))) (Iic 1) 1 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      (lt_mem_nhds (zero_lt_one : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hrx hr0 hr1
    change r ≤ 1 at hr1
    by_cases hre : r = 1
    · subst r; exact le_rfl
    · have hrlt : r < 1 := lt_of_le_of_ne hr1 hre
      have hball : (r:ℂ)*t ∈ ball (0:ℂ) 1 := by
        simp only [mem_ball_zero_iff,norm_mul,Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos hr0,htn,mul_one]
        exact hrlt
      simpa only [ofReal_one,one_mul] using
        hL _ (subset_closure ((E.interior_iff _ hrx).mpr hball))
  have hy : (-1:ℝ) ∈ posTangentConeAt (Iic (1:ℝ)) 1 := by
    apply mem_posTangentConeAt_of_segment_subset
    apply (convex_Iic (1:ℝ)).segment_subset <;> simp
  have hnonpos := hm.hasFDerivWithinAt_nonpos hgrL.hasFDerivAt.hasFDerivWithinAt hy
  simp only [ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul] at hnonpos
  have hLN : 0 < L N := by
    have hn : L N ≠ 0 := by
      intro hzero
      apply hLne
      ext w
      change L w = 0
      rw [real_linear_normal hN htan w,hzero,zero_div,zero_mul]
    exact lt_of_le_of_ne (by linarith) (Ne.symm hn)
  have hle : L (z-G t) ≤ 0 := by
    rw [map_sub]
    exact sub_nonpos.mpr (hL z hz)
  rw [real_linear_normal hN htan (z-G t)] at hle
  have hratio : 0 < L N / ‖N‖^2 :=
    div_pos hLN (sq_pos_of_pos (norm_pos_iff.mpr hN))
  have hle' : (conj N*(z-G t)).re ≤ 0 := by nlinarith
  change 0 ≤ (conj N*(G t-z)).re
  have heq : (conj N*(G t-z)).re = -(conj N*(z-G t)).re := by
    rw [show G t-z = -(z-G t) by ring,mul_neg,neg_re]
  rw [heq]
  linarith
end CompleteCrouzeix
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_GeometryBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology

def LocalClosedAnalyticBoundary (U : Set ℂ) (p : ℂ) : Prop :=
  ∃ χ : ℂ → ℂ, χ 0 = p ∧ AnalyticAt ℂ χ 0 ∧ deriv χ 0 ≠ 0 ∧
    (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ U ↔ 0 < z.im) ∧
    (∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier U) ∧
    (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ closure U ↔ 0 ≤ z.im)

end CompleteCrouzeix
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_SharedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance instFactLtRealOfNat_5 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

end AdmissibleDomain
end CompleteCrouzeix
end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_SharedMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance instFactLtRealOfNat_6 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def analyticRangeMaximum {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) : ℝ :=
  sSup ((fun z => ‖v z‖) '' closure D.domain)

end AdmissibleDomain
end CompleteCrouzeix
end
end

end OAI
end

section
-- module Solutions.OAIW2_StructCrouzeix.StructuralCrouzeix_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker
namespace StructuralCrouzeix
open CompleteCrouzeix

lemma IsAdmissible.compact_closure {U : Set ℂ} (hU : IsAdmissible U) :
    IsCompact (closure U) :=
  isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hU.bounded.closure⟩

def bundleDomain {U : Set ℂ} (hU : IsAdmissible U) (a : ℂ) (ha : a ∈ U)
    (f : DiskCoordinate U a) (G : ExteriorCoordinate U) : AdmissibleDomain where
  domain := U
  isOpen := hU.isOpen
  convex := hU.convex
  compact_closure := hU.compact_closure
  base := a
  base_mem := ha
  interior := f
  exterior := G
  support := convex_exteriorCoordinate_support hU.isOpen hU.convex hU.nonempty G

end StructuralCrouzeix
end

end OAI
end


