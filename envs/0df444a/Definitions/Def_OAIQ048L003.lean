-- Prove2me | Definitions.Def_OAIQ048L003
-- name    : OAIQ048L003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:23:08.430165+00:00
-- url     : https://prove2.me/theorems/75d3c705-3cc7-4e28-911c-61d77d8c903c
-- title:
--   Definitions bundle OAIQ048L003 of the split of OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 75 declarations of OpenAI's Lean: 53 definitions and 22 theorems. The definitions and types are `OAI.LogConcaveSampling.TensorEnergy.arrayMatrix`, `OAI.LogConcaveSampling.TensorExpression.physicalBase`, `OAI.LogConcaveSampling.affinePotential`, `OAI.LogConcaveSampling.anchorGauge`, `OAI.LogConcaveSampling.arrayCoordinateLift`, `OAI.LogConcaveSampling.centeringMeanArray`, `OAI.LogConcaveSampling.clampedProbabilityDerivative`, `OAI.LogConcaveSampling.clampedProbabilityVelocity`, `OAI.LogConcaveSampling.conditionalMeanArray`, `OAI.LogConcaveSampling.gibbsKernel`, `OAI.LogConcaveSampling.harmonicKernel`, `OAI.LogConcaveSampling.harmonicMeanBudget`, `OAI.LogConcaveSampling.harmonicMeanDefect`, `OAI.LogConcaveSampling.harmonicNormalizedTerm`, `OAI.LogConcaveSampling.harmonicRmsBudget`, `OAI.LogConcaveSampling.harmonicSkew`, `OAI.LogConcaveSampling.harmonicStationaryMoment`, `OAI.LogConcaveSampling.identityOutputProjection`, `OAI.LogConcaveSampling.interpolationLaw`, `OAI.LogConcaveSampling.interpolationResidual`, `OAI.LogConcaveSampling.iterEnergyBudget`, `OAI.LogConcaveSampling.iterTensorLie`, `OAI.LogConcaveSampling.jointCorrectionArray`, `OAI.LogConcaveSampling.jointCumulant`, `OAI.LogConcaveSampling.jointInterpolationLaw`, `OAI.LogConcaveSampling.jointPosteriorLaw`, `OAI.LogConcaveSampling.kernelCorrectionPicard`, `OAI.LogConcaveSampling.kernelNormalizedTerm`, `OAI.LogConcaveSampling.kernelTransportAction`, `OAI.LogConcaveSampling.kernelValueRmsBudget`, `OAI.LogConcaveSampling.lieInside`, `OAI.LogConcaveSampling.meanOutputProjection`, `OAI.LogConcaveSampling.noisedLaw`, `OAI.LogConcaveSampling.normalizedTensor`, `OAI.LogConcaveSampling.posteriorKernel`, `OAI.LogConcaveSampling.posteriorPotential`, `OAI.LogConcaveSampling.probabilityFlow`, `OAI.LogConcaveSampling.probabilityInitialRms`, `OAI.LogConcaveSampling.probabilityRmsBudget`, `OAI.LogConcaveSampling.probabilityTransport` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `LogConcave_Analysis_AffinePotential`, `LogConcave_Analysis_CenteringPotential`, `LogConcave_Analysis_InterpolationPotential`, `LogConcave_Analysis_Law`, `LogConcave_Complexity_HarmonicCorrectionBudget`, `LogConcave_Complexity_KernelValueRmsBudget`, `LogConcave_Complexity_OccurrenceBudget`, `LogConcave_Complexity_ProbabilityRmsBudget`, `LogConcave_JetEstimates_ArrayMatrix`, `LogConcave_JetEstimates_Bound`, `LogConcave_JetEstimates_ContractLeftSplit`, `LogConcave_JetEstimates_Extension`, `LogConcave_JetEstimates_ProperSplit`, `LogConcave_JetEstimates_TensorExpression`, `LogConcave_JetEstimates_WireStep`, `LogConcave_Numerics_KernelCorrectionPicard`, `LogConcave_Sampling_AnchorGauge`, `LogConcave_Sampling_ConditionalMeanArray`, `LogConcave_Sampling_CoordinateProjection`, `LogConcave_Sampling_DirectionalBasisSum`, `LogConcave_Sampling_HarmonicKernel`, `LogConcave_Sampling_HarmonicMeanDefect`, `LogConcave_Sampling_HarmonicStationaryMoment`, `LogConcave_Sampling_IdentityOutputEmbedding`, `LogConcave_Sampling_InterpolationResidual`, `LogConcave_Sampling_IterTensorLie`, `LogConcave_Sampling_Jet`, `LogConcave_Sampling_JointInterpolationLaw`, `LogConcave_Sampling_JointPosition`, `LogConcave_Sampling_KernelTransportAction`, `LogConcave_Sampling_NormalizedTensor`, `LogConcave_Sampling_ProbabilityInitialRms`, `LogConcave_Sampling_ProbabilityNodes`, `LogConcave_Sampling_ProbabilityNormalizedTerm`, `LogConcave_Sampling_ProbabilityVelocity`, `LogConcave_Sampling_ScoreAugmented`, `LogConcave_Sampling_ScoreSlots`, `LogConcave_Sampling_SkewCenteringField`, `LogConcave_Sampling_SpatialTransport`, `LogConcave_Sampling_TensorGrad`, `LogConcave_Sampling_TensorVector`, `LogConcave_Sampling_TerminalBackward`, `LogConcave_Sampling_TerminalMean`, `LogConcave_Sampling_TimeBump`, `LogConcave_Sampling_TransportCorrectionMajorant`, `LogConcave_Sampling_VelocityJointLip`.
--
--   **Imports.** It imports the published bundle `Def_LogConcaveQuery`; the bundles `OAIQ048L000` and `OAIQ048L001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ048L004`; the statements `OAI.LogConcaveSampling.kernelCorrectionPicard_rms` and `OAI.LogConcaveSampling.probabilityAnchored_marginal_rms`; the proofs of `OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy` and `OAI.LogConcaveSampling.stationaryMeanTarget_law`.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L000
import Definitions.Def_OAIQ048L001

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_AffinePotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Function
open scoped Classical NNReal RealInnerProductSpace

variable {d : ℕ}

def affinePotential (V : Point d → ℝ) (a : Point d) (s : ℝ) : Point d → ℝ :=
  fun z => V (a+s • z)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace TensorEnergy
open scoped BigOperators

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

lemma Bound.bilinear {A : I → J → ℝ} {C : ℝ} (h : Bound A C) (u : I → ℝ) (v : J → ℝ) :
    (∑ i, ∑ j, u i*A i j*v j)^2 ≤ C*(∑ i, (u i)^2)*(∑ j, (v j)^2) := by
  simp only [mul_assoc,← Finset.mul_sum]
  exact (dot_sq u (fun i => ∑ j, A i j*v j)).trans
    ((mul_le_mul_of_nonneg_left (h v) (energy_nonneg u)).trans_eq (by ring))

lemma Bound.transpose {A : I → J → ℝ} {C : ℝ} (h : Bound A C) (hC : 0 ≤ C) :
    Bound (fun j i => A i j) C := by
  apply bound_of_bilinear hC
  intro u v
  have hh := h.bilinear v u
  rw [Finset.sum_comm] at hh
  convert hh using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

universe u v w

end TensorEnergy
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma jointPosition_basis {d : ℕ} (i : Fin d) :
    jointPosition d ((EuclideanSpace.basisFun (Fin d) ℝ) i)=
      (EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ) (Sum.inl i) := by
  simp only [EuclideanSpace.basisFun_apply]
  ext j
  cases j with
  | inl j =>
    change (EuclideanSpace.single i (1:ℝ)) j=(EuclideanSpace.single (Sum.inl i : Fin d ⊕ Fin d) (1:ℝ)) (Sum.inl j)
    simp [PiLp.single_apply]
  | inr j =>
    change (0:ℝ)=(EuclideanSpace.single (Sum.inl i : Fin d ⊕ Fin d) (1:ℝ)) (Sum.inr j)
    simp

lemma jointField_basis {d : ℕ} (i : Fin d) :
    jointField d ((EuclideanSpace.basisFun (Fin d) ℝ) i)=
      (EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ) (Sum.inr i) := by
  simp only [EuclideanSpace.basisFun_apply]
  ext j
  cases j with
  | inl j =>
    change (0:ℝ)=(EuclideanSpace.single (Sum.inr i : Fin d ⊕ Fin d) (1:ℝ)) (Sum.inl j)
    simp
  | inr j =>
    change (EuclideanSpace.single i (1:ℝ)) j=(EuclideanSpace.single (Sum.inr i : Fin d ⊕ Fin d) (1:ℝ)) (Sum.inr j)
    simp [PiLp.single_apply]

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SkewCenteringField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

def skewCenteringField {d : ℕ} (K : Point d → Point d →L[ℝ] Point d)
    (m : Point d → Point d) (s : ℝ) (p : Point d × Point d) : Point d × Point d :=
  (-s⁻¹ • (K p.1).adjoint p.2,s⁻¹ • m p.1)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_InterpolationPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

def interpolationLaw {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ) : Measure (Point d) :=
  ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
    (fun p => ρ • p.1+Real.sqrt (1-ρ^2) • p.2)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

lemma Bound.submatrix {A : I → J → ℝ} {C : ℝ} (h : Bound A C)
    (e : K ↪ I) (f : L ↪ J) : Bound (fun k l => A (e k) (f l)) C := by
  classical
  intro v
  have hh := h (zeroExtension f v)
  simp only [dot_zeroExtension,energy_zeroExtension] at hh
  apply le_trans _ hh
  let g : I → ℝ := fun i => (∑ l,A i (f l)*v l)^2
  change (∑ k,g (e k)) ≤ ∑ i,g i
  rw [← Finset.sum_image (s := Finset.univ) (f := g) e.injective.injOn]
  apply Finset.sum_le_univ_sum_of_nonneg
  intro i
  exact sq_nonneg _

end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ProperSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators Classical Matrix.Norms.L2Operator

variable {I J : Type*} [Fintype I] [Fintype J]

lemma bound_norm (A : Matrix I J ℝ) : Bound A (‖A‖^2) := by
  intro v
  have h := A.l2_opNorm_mulVec (WithLp.toLp 2 v)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  change ‖(WithLp.toLp 2 (fun i => ∑j,A i j*v j) : EuclideanSpace ℝ I)‖^2 ≤
    (‖A‖*‖(WithLp.toLp 2 v : EuclideanSpace ℝ J)‖)^2 at hs
  simpa only [mul_pow,EuclideanSpace.real_norm_sq_eq] using hs

lemma Bound.norm_le {A : Matrix I J ℝ} {M : ℝ} (hM : 0≤M) (h : Bound A (M^2)) :
    ‖A‖≤M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg v))).mp
  change ‖(WithLp.toLp 2 (fun i => ∑j,A i j*(WithLp.ofLp v) j) : EuclideanSpace ℝ I)‖^2 ≤
    (M*‖v‖)^2
  simpa only [mul_pow,EuclideanSpace.real_norm_sq_eq] using h (WithLp.ofLp v)

lemma bound_iff_norm_le {A : Matrix I J ℝ} {M : ℝ} (hM : 0≤M) :
    Bound A (M^2) ↔ ‖A‖≤M := by
  refine ⟨Bound.norm_le hM,fun h => ?_⟩
  intro v
  exact (bound_norm A v).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) h 2) (energy_nonneg v))

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_WireStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

lemma Bound.comp {A : I → J → ℝ} {B : J → K → ℝ} {C D : ℝ}
    (hA : Bound A C) (hB : Bound B D) (hC : 0≤C) :
    Bound (fun i k => ∑ j,A i j*B j k) (C*D) := by
  intro v
  have he (i : I) : (∑ k,(∑ j,A i j*B j k)*v k)=
      ∑ j,A i j*(∑ k,B j k*v k) := by
    simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
    exact Finset.sum_comm
  simp_rw [he]
  exact (hA _).trans ((mul_le_mul_of_nonneg_left (hB v) hC).trans_eq (by ring))

lemma bound_identity [DecidableEq I] : Bound (fun i j : I => if i=j then (1:ℝ) else 0) 1 := by
  intro v
  simp

lemma Bound.contract {P : Type*} [Fintype P]
    {A : I → J × P → ℝ} {B : P × K → L → ℝ} {C D : ℝ}
    (hA : Bound A C) (hB : Bound B D) (hC : 0≤C) :
    Bound (fun (i : I × K) (j : J × L) => ∑ p,A i.1 (j.1,p)*B (p,i.2) j.2) (C*D) := by
  classical
  have h₁ := hA.kronecker (bound_identity (I:=K)) hC
  have h₂ := (bound_identity (I:=J)).kronecker hB (by norm_num)
  have h₂' := h₂.reindex (Equiv.prodAssoc J P K) (Equiv.refl (J×L))
  have hh := h₁.comp h₂' (by simpa using hC)
  simp only [mul_one,one_mul] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  funext i j
  simp only [Fintype.sum_prod_type,Equiv.prodAssoc_apply,Equiv.refl_apply]
  simp [mul_ite,ite_mul]

lemma Bound.entry_sq {A : I → J → ℝ} {C : ℝ} (hA : Bound A C) (i : I) (j : J) :
    (A i j)^2 ≤ C := by
  classical
  have hh := hA (fun k => if k=j then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    ite_pow,one_pow,zero_pow (by decide : (2:ℕ)≠0)] at hh
  exact (Finset.single_le_sum (fun k _ => sq_nonneg (A k j)) (Finset.mem_univ i)).trans hh

end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ContractLeftSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators Matrix.Norms.L2Operator

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

lemma Bound.finite_sum_norm {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]
    {A : J → Matrix O I ℝ} {M : J → ℝ}
    (hM : ∀j,0≤M j) (h : ∀j,Bound (A j) ((M j)^2)) :
    Bound (fun o i => ∑j,A j o i) ((∑j,M j)^2) := by
  have he : (fun o i => ∑j,A j o i)=∑j,A j := by
    ext o i
    exact (Matrix.sum_apply o i Finset.univ A).symm
  rw [he]
  apply (bound_iff_norm_le (Finset.sum_nonneg (fun j _ => hM j))).mpr
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => (h j).norm_le (hM j)))

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_NormalizedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace NNReal

universe u

def normalizedTensor {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    (y : Point d) {S : Type u} [Fintype S] (mask : S → Bool) (l : List S)
    (c : S → Fin d) : ℝ :=
  ((1-ρ^2)^(Fintype.card S-1))⁻¹ * JetCalculus.jet
    (fun s => EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
      (conditionalSlotEmbedding d mask c s)) l
    (fun z => Real.log (Appell.laplace (jointConditionalLaw F x r ρ y L)
      (fun _ => (1:ℝ)) z)) 0

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal Topology

def jointCumulant {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    {ι : Type*} (v : ι → JointPoint d) (l : List ι) (y : Point d) : ℝ :=
  JetCalculus.jet v l (fun θ => Real.log
    (Appell.laplace (jointConditionalLaw F x r ρ y L) (fun _ => (1:ℝ)) θ)) 0

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_DirectionalBasisSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators RealInnerProductSpace

lemma growth_of_bounded {d : ℕ} {f : Point d → ℝ} {B : ℝ}
    (hB : 0≤B) (h : ∀x,|f x|≤B) : HasPolynomialGrowth f := by
  refine ⟨B,hB,0,fun x => ?_⟩
  simp only [pow_zero,Real.norm_eq_abs]
  exact (h x).trans (by linarith)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_JointInterpolationLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def jointInterpolationLaw {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ) :=
  (((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
    (fun p => (p.1,ρ • p.1+Real.sqrt (1-ρ^2) • p.2)))

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_InterpolationResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

def interpolationResidual {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (p : Point d × Point d) : Point d :=
  (1/(1-ρ^2)) • (p.1-ρ • p.2)+r • conditionalFieldMean F x r ρ p.2

end LogConcaveSampling

open Function MeasureTheory Set Filter
open scoped Topology NNReal

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityVelocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open Set Function MeasureTheory Filter
open scoped Topology

def clampedProbabilityVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ)
    (hT : 0≤T) (t : ℝ) (z : Point d) : Point d :=
  probabilityVelocity F x r (projIcc 0 T hT t) z

def clampedProbabilityDerivative {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ)
    (hT : 0≤T) (t : ℝ) (z : Point d) : Point d →L[ℝ] Point d :=
  (fderiv ℝ (uncurry (probabilityVelocity F x r)) ((projIcc 0 T hT t:ℝ),z)).comp
    (ContinuousLinearMap.inr ℝ ℝ (Point d))

lemma clampedProbabilityVelocity_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    Continuous (uncurry (clampedProbabilityVelocity F x r T hT0)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hcm := (projIcc 0 T hT0 p.1).2
  have hp : (projIcc 0 T hT0 p.1:ℝ)^2<1 := by
    have hh := (probability_time hcm.1 (hcm.2.trans_lt hT1)).1
    linarith
  exact (probabilityVelocity_joint_smooth hF x hr (by linarith) (_,p.2) hp).continuousAt.comp (f:=fun q : ℝ × Point d => ((projIcc 0 T hT0 q.1:ℝ),q.2))
    ((continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).continuousAt.prodMk
      continuous_snd.continuousAt)

lemma clampedProbabilityVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (t : ℝ) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩
      (clampedProbabilityVelocity F x r T hT0 t) :=
  probabilityVelocity_lipschitz hF x hr hl (projIcc 0 T hT0 t).2 hT1

lemma clampedProbabilityVelocity_eq {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T : ℝ) (hT : 0≤T) {t : ℝ} (ht : t∈Icc 0 T) (z : Point d) :
    clampedProbabilityVelocity F x r T hT t z=probabilityVelocity F x r t z := by
  simp [clampedProbabilityVelocity,projIcc_of_mem _ ht]
end LogConcaveSampling
namespace LogConcaveSampling
open Set Function MeasureTheory Filter ProbabilityTheory
open scoped Topology

def probabilityFlow {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (z : Point d) : Point d :=
  GlobalODE.flow (fun t _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 t)
    (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1) ⟨0,le_rfl,hT0⟩ z T

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TimeBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function Filter Metric
open scoped Topology NNReal

lemma smoothTimeClip_eq {T t : ℝ} (hT0 : 0≤T) (hT1 : T<1) (ht : t∈Icc 0 T) :
    smoothTimeClip hT0 hT1 t=t := by
  have hh : timeBump hT0 hT1 t=1 := by
    apply (timeBump hT0 hT1).one_of_mem_closedBall
    rw [mem_closedBall,Real.dist_eq,abs_le]
    change -((T+1)/4)≤t-T/2 ∧ t-T/2≤(T+1)/4
    constructor <;> linarith [ht.1,ht.2]
  simp [smoothTimeClip,hh]

def probabilityTransport {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (z : Point d) : Point d :=
  GlobalODE.flow (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1) s z t

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalBackward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma smoothTimeClip_mem_extended (t : ℝ) :
    smoothTimeClip hT0 hT1 t∈Ioo (-1) (T+1) := by
  have hh := smoothTimeClip_sq_lt hT0 hT1 t
  constructor <;> nlinarith

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_TensorExpression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorExpression

def physicalBase {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ)
    (q : ℕ) (c : Fin (q+2) → Fin d) (y : Point d) : ℝ :=
  normalizedTensor F x r ρ L y (fun i => decide (i=Fin.last (q+1))) (List.finRange (q+2)) c

end TensorExpression
end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ScoreAugmented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorEnergy
open scoped Matrix.Norms.L2Operator in
lemma Bound.add_norm {I O : Type*} [Fintype I] [Fintype O]
    {A B : O → I → ℝ} {M N : ℝ} (hA : Bound A (M^2)) (hB : Bound B (N^2))
    (hM : 0≤M) (hN : 0≤N) : Bound (fun o i => A o i+B o i) ((M+N)^2) := by
  change Bound (A+B) ((M+N)^2)
  apply (bound_iff_norm_le (add_nonneg hM hN)).mpr
  exact (norm_add_le _ _).trans (add_le_add (hA.norm_le hM) (hB.norm_le hN))

end TensorEnergy

def scoreAugmented {d : ℕ} {K : Type} (H : Point d → ℝ) (l : List K)
    (y : Point d) (c : (K ⊕ Unit) ⊕ Unit → Fin d) : ℝ :=
  JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl (Sum.inl k)))) l
    (directional (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl (Sum.inr ()))))
      (directional (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))) H)) y

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ScoreSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

def spatialInside {K S : Type} {d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K)
    (c : K ⊕ S → Fin d) (z : Fin d) : Point d → ℝ :=
  JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k))) l
    (F (Sum.elim (fun s => c (Sum.inr s)) (fun _ => z)))

def spatialAdjointLeading {K S : Type} {d : ℕ}
    (H : Point d → ℝ) (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K)
    (y : Point d) (c : K ⊕ S → Fin d) : ℝ :=
  tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ) (spatialInside F l c) y

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TerminalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function Filter MeasureTheory
open scoped NNReal Topology RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

def terminalMean (p : ℝ × Point d) : Point d :=
  conditionalFieldMean F x r (smoothTimeClip hT0 hT1 p.1)
    (terminalBackward hF x hr.le hl hT0 hT1 p)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_CoordinateProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Function
open scoped Classical BigOperators
open TensorEnergy

def arrayCoordinateLift {S : Type} {d D : ℕ} (e : Fin d ↪ Fin D)
    (ι : S → Fin d ↪ Fin D) (F : (S → Fin d) → Point d → ℝ) :
    (S → Fin D) → Point D → ℝ :=
  fun c y => TensorEnergy.zeroExtend (slotEmbedding ι) (fun a => F a (coordinateProjection e y)) c

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_SpatialTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function Filter Metric
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 ≤ r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma smoothTimeClip_eventually_eq {t : ℝ} (ht : t∈Icc 0 T) :
    smoothTimeClip hT0 hT1=ᶠ[𝓝 t] id := by
  have hb : t∈ball (T/2) ((T+1)/4) := by
    rw [mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith [ht.1,ht.2]
  filter_upwards [isOpen_ball.mem_nhds hb] with u hu
  have hh : timeBump hT0 hT1 u=1 := (timeBump hT0 hT1).one_of_mem_closedBall
    (show u∈closedBall (T/2) ((T+1)/4) from ball_subset_closedBall hu)
  simp [smoothTimeClip,hh]

def spatialTransport (s : Icc (0:ℝ) T) (p : ℝ × Point d) : Point d :=
  GlobalODE.flow (a:= -1) (b:=T+1)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
    ⟨s,by constructor <;> linarith [s.2.1,s.2.2]⟩ p.2 (smoothTimeClip hT0 hT1 p.1)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TensorGrad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

def tensorGrad {S : Type} {d : ℕ} (F : (S → Fin d) → Point d → ℝ)
    (c : S ⊕ Unit → Fin d) : Point d → ℝ :=
  directional (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))) (F (fun s => c (Sum.inl s)))

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

def lieInside {S : Type} {d : ℕ} (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (c : S ⊕ Unit → Fin d) (y : Point d) : ℝ :=
  singleContract (fun a => A a y) (fun a => tensorGrad F a y) (c ∘ Equiv.sumComm Unit S)

def tensorLie {S : Type} {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (c : S → Fin d) : Point d → ℝ :=
  tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ) (fun z => lieInside A F (Sum.elim c (fun _ => z)))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_IterTensorLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical NNReal BigOperators
open TensorEnergy

def iterTensorLie {S : Type} {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ) :
    ℕ → (S → Fin d) → Point d → ℝ
  | 0 => F
  | n+1 => tensorLie H A (iterTensorLie H A F n)

def iterEnergyBudget (K : ℝ) (C D B : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => B
  | n+1 => adjointEnergyBudget K D (productEnergyBudget C (iterEnergyBudget K C D B n))

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TensorVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

def tensorVector {S : Type} {d : ℕ} (F : (S → Fin d) → Point d → ℝ) (y : Point d) :
    EuclideanSpace ℝ (S → Fin d) := WithLp.toLp 2 (fun c => F c y)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ConditionalMeanArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

def conditionalMeanArray {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ)
    (c : Unit → Fin d) (y : Point d) : ℝ :=
  inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c ())) (conditionalFieldMean F x r T y)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_CenteringPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

def centeringMeanArray {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ) :
    (Unit → Fin (d+d)) → Point (d+d) → ℝ :=
  arrayCoordinateLift (leftCoordinates d d) (fun _ => leftCoordinates d d)
    (conditionalMeanArray F x r T)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_HarmonicKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

def harmonicKernel (d : ℕ) : Point d → Point d →L[ℝ] Point d :=
  fun _ => -(ContinuousLinearMap.id ℝ (Point d))
def harmonicSkew (d : ℕ) := jointSkew (harmonicKernel d) 1

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_TransportCorrectionMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

def vectorArray {d : ℕ} (f : Point d → Point d) (c : Unit → Fin d) (y : Point d) : ℝ :=
  inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c ())) (f y)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy

def jointCorrectionArray {d : ℕ} (f : Point d → Point d) :
    (Unit → Fin (d+d)) → Point (d+d) → ℝ :=
  arrayCoordinateLift (leftCoordinates d d) (fun _ => leftCoordinates d d) (vectorArray f)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_HarmonicCorrectionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

def harmonicMeanBudget (n : ℕ) : ℝ :=
  iterEnergyBudget harmonicGradientBound (fun _ => 2)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (normalizedTensorMajorant (k+1) 1)^2) n 0

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

attribute [local instance] OAI.LogConcaveSampling.instDecidableEqUnit_solutions_7
def meanOutputProjection (d : ℕ) : EuclideanSpace ℝ (Unit → Fin (d+d)) →L[ℝ] Point d :=
  finiteCoordinateProjection (meanOutputEmbedding d)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_HarmonicMeanDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

def harmonicMeanDefect {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T z : ℝ)
    (Ξ : Point (d+d) → ℝ → Point (d+d)) (n : ℕ) (i : Fin (n+1)) (y : Point (d+d)) : Point d :=
  let M := fun t => conditionalFieldMean F x r T (productPointEquiv d d (Ξ y (z*t))).1
  z • (∫t in 0..probabilityNodes n i,Real.sin (z*(probabilityNodes n i-t)) • M t)-
    ∑j,harmonicWeight n z i j • M (probabilityNodes n j)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_HarmonicStationaryMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped NNReal RealInnerProductSpace

def harmonicStationaryMoment {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ) : ℝ :=
  ∫y,‖conditionalFieldMean F x r T (productPointEquiv d d y).1‖^2
    ∂gibbs (centeringPotential F x r T)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityInitialRms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

def probabilityInitialRms {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) (r : ℝ) : ℝ :=
  Real.sqrt (2*(terminalTransportConstant*(r*‖primitiveField F x r 0‖+
    (lam:ℝ)*r^2*Real.pi*Real.sqrt d))^2+2*(terminalTransportConstant*((lam:ℝ)*r^2))^2*d)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_ProbabilityRmsBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

def probabilityRmsBudget {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam A : ℝ≥0) (r h C : ℝ) (k n N : ℕ) : ℝ :=
  4*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)+
    (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*probabilityInitialRms F x lam r)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Numerics_KernelCorrectionPicard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal

def kernelCorrectionPicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h z : ℝ) (n N : ℕ) (s e : ProbabilityNode T h n)
    (p : Point d × Point d) : Point d :=
  let b := probabilityAnchoredPicard F x r T h n N e p.1 s
  let w := harmonicPicard F x r (probabilityNodeTime T h n s) z n N (b,p.2) (Fin.last n)
  probabilityAnchoredPicard F x r T h n (N+1) s w e-w

def harmonicRmsBudget {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam A : ℝ≥0) (r R t z C : ℝ) (n N : ℕ) : ℝ :=
  2*(r*t)*Real.sqrt (4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
    ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)))+
    (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(r*t)*Real.sqrt (harmonicStationaryMoment F x r t)

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_KernelTransportAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal

def kernelTransportAction {d : ℕ} (f : Point d → Point d) (p : Point (d+d)) : Point d :=
  (fderiv ℝ f (productPointEquiv d d p).1) (productPointEquiv d d p).2-
    (productPointEquiv d d p).2

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_KernelValueRmsBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def kernelValueRmsBudget {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam Ap Ah Lp : ℝ≥0) (r R ρ h z C J : ℝ) (k n N : ℕ) : ℝ :=
  2*(2*(Lp*probabilityMeanLipschitz lam r):ℝ≥0)^2*
    (32*(probabilityRmsBudget F x lam Ap r h C k n N)^2+
      2*(harmonicRmsBudget F x lam Ah r R ρ z J n N)^2)+
    2*(probabilityRmsBudget F x lam Ap r h C k n (N+1))^2

end LogConcaveSampling

end

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_JetEstimates_ArrayMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace

namespace TensorEnergy

def arrayMatrix {d : ℕ} (a : (Unit ⊕ Unit → Fin d) → ℝ) : Point d →L[ℝ] Point d :=
  ∑i, ∑j, a (Sum.elim (fun _ => i) (fun _ => j)) • coordinateRankOne d i j

end TensorEnergy

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_Jet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal RealInnerProductSpace

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0 < r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

def terminalActionChain : ℕ → ℝ × (Point d × Point d) → Point d
  | 0 => fun p => (terminalJacobian hF x hr hl hT0.le hT1 (p.1,p.2.1)-
      ContinuousLinearMap.id ℝ (Point d)) p.2.2
  | n+1 => fun p => TimeJet.jet (terminalJacobian hF x hr hl hT0.le hT1) (n+1) (p.1,p.2.1) p.2.2

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_IdentityOutputEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

attribute [local instance] OAI.LogConcaveSampling.identityOutputEmbeddingDecidableEqUnit
def identityOutputProjection (d : ℕ) : EuclideanSpace ℝ (Unit → Fin d) →L[ℝ] Point d :=
  finiteCoordinateProjection (identityOutputEmbedding d)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_ProbabilityNormalizedTerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def harmonicNormalizedTerm (n : ℕ) (R z : ℝ) : ℝ :=
  4*(|z|^(n+1)/(n.factorial:ℝ))*(R⁻¹)^(2*(n+1))*Real.sqrt (harmonicMeanBudget (n+1))

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Quadrature
open scoped NNReal BigOperators

def kernelNormalizedTerm (d k n N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R h z : ℝ) : ℝ :=
  probabilityNormalizedTerm d k n h+harmonicNormalizedTerm n R z+
    (numericalContractionCoefficient Ap Ah Lp*((lam:ℝ)*r^2))^N

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Analysis_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical NNReal RealInnerProductSpace

variable {d : ℕ}

def posteriorPotential (V : Point d → ℝ) (h : ℝ) (y z : Point d) : ℝ :=
  V z+‖z-y‖^2/(2*h)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

lemma measurable_gibbs_family {H : A → Point d → ℝ}
    (hH : Measurable (uncurry H)) : Measurable (fun a => gibbs (H a)) := by
  have hw : Measurable (fun p : A × Point d => gibbsDensity (H p.1) p.2) := by
    unfold gibbsDensity
    exact (Real.measurable_exp.comp hH.neg).ennreal_ofReal
  have hp : Measurable (fun a => partition (H a)) := hw.lintegral_prod_right
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [gibbs,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs]
  change Measurable (fun a => (partition (H a))⁻¹ * ∫⁻z in s,gibbsDensity (H a) z)
  exact hp.inv.mul (hw.lintegral_prod_right (ν:=volume.restrict s))

def gibbsKernel (H : A → Point d → ℝ) (hH : Measurable (uncurry H)) : Kernel A (Point d) where
  toFun a := gibbs (H a)
  measurable' := measurable_gibbs_family hH

def posteriorKernel (V : Point d → ℝ) (hV : Admissible V) (h : ℝ) : Kernel (Point d) (Point d) :=
  gibbsKernel (posteriorPotential V h) (by
    have hm := hV.smooth.continuous.measurable
    unfold uncurry posteriorPotential
    fun_prop)

def jointPosteriorLaw (V : Point d → ℝ) (h : ℝ) : Measure (Point d × Point d) :=
  ((gibbs V).prod (stdGaussian (Point d))).map (fun p => (p.1,p.1+Real.sqrt h • p.2))

def noisedLaw (V : Point d → ℝ) (h : ℝ) : Measure (Point d) :=
  ((gibbs V).prod (stdGaussian (Point d))).map (fun p => p.1+Real.sqrt h • p.2)

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_VelocityJointLip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

def velocityJointLip (n m : ℕ) (A lam : ℝ≥0) (r T h ψ s : ℝ) : ℝ≥0 :=
  2*(‖-(r*s)⁻¹‖₊*((∑i,‖terminalQuadratureWeight T h n i‖₊)*
    ((∑i : Fin (m+1),‖derivativeWeight (angleNodes m) i/ψ‖₊)*
      (16*(A*probabilityMeanLipschitz lam r))))+
    ‖s⁻¹‖₊*Real.toNNReal ((Real.pi^2/2)*T*((lam:ℝ)*r)))

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Complexity_OccurrenceBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Quadrature MeanTree
open scoped Topology Classical

def sourceOccurrenceBudget (a b : ℝ) (n m N nc Nc d : ℕ) : ℕ :=
  meanWork (Fintype.card (ProbabilityNode (sourceCorrelation a d) ((d:ℝ)^(-b)) (n+1)))
    (n+2) m N nc Nc 0 0 0+
  (Fintype.card (ProbabilityNode (sampleCorrelation ((d:ℝ)^(-a))) ((d:ℝ)^(-b)) (n+1))+1)^N

end LogConcaveSampling

end

end

end OAI
end

section
-- module Solutions.OAIQ048_LC.LogConcave_Sampling_AnchorGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

def anchorGauge (C : ℝ) (z : Point d) : ℝ := 1+C+‖z‖

end LogConcaveSampling

end

end

end OAI
end


