-- Prove2me | Definitions.Def_OAIQ019N002
-- name    : OAIQ019N002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:58:02.799959+00:00
-- url     : https://prove2.me/theorems/136d4ec2-89ab-41c2-98a2-53a92b34bd11
-- title:
--   Definitions bundle OAIQ019N002 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 28 definitions, 1 inductive type or structure, 3 instances and 21 theorems. The definitions and types are `OAI.NuclearUltrapower.HasKazhdanGap`, `OAI.NuclearUltrapower.HasNoFiniteDimensionalSubrep`, `OAI.NuclearUltrapower.HilbertSchmidt`, `OAI.NuclearUltrapower.HilbertUltraproduct.boundedUnitary`, `OAI.NuclearUltrapower.PositiveTrace`, `OAI.NuclearUltrapower.SL3Certificate.q0`, `OAI.NuclearUltrapower.SL3Certificate.q1`, `OAI.NuclearUltrapower.SL3Certificate.q10`, `OAI.NuclearUltrapower.SL3Certificate.q100`, `OAI.NuclearUltrapower.SL3Certificate.q101`, `OAI.NuclearUltrapower.SL3Certificate.q102`, `OAI.NuclearUltrapower.SL3Certificate.q103`, `OAI.NuclearUltrapower.SL3Certificate.q104`, `OAI.NuclearUltrapower.bottomEnergy`, `OAI.NuclearUltrapower.boundedUnitarySeq`, `OAI.NuclearUltrapower.completionUnitary`, `OAI.NuclearUltrapower.crossOperator`, `OAI.NuclearUltrapower.dualIsometry`, `OAI.NuclearUltrapower.dualUnitary`, `OAI.NuclearUltrapower.finiteOperatorTensor`, `OAI.NuclearUltrapower.normUltrapowerMk`, `OAI.NuclearUltrapower.operatorLift`, `OAI.NuclearUltrapower.operatorPositiveTrace`, `OAI.NuclearUltrapower.polarSpectralOrder`, `OAI.NuclearUltrapower.polarUnitary`, `OAI.NuclearUltrapower.representedUnitary`, `OAI.NuclearUltrapower.tensorOperator`, `OAI.NuclearUltrapower.tupleEnergy`, `OAI.NuclearUltrapower.unitaryReplacement`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_HilbertSchmidt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertSchmidt.lean), [`NuclearUltrapower_HilbertTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertTensor.lean), [`NuclearUltrapower_HilbertUltraproduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertUltraproduct.lean), [`NuclearUltrapower_InducedApproximation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/InducedApproximation.lean), [`NuclearUltrapower_NormUltrapower`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/NormUltrapower.lean), [`NuclearUltrapower_NuclearFiniteness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/NuclearFiniteness.lean), [`NuclearUltrapower_SOSCertificate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSCertificate.lean).
--
--   **Imports.** It imports the published bundle `Def_NuclearUltrapower`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ019N040` and `OAIQ019N041`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_NuclearUltrapower

section
-- module Solutions.OAIQ019_Nuc.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertSchmidt
attribute [-instance] _root_.OAI.NuclearUltrapower.instStarNormUltrapower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End

namespace NuclearUltrapower

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The conjugate Hilbert space realized as the strong dual. Its norm is the
existing dual norm, not a new norm on the same space. -/
instance strongDualInner : InnerProductSpace ℂ (StrongDual ℂ K) where
  inner f g := ⟪(InnerProductSpace.toDual ℂ K).symm g,
    (InnerProductSpace.toDual ℂ K).symm f⟫_ℂ
  norm_sq_eq_re_inner f := by
    rw [← norm_sq_eq_re_inner, (InnerProductSpace.toDual ℂ K).symm.norm_map]
  conj_inner_symm f g := inner_conj_symm _ _
  add_left f g h := by simp only [map_add, inner_add_right]
  smul_left f g r := by simp only [map_smulₛₗ, inner_smul_right]

@[simp] theorem dual_inner_toDual (x : K) (f : StrongDual ℂ K) :
    ⟪InnerProductSpace.toDual ℂ K x, f⟫_ℂ = f x := by
  change ⟪(InnerProductSpace.toDual ℂ K).symm f,
    (InnerProductSpace.toDual ℂ K).symm (InnerProductSpace.toDual ℂ K x)⟫_ℂ = f x
  simp

/-- Algebraic finite-rank operators represented by Hilbert tensors. -/
def tensorOperator : K ⊗[ℂ] StrongDual ℂ K →ₗ[ℂ] (K →L[ℂ] K) :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun f => f.smulRight x
          map_add' := by intro f g; ext v; simp [add_smul]
          map_smul' := by intro c f; ext v; simp [mul_smul] }
      map_add' := by intro x y; ext f v; simp [smul_add]
      map_smul' := by intro c x; ext f v; simp [smul_smul, mul_comm] }

omit [CompleteSpace K] in
@[simp] theorem tensorOperator_tmul (x : K) (f : StrongDual ℂ K) (v : K) :
    tensorOperator (x ⊗ₜ[ℂ] f) v = f v • x := rfl

-- A shortcut for instance synthesis through the tensor's core norm.
instance tensorBoundedSMul : IsBoundedSMul ℂ (K ⊗[ℂ] StrongDual ℂ K) :=
  NormedSpace.toIsBoundedSMul (𝕜 := ℂ) (E := K ⊗[ℂ] StrongDual ℂ K)

/-- Hilbert--Schmidt vectors, with the actual tensor Hilbert norm. -/
abbrev HilbertSchmidt (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] := UniformSpace.Completion (K ⊗[ℂ] StrongDual ℂ K)

/-- The conjugate (contragredient) unitary on the strong dual. -/
def dualUnitary (u : K ≃ₗᵢ[ℂ] K) : StrongDual ℂ K ≃ₗᵢ[ℂ] StrongDual ℂ K :=
  ((InnerProductSpace.toDual ℂ K).symm.trans u).trans (InnerProductSpace.toDual ℂ K)

@[simp] theorem dualUnitary_toDual (u : K ≃ₗᵢ[ℂ] K) (v : K) :
    dualUnitary u (InnerProductSpace.toDual ℂ K v) = InnerProductSpace.toDual ℂ K (u v) := by
  simp [dualUnitary]

@[simp] theorem dualUnitary_apply (u : K ≃ₗᵢ[ℂ] K) (f : StrongDual ℂ K) (v : K) :
    dualUnitary u f v = f (u.symm v) := by
  obtain ⟨x, rfl⟩ := (InnerProductSpace.toDual ℂ K).surjective f
  rw [dualUnitary_toDual]
  change ⟪u x, v⟫_ℂ = ⟪x, u.symm v⟫_ℂ
  exact u.inner_map_eq_flip x v

/-- Extension of a linear isometry equivalence to metric completions. -/
def completionUnitary {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (u : E ≃ₗᵢ[ℂ] F) :
    UniformSpace.Completion E ≃ₗᵢ[ℂ] UniformSpace.Completion F :=
  u.toLinearEquiv.extendOfIsometry
    UniformSpace.Completion.toComplₗᵢ.toLinearMap UniformSpace.Completion.toComplₗᵢ.toLinearMap
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
    (fun x => by simp)

@[simp] theorem completionUnitary_coe {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (u : E ≃ₗᵢ[ℂ] F) (x : E) :
    completionUnitary u (x : UniformSpace.Completion E) = (u x : UniformSpace.Completion F) := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

variable {Γ : Type*} [Group Γ]

/-- The absence of nonzero finite-dimensional subrepresentations, without separability. -/
def HasNoFiniteDimensionalSubrep (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) : Prop :=
  ∀ W : Submodule ℂ K, W ≠ ⊥ →
    (∀ g : Γ, ∀ ξ ∈ W, σ g ξ ∈ W) → ¬ FiniteDimensional ℂ W

end NuclearUltrapower

noncomputable section
open scoped CStarAlgebra

namespace NuclearUltrapower

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]

/-- A finite positive trace. This definition is used only for the finite-rank
part of the Powers--Størmer argument; no trace is assumed in the main theorem. -/
structure PositiveTrace (A : Type*) [CStarAlgebra A] [PartialOrder A] where
  toLinearMap : A →ₗ[ℝ] ℝ
  nonneg : ∀ a : A, 0 ≤ a → 0 ≤ toLinearMap a
  cyclic : ∀ a b : A, toLinearMap (a * b) = toLinearMap (b * a)

namespace PositiveTrace

instance instCoeFunForallReal : CoeFun (PositiveTrace A) (fun _ => A → ℝ) := ⟨fun τ => τ.toLinearMap⟩

@[simp] theorem map_add (τ : PositiveTrace A) (a b : A) :
    τ (a + b) = τ a + τ b := τ.toLinearMap.map_add a b
@[simp] theorem map_sub (τ : PositiveTrace A) (a b : A) :
    τ (a - b) = τ a - τ b := τ.toLinearMap.map_sub a b
@[simp] theorem map_zero (τ : PositiveTrace A) : τ 0 = 0 := τ.toLinearMap.map_zero

end PositiveTrace
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The finite-dimensional Hilbert tensor representing an operator. -/
def finiteOperatorTensor [FiniteDimensional ℂ K] (T : K →L[ℂ] K) :
    K ⊗[ℂ] StrongDual ℂ K :=
  ∑ i, T (stdOrthonormalBasis ℂ K i) ⊗ₜ[ℂ]
    InnerProductSpace.toDual ℂ K (stdOrthonormalBasis ℂ K i)

/-- The real part of the ordinary trace on finite-dimensional operators. -/
def operatorPositiveTrace [FiniteDimensional ℂ K] : PositiveTrace (K →L[ℂ] K) where
  toLinearMap :=
    { toFun T := (LinearMap.trace ℂ K T.toLinearMap).re
      map_add' := by intro T U; simp
      map_smul' := by intro r T; simp }
  nonneg T hT := (Complex.nonneg_iff.mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hT).toLinearMap.trace_nonneg).1
  cyclic T U := congrArg Complex.re (LinearMap.trace_mul_comm ℂ T.toLinearMap U.toLinearMap)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Functorial conjugate Hilbert-space embedding. -/
def dualIsometry (f : F →ₗᵢ[ℂ] K) : StrongDual ℂ F →ₗᵢ[ℂ] StrongDual ℂ K :=
  (InnerProductSpace.toDual ℂ K).toLinearIsometry.comp
    (f.comp (InnerProductSpace.toDual ℂ F).symm.toLinearIsometry)

@[simp] theorem dualIsometry_toDual (f : F →ₗᵢ[ℂ] K) (x : F) :
    dualIsometry f (InnerProductSpace.toDual ℂ F x) = InnerProductSpace.toDual ℂ K (f x) := by
  simp [dualIsometry]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The rectangular operator associated with an algebraic Hilbert tensor. -/
def crossOperator : E ⊗[ℂ] K →ₗ[ℂ] (StrongDual ℂ E →L[ℂ] K) :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun y => (NormedSpace.inclusionInDoubleDual ℂ E x).smulRight y
          map_add' := by intro y z; ext f; simp [smul_add]
          map_smul' := by intro c y; ext f; simp [smul_smul, mul_comm] }
      map_add' := by intro x y; ext z f; simp [add_smul]
      map_smul' := by intro c x; ext y f; simp [mul_smul] }

omit [CompleteSpace E] [CompleteSpace K] in
@[simp] theorem crossOperator_tmul (x : E) (y : K) (f : StrongDual ℂ E) :
    crossOperator (x ⊗ₜ[ℂ] y) f = f x • y := rfl

/-- Conjugation/compression by an isometric Hilbert-space embedding. -/
def operatorLift (f : F →ₗᵢ[ℂ] K) (T : F →L[ℂ] F) : K →L[ℂ] K :=
  f.toContinuousLinearMap ∘L T ∘L f.toContinuousLinearMap.adjoint

@[simp] theorem operatorLift_mul (f : F →ₗᵢ[ℂ] K) (T U : F →L[ℂ] F) :
    operatorLift f (T * U) = operatorLift f T * operatorLift f U := by
  have hf (x : F) : f.toContinuousLinearMap.adjoint (f x) = x :=
    congrArg (fun T : F →L[ℂ] F => T x) f.adjoint_comp_self
  ext x
  change f (T (U (f.toContinuousLinearMap.adjoint x))) =
    f (T (f.toContinuousLinearMap.adjoint (f (U (f.toContinuousLinearMap.adjoint x)))))
  rw [hf]

theorem operatorLift_nonneg (f : F →ₗᵢ[ℂ] K) {T : F →L[ℂ] F} (hT : 0 ≤ T) :
    0 ≤ operatorLift f T :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (((ContinuousLinearMap.nonneg_iff_isPositive _).mp hT).conj_adjoint f.toContinuousLinearMap)

@[simp] theorem operatorLift_sqrt (f : F →ₗᵢ[ℂ] K) {T : F →L[ℂ] F} (hT : 0 ≤ T) :
    operatorLift f (CFC.sqrt T) = CFC.sqrt (operatorLift f T) := by
  symm
  apply (CFC.sqrt_eq_iff _ _ (operatorLift_nonneg f hT)
    (operatorLift_nonneg f (CFC.sqrt_nonneg T))).mpr
  rw [← operatorLift_mul, CFC.sqrt_mul_sqrt_self T hT]

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact standing Kazhdan-gap convention in the tensor-norm formulation. -/
def HasKazhdanGap {Γ : Type u} [Group Γ] (S : Finset Γ) (κ : ℝ) : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)),
    (∀ ξ : H, (∀ g : Γ, ρ g ξ = ξ) → ξ = 0) →
    ∀ ξ : H, κ * ‖ξ‖ ^ 2 ≤ ∑ s ∈ S, ‖ρ s ξ - ξ‖ ^ 2

end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertTensor
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower

section CompletionMaps
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Completion does not change an operator norm. -/
@[simp] theorem completed_norm (f : E →L[ℂ] F) : ‖f.completion‖ = ‖f‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le f.completion.continuous.norm (continuous_const.mul continuous_norm)
    | ih x => simpa using f.le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa using f.completion.le_opNorm (x : UniformSpace.Completion E)
end CompletionMaps

end NuclearUltrapower

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertUltraproduct
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal

namespace NuclearUltrapower

/-- Bounded scalar families have a genuine ultralimit. No countable completeness
or separability hypothesis is used. -/
theorem hilbert_tendsto_ultralimit_of_bounded {ι : Type u} (ω : Ultrafilter ι)
    {F : Type v} [NormedAddCommGroup F] [ProperSpace F] (f : ι → F)
    (hf : ∃ C : ℝ, ∀ i, ‖f i‖ ≤ C) :
    Tendsto f (ω : Filter ι) (𝓝 (limUnder (ω : Filter ι) f)) := by
  obtain ⟨C, hC⟩ := hf
  apply tendsto_nhds_limUnder
  obtain ⟨x, _, hx⟩ := (isCompact_closedBall (0 : F) C).ultrafilter_le_nhds'
    (Ultrafilter.map f ω) (by
      change {i | f i ∈ Metric.closedBall 0 C} ∈ (ω : Filter ι)
      exact Filter.Eventually.of_forall (fun i => by simpa using hC i))
  exact ⟨x, hx⟩

end NuclearUltrapower

end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NuclearFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal

namespace NuclearUltrapower
namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    (ω : Ultrafilter ι)

/-- A unitary family is uniformly bounded, independently of Hilbert dimension. -/
def boundedUnitary (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) : lp (fun i => E i →L[ℂ] E i) ∞ :=
  ⟨fun i => (U i : E i →L[ℂ] E i), memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul, LinearIsometryEquiv.coe_coe''] using ((U i).norm_map x).le⟩⟩

end HilbertUltraproduct
end NuclearUltrapower

noncomputable section

open scoped InnerProductSpace Topology
open Filter

namespace NuclearUltrapower
variable {Γ : Type u} {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The quadratic form of the matching Laplacian. -/
def tupleEnergy (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (x : E) : ℝ :=
  ∑ s ∈ S, ‖U s x - x‖ ^ 2

variable [Nontrivial E]

/-- Bottom Rayleigh energy, equal to the bottom of the matching spectrum in a
faithful representation. This definition retains arbitrary Hilbert dimension. -/
def bottomEnergy (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) : ℝ :=
  sInf {r | ∃ x : E, ‖x‖ = 1 ∧ r = tupleEnergy S U x}

end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InducedApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u
section InducedVectors
variable {Γ B E : Type u}
  [Group Γ]
  [CStarAlgebra B]
  [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]
  [CompleteSpace E]
  (H : Subgroup Γ)
  [Fintype (Γ ⧸ H)]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E))
  (u : Γ → unitary B)

def representedUnitary (b : unitary B) : E ≃ₗᵢ[ℂ] E :=
  Unitary.linearIsometryEquiv (Unitary.map (StarMonoidHom.ofClass ρ) b)

@[simp] theorem representedUnitary_toCLM (b : unitary B) :
    (representedUnitary ρ b : E →L[ℂ] E) = ρ b := rfl

end InducedVectors
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NormUltrapower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

universe u

noncomputable section
open Filter
open scoped Topology

namespace NuclearUltrapower
variable {A : Type*} [CStarAlgebra A]

local instance polarSpectralOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance polarSpectralOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- The polar retraction on the open set of invertible elements. -/
def polarUnitary (a : A) (ha : IsUnit a) : unitary A := by
  let q := CFC.sqrt (star a * a)
  have hq : IsUnit q := (CFC.isUnit_sqrt_iff _ (star_mul_self_nonneg a)).mpr
    (ha.star.mul ha)
  have hqi : IsUnit (Ring.inverse q) := by
    rw [← hq.unit_spec, Ring.inverse_unit]
    exact Units.isUnit _
  refine ⟨a * Ring.inverse q, ((ha.mul hqi).mem_unitary_iff_star_mul_self).mpr ?_⟩
  have hqstar : star q = q := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have hi : star (Ring.inverse q) = Ring.inverse q := by
    rw [← Ring.inverse_star, hqstar]
  rw [star_mul, hi]
  calc
    (Ring.inverse q * star a) * (a * Ring.inverse q) =
      Ring.inverse q * (star a * a) * Ring.inverse q := by simp only [mul_assoc]
    _ = Ring.inverse q * (q * q) * Ring.inverse q := by
      rw [show q * q = star a * a from CFC.sqrt_mul_sqrt_self _]
    _ = 1 := by
      rw [← mul_assoc (Ring.inverse q) q q, Ring.inverse_mul_cancel _ hq,
        one_mul, Ring.mul_inverse_cancel _ hq]

@[simp] theorem polarUnitary_value (a : A) (ha : IsUnit a) :
    (polarUnitary a ha : A) = a * Ring.inverse (CFC.sqrt (star a * a)) := rfl

/-- A unitary-valued extension of polar retraction. Away from invertibles it
is set equal to 1. -/
def unitaryReplacement (a : A) : unitary A := by
  classical
  exact if h : IsUnit a then polarUnitary a h else 1

end NuclearUltrapower

namespace NuclearUltrapower
section UltrapowerDefinition
variable (B : Type u) [CStarAlgebra B] (ω : Ultrafilter ℕ)

theorem ultraRel_iff_norm (x y : BoundedSeq B) :
    ultraRel B ω x y ↔
      Tendsto (fun n => ‖x n - y n‖) (ω : Filter ℕ) (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero

/-- The canonical quotient map, preserving the unit and the complex star algebra. -/
def normUltrapowerMk : BoundedSeq B →⋆ₐ[ℂ] NormUltrapower B ω where
  __ := (ultraCon B ω).mkₐ ℂ
  map_star' _ := rfl

end UltrapowerDefinition
end NuclearUltrapower

namespace NuclearUltrapower
variable {B : Type*} [CStarAlgebra B] [Nontrivial B] (ω : Ultrafilter ℕ)

/-- Every unitary sequence is bounded by one. -/
def boundedUnitarySeq (u : ℕ → unitary B) : BoundedSeq B :=
  BoundedContinuousFunction.mkOfDiscrete (fun n => (u n : B)) 2 (by
    intro n m
    calc dist (u n : B) (u m : B) ≤ ‖(u n : B)‖ + ‖(u m : B)‖ := dist_le_norm_add_norm _ _
         _ = 2 := by rw [CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]; norm_num)

@[simp] theorem boundedUnitarySeq_apply (u : ℕ → unitary B) (n : ℕ) :
    boundedUnitarySeq u n = (u n : B) := rfl

end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/- Exact rational SOS data. All asserted computed identities reduce in the
   stock Lean kernel; the numerical program and these literals are untrusted. -/
namespace NuclearUltrapower.SL3Certificate
def q0 : List ℤ := [639, 0, 0, 296, 0, 0, 0, 61, 0, -257, -772, 313, -124358, -17378, -1298, 0, 58764, 13297, 0, 72852, 0, -774, -86672, 4393, 61233, 0, -2046, 16950, 66669, -52990, -2326, 67932, 0, -973, -16584, -2181, 123538, 0, -2620, -30357, 91697, 33336, -28704, -988, 0, -23194, 0, 0, 321, 0, -8, -87386, -3519, 178567, -111, -53575, -20627, -10431, 6309, 17237, 52103, 55860, 26775, 34462, -14992, 0, -81312, 0, -56545, -80682, -203, 15466, -505, 188, -1293, 0, -42336, 0, -34, 0, -78914, -201660, 44897, -105876, 1939, 0, -475, 0, 6526, 68153, 2310, 24952, -51656, 105235, 0, 2, 3323, 30093, -3746, -153323, 73422, -500, -3181, -11296, 0, -36493, -1944, -108948, 0, 0, 0, -66692, 3, -306, -69119, 0, -6674, -1307, -1207, 0]
def q1 : List ℤ := [599, 0, 0, -984, 0, 0, 0, 894, 0, 1253, 2960, 2911, 96577, -5843, 426, 0, 182264, -30016, 0, 72852, 0, -1614, -176118, 118021, 32724, 0, -203, -40466, -57730, -52990, -2326, 112048, 0, 449, 99983, -858, 1356, 0, -27950, 7921, 26516, -11875, 28704, -988, 0, -48321, 0, 0, -19, 0, -371, -87386, 6096, -98317, 1176, -31886, 79472, -149428, 277, -45956, -59969, 67084, 54647, -25539, -60845, 0, -46704, 0, 97372, 80682, 203, 20860, -339, 17, 550, 0, -32683, 0, -1062, 0, 52441, 10343, 36574, 38576, -1939, 0, 358, 0, 3154, -72959, -1826, 44909, -120179, -105235, 0, -488, 7126, -55449, 5545, -1602, 59906, -500, -1319, 12843, 0, -5869, 35548, -9739, 0, 0, 0, -3080, -4259, -2820, 124780, 0, -3114, -910, -574, 0]
def q10 : List ℤ := [-701, -104, -1056, -323, -236, -210968, -274610, -139, -132, 124, -1109, -1315, 75165, -115097, -899, 78128, -46221, 63126, 537, -56303, 924, -624, 28095, -47583, 112437, -356847, -884, -63237, 256981, 54133, -10, -48922, 84184, -1010, -12840, -72, -62577, -112413, -237955, 99687, 113652, 76942, 19891, -684, -99073, 289961, -15450, -12422, 1097, 20945, -132, -16957, -284, -121525, -1142, -32302, -13130, -58765, -2146, 82471, -49496, 25913, 20691, -202483, 13127, -252529, -12443, 133215, 9959, -69544, 755, -148561, 210, -402, 2122, -509, -74653, 182201, 2008, 58851, -217566, 75705, -130261, 37106, 431, -13443, -3051, -65710, 9346, 142989, 210, 118044, -223337, -101538, 93, 770, 1590, -41363, 627, 94654, 58585, -38, -214, 8449, 150495, 165268, -70196, -47567, -21850, 51232, -69814, -16856, 1972, -5166, -47362, 3387, 1104, -1096, -605, 985]
def q100 : List ℤ := [374, 255, -316, -1111, -61, 345925, 274610, -241, -361, 717, 1126, -472, -94381, -168133, 557, -240800, -12511, -33089, -456, -56303, -1442, 130, 96020, -62509, -182432, -17411, -490, 38057, -105383, 54133, -10, -18556, 140052, 1154, -25714, 713, -69450, -13682, -44739, 143587, 92475, -242031, -19891, -684, -15079, 167700, -45849, 29822, 715, 91705, -760, -16957, 6590, 9871, -1266, 4119, 83002, 134626, -2450, -66706, -194332, 201454, 24877, 198514, -194981, 11664, -35115, 254288, 6886, 69544, -755, -155023, -2830, 542, -2050, 224, -91995, 182201, 480, -58183, 97414, -18202, 188962, -29673, -431, 13443, 1375, -145040, -96, 41314, -645, -69614, -152863, 101538, 80, 219, -1063, 14481, -2253, 22996, 47152, -38, -1246, -128328, 129529, 55506, -112976, 169632, 56953, 5124, -89324, 39932, -201, -8408, -98097, 40354, -618, -268, -2041, -968]
def q101 : List ℤ := [1469, -546, 537, -47, -458, -136496, 194573, -1551, 407, -661, 1371, 578, -102966, 90190, 579, -235956, -12577, 52014, -36, -1232, -708, -432, 5127, 61922, 69543, -7041, 677, -117406, -272147, -225086, 388, -20560, -40147, 644, 47397, 486, -82798, -5575, 49179, -158400, -112905, 299689, 0, 858, -97048, 61294, -47313, -19895, 720, 74773, 942, -163446, 9251, -93839, 312, 26194, 173390, 186930, -2333, -109463, 273383, 36822, 6058, -127597, -328608, -116784, -23040, 96656, -17414, 0, 0, -135664, -174, 679, -218, 930, 233394, 0, -351, 68117, -114709, -36714, -110771, -38248, 0, -37944, -875, -65215, -2146, 6534, 88, -34572, -296265, 0, 200, 514, -3700, -18593, -3159, 3023, 6299, 747, -807, 55581, -148031, 70509, 86325, -204630, -13937, -101563, 79174, 13827, 1449, 982, -71732, 28554, -1210, -152, -571, -25]
def q102 : List ℤ := [639, 0, 0, -296, 0, 0, 0, 61, 0, -257, 772, -313, 124358, -17378, -1298, 0, 58764, -13297, 0, 72852, 0, -774, 86672, 4393, -61233, 0, 2046, 16950, 66669, -52990, -2326, -67932, 0, -973, -16584, 2181, 123538, 0, -2620, -30357, -91697, 33336, 28704, -988, 0, 23194, 0, 0, 321, 0, -8, -87386, -3519, 178567, -111, -53575, 20627, -10431, -6309, -17237, -52103, 55860, -26775, 34462, -14992, 0, -81312, 0, -56545, 80682, 203, 15466, 505, 188, -1293, 0, 42336, 0, 34, 0, -78914, -201660, 44897, -105876, -1939, 0, 475, 0, 6526, 68153, 2310, 24952, 51656, -105235, 0, -2, -3323, -30093, 3746, 153323, -73422, -500, 3181, 11296, 0, 36493, 1944, 108948, 0, 0, 0, 66692, -3, -306, -69119, 0, 6674, 1307, 1207, 0]
def q103 : List ℤ := [-225, -58, 1391, -787, 137, -202914, -274610, -258, 54, -841, -321, 843, 18477, 194264, 342, 37293, 85760, -96214, 94, -56303, 500, 494, 67925, -38049, -165959, 367949, 1364, 92370, 77588, 54133, -10, 105356, 9510, -1189, 38555, 228, 14111, 16112, 202530, 19292, -7821, 32472, 19891, -684, -34440, 220400, -35614, -29531, -471, -8692, -855, -16957, -2361, 111654, 2408, 21375, 117860, -75862, -304, 77061, 151824, 190262, 4752, -226211, 181854, 239613, -2434, 165732, 28890, -69544, 755, -206252, 2000, 655, -72, 209, -17342, 182201, -1528, -151119, 120151, -26719, -58702, -7433, 431, -13443, 1103, 30877, -8067, -184303, 435, -115445, 70474, -101538, 230, -2174, -2653, 34759, 1108, -71658, 5828, -38, -1032, -117282, 161969, 125466, 53064, 217199, 39634, -29619, -13973, -34531, -1969, -6594, -45190, 94889, 630, 828, -1436, 1124]
def q104 : List ℤ := [192, 219, -80, 354, -112, 55042, 274610, 884, -877, 908, -566, -626, 20174, -121593, -5, -400863, -16574, 88852, -598, -56303, -1254, -657, -96423, -88652, 114920, -119292, 369, -34749, -54330, 54133, -10, 1060, -144922, -844, -38981, 1249, 33351, 6795, -195161, 93274, -56172, 5559, 19891, -684, 53104, 238826, 48260, -15524, 368, -83642, -802, -16957, 8836, 119728, -2385, -11179, -71249, 62345, -2360, 107977, -170073, 249442, -1083, -84232, -125120, -94003, 19563, -50373, 28103, -69544, 755, -215625, 3103, -777, 342, 806, 40784, -182201, 1445, 46244, 178472, -41090, -146168, 4712, 431, 13443, -56, 272876, -1986, -126683, 50, -221532, 123556, -101538, -120, 560, 1250, 9433, 2251, 21246, 105201, -38, -1176, 70167, -72762, 62095, 153406, 192031, 86785, -21159, -123183, -48301, 658, -5666, -90265, -21202, -10, 1086, -1520, -384]
end NuclearUltrapower.SL3Certificate
end

end OAI
end


