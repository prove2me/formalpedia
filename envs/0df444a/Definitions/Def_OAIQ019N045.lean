-- Prove2me | Definitions.Def_OAIQ019N045
-- name    : OAIQ019N045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:07:12.176122+00:00
-- url     : https://prove2.me/theorems/37f5aa40-287b-49e1-b99b-312d1dc61844
-- title:
--   Definitions bundle OAIQ019N045 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 12 definitions, 1 instance and 24 theorems. The definitions and types are `OAI.NuclearUltrapower.HilbertUltraproduct.operatorRep`, `OAI.NuclearUltrapower.HilbertUltraproduct.unitalOperatorRep`, `OAI.NuclearUltrapower.VariableUltra.quotientHilbertRep`, `OAI.NuclearUltrapower.VariableUltra.sequenceHom`, `OAI.NuclearUltrapower.coordinateInclusion`, `OAI.NuclearUltrapower.finiteInduced`, `OAI.NuclearUltrapower.identityCoordinate`, `OAI.NuclearUltrapower.pairedTensorUnitary`, `OAI.NuclearUltrapower.tensorIsometry`, `OAI.NuclearUltrapower.tensorLeftRep`, `OAI.NuclearUltrapower.tensorMapBetween`, `OAI.NuclearUltrapower.tensorRightRep`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_FiniteInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/FiniteInduction.lean), [`NuclearUltrapower_HilbertInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertInduction.lean), [`NuclearUltrapower_HilbertUltraproduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertUltraproduct.lean), [`NuclearUltrapower_NuclearFiniteness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/NuclearFiniteness.lean), [`NuclearUltrapower_SpatialGap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SpatialGap.lean), [`NuclearUltrapower_TensorNorms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/TensorNorms.lean).
--
--   **Imports.** It imports the published bundle `Def_NuclearUltrapower`; the bundle `OAIQ019N040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ019N042` and `OAIQ019N046`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N040

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertInduction
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal InnerProductSpace
namespace NuclearUltrapower
universe u v

section Induction
variable {G : Type u} [Group G] (H : Subgroup G)

variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (α : H →* (V ≃ₗᵢ[ℂ] V))

/-- Subgroup elements fix the identity left coset. -/
@[simp] theorem subgroup_smul_identity (h : H) :
    (h : G) • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 := by
  change (QuotientGroup.mk ((h:G) * 1) : G ⧸ H) = QuotientGroup.mk 1
  apply QuotientGroup.eq.mpr
  simp

@[simp] theorem cosetCocycle_identity (h : H) :
    cosetCocycle H (h:G) (QuotientGroup.mk 1) = h := by
  apply Subtype.ext
  simp only [cosetCocycle, subgroup_smul_identity, cosetRep_identity, inv_one, one_mul, mul_one]

@[simp] theorem induced_identity_coordinate (h : H)
    (x : lp (fun _ : G ⧸ H => V) 2) :
    inducedUnitary H α (h:G) x (QuotientGroup.mk 1) = α h (x (QuotientGroup.mk 1)) := by
  rw [inducedUnitary_apply]
  have hh : (h:G)⁻¹ • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 :=
    subgroup_smul_identity H h⁻¹
  rw [hh, cosetCocycle_identity]

end Induction
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FiniteInduction
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace ENNReal
namespace NuclearUltrapower
universe u

section FiniteInduction
variable {Γ : Type u} [Group Γ] (H : Subgroup Γ) [Finite (Γ ⧸ H)]
    (α : FiniteUnitaryRep.{u,u} H)

instance induced_nontrivial : Nontrivial (lp (fun _ : Γ ⧸ H => α) 2) :=
  (inductionInclusion H (V := α)).injective.nontrivial

/-- Finite-index unitary induction, using the exact coset cocycle. -/
def finiteInduced : FiniteUnitaryRep.{u,u} Γ where
  carrier := lp (fun _ : Γ ⧸ H => α) 2
  action := inducedUnitary H α.action

/-- Identity-coordinate projection on the induced Hilbert space. -/
def identityCoordinate : finiteInduced H α →L[ℂ] α :=
  lp.evalCLM ℂ (fun _ : Γ ⧸ H => α) 2 (QuotientGroup.mk 1)

@[simp] theorem identityCoordinate_apply (x : finiteInduced H α) :
    identityCoordinate H α x = Subtype.val x (QuotientGroup.mk 1) := rfl

end FiniteInduction
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
section Functor
variable {E E' E'' F F' F'' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup E''] [InnerProductSpace ℂ E'']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']
  [NormedAddCommGroup F''] [InnerProductSpace ℂ F'']

/-- Heterogeneous completion of the Hilbert tensor functor. -/
def tensorMapBetween (U : E →L[ℂ] E') (V : F →L[ℂ] F') :
    TensorHilbert E F →L[ℂ] TensorHilbert E' F' := (TensorProduct.mapL U V).completion

@[simp] theorem tensorMapBetween_coe (U : E →L[ℂ] E') (V : F →L[ℂ] F')
    (z : E ⊗[ℂ] F) : tensorMapBetween U V z =
      (TensorProduct.mapL U V z : TensorHilbert E' F') :=
  ContinuousLinearMap.completion_apply_coe _ _

@[simp] theorem tensorMapBetween_comp (U : E →L[ℂ] E') (U' : E' →L[ℂ] E'')
    (V : F →L[ℂ] F') (V' : F' →L[ℂ] F'') :
    tensorMapBetween (U'.comp U) (V'.comp V) =
      (tensorMapBetween U' V').comp (tensorMapBetween U V) := by
  simp only [tensorMapBetween, TensorProduct.mapL_comp, completed_comp]

@[simp] theorem tensorMapBetween_one :
    tensorMapBetween (1 : E →L[ℂ] E) (1 : F →L[ℂ] F) = 1 := completedTensorMap_one

@[simp] theorem tensorMapBetween_add_right (U : E →L[ℂ] E') (V W : F →L[ℂ] F') :
    tensorMapBetween U (V+W) = tensorMapBetween U V + tensorMapBetween U W := by
  simp only [tensorMapBetween, TensorProduct.mapL_add_right, completed_add]

@[simp] theorem tensorMapBetween_zero_right (U : E →L[ℂ] E') :
    tensorMapBetween U (0 : F →L[ℂ] F') = 0 := by
  simp only [tensorMapBetween, TensorProduct.mapL_zero_right, completed_zero]

/-- Isometries remain isometries upon completion, proved using density. -/
def tensorIsometry (U : E →ₗᵢ[ℂ] E') (V : F →ₗᵢ[ℂ] F') :
    TensorHilbert E F →ₗᵢ[ℂ] TensorHilbert E' F' where
  toLinearMap := (tensorMapBetween U.toContinuousLinearMap V.toContinuousLinearMap).toLinearMap
  norm_map' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) continuous_norm
    | ih x =>
      change ‖tensorMapBetween U.toContinuousLinearMap V.toContinuousLinearMap (x : TensorHilbert E F)‖ = ‖(x : TensorHilbert E F)‖
      rw [tensorMapBetween_coe, UniformSpace.Completion.norm_coe,
        UniformSpace.Completion.norm_coe]
      rw [← TensorProduct.toContinuousLinearMap_mapIsometry]
      exact (TensorProduct.mapIsometry U V).norm_map x

@[simp] theorem tensorIsometry_toCLM (U : E →ₗᵢ[ℂ] E') (V : F →ₗᵢ[ℂ] F') :
    (tensorIsometry U V).toContinuousLinearMap =
      tensorMapBetween U.toContinuousLinearMap V.toContinuousLinearMap := rfl

end Functor
end NuclearUltrapower
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped InnerProductSpace ENNReal
namespace NuclearUltrapower
universe u v
section Coordinates
variable {Γ : Type u} [Group Γ] (H : Subgroup Γ)
  {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (α : H →* (V ≃ₗᵢ[ℂ] V))

def coordinateInclusion (i : Γ ⧸ H) : V →ₗᵢ[ℂ] lp (fun _ : Γ ⧸ H => V) 2 := by
  classical
  refine { toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : Γ ⧸ H => V) 2 i, norm_map' := ?_ }
  intro v
  exact lp.norm_single (E := fun _ : Γ ⧸ H => V) (p := 2) (by norm_num) i v

@[simp] theorem coordinateInclusion_apply (i j : Γ ⧸ H) (v : V) :
    coordinateInclusion H i v j = Pi.single (M := fun _ : Γ ⧸ H => V) i v j := rfl

@[simp] theorem coordinateInclusion_identity :
    coordinateInclusion H (QuotientGroup.mk 1) = inductionInclusion H (V := V) := rfl

end Coordinates
section FiniteCoordinates
variable {Γ : Type u} [Group Γ] (H : Subgroup Γ) [Finite (Γ ⧸ H)]
  (α : FiniteUnitaryRep.{u,u} H)

@[simp] theorem identityCoordinate_inclusion (i : Γ ⧸ H) (v : α) :
    identityCoordinate H α (coordinateInclusion H i v) =
      if i = QuotientGroup.mk 1 then v else 0 := by
  classical
  change Pi.single (M := fun _ : Γ ⧸ H => α) i v (QuotientGroup.mk 1) = _
  split_ifs with hi
  · simp [hi]
  · exact Pi.single_eq_of_ne (M := fun _ : Γ ⧸ H => α) (Ne.symm hi) v

end FiniteCoordinates
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertUltraproduct
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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
variable {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
    (ω : Ultrafilter ι)

theorem map_norm_le (T : lp (fun i => E i →L[ℂ] F i) ∞) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ᶠ i in (ω : Filter ι), ‖T i‖ ≤ C) : ‖map ω T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x =>
    simpa only [map_coe, UniformSpace.Completion.norm_coe] using
      UltraPreHilbert.mapLinear_norm_le ω T C hT x

end HilbertUltraproduct

end NuclearUltrapower

namespace NuclearUltrapower
namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] (ω : Ultrafilter ι)

attribute [local instance] OAI.NuclearUltrapower.HilbertUltraproduct.instIsBoundedSMulComplexContinuousLinearMapId
/-- Bounded operator products and adjoints descend to the Hilbert ultraproduct. -/
def operatorRep : lp (fun i => E i →L[ℂ] E i) ∞ →⋆ₙₐ[ℂ]
    (HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω) where
  toFun := map (E := E) (F := E) ω
  map_zero' := map_zero ω
  map_add' := map_add ω
  map_smul' := map_smul ω
  map_mul' := map_mul ω
  map_star' := map_star ω

@[simp] theorem operatorRep_apply (T : lp (fun i => E i →L[ℂ] E i) ∞) :
    operatorRep ω T = map (E := E) (F := E) ω T := rfl

omit [∀ i, CompleteSpace (E i)] in
/-- The operator norm on the Hilbert ultraproduct is precisely the ultralimit
of coordinate operator norms. In particular no norm information is lost. -/
theorem map_norm_tendsto (T : lp (fun i => E i →L[ℂ] E i) ∞) :
    Tendsto (fun i => ‖T i‖) (ω : Filter ι) (𝓝 ‖map ω T‖) := by
  have ht := hilbert_tendsto_ultralimit_of_bounded ω (fun i => ‖T i‖)
    ⟨‖T‖, fun i => by simpa only [Real.norm_eq_abs, abs_norm] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero T i⟩
  let c := limUnder (ω : Filter ι) (fun i => ‖T i‖)
  have hc : 0 ≤ c := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Filter.Eventually.of_forall (fun i => norm_nonneg _))
  have hle : ‖map ω T‖ ≤ c := by
    apply le_of_forall_pos_le_add
    intro ε hε
    exact map_norm_le ω T (c + ε) (by positivity)
      ((ht.eventually (gt_mem_nhds (show c < c + ε by linarith))).mono (fun _ h => h.le))
  have hge : c ≤ ‖map ω T‖ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    choose x hx hTx using fun i => (T i).exists_lt_apply_of_lt_opNorm
      (show ‖T i‖ - ε < ‖T i‖ by linarith)
    let X : UltraPreHilbert E ω := (⟨x, memℓp_infty ⟨1, by
      rintro _ ⟨i, rfl⟩; exact (hx i).le⟩⟩ : lp E ∞)
    have hnX : ‖X‖ ≤ 1 := le_of_tendsto_of_tendsto (UltraPreHilbert.norm_tendsto ω X)
      tendsto_const_nhds (Filter.Eventually.of_forall (fun i => (hx i).le))
    have hb : c - ε ≤ ‖UltraPreHilbert.mapLinear ω T X‖ :=
      le_of_tendsto_of_tendsto (ht.sub_const ε)
        (UltraPreHilbert.norm_tendsto ω (UltraPreHilbert.mapLinear ω T X))
        (Filter.Eventually.of_forall (fun i => (hTx i).le))
    have ho : ‖UltraPreHilbert.mapLinear ω T X‖ ≤ ‖map ω T‖ := by
      have he := (map ω T).le_opNorm_of_le
        (show ‖(X : HilbertUltraproduct E ω)‖ ≤ 1 by simpa using hnX)
      simpa only [map_coe, UniformSpace.Completion.norm_coe, mul_one] using he
    linarith
  rwa [show ‖map ω T‖ = c from le_antisymm hle hge]

omit [∀ i, CompleteSpace (E i)] in
/-- Norm-null families, and only norm-null families, represent zero. -/
theorem map_eq_zero_iff (T : lp (fun i => E i →L[ℂ] E i) ∞) :
    map ω T = 0 ↔ Tendsto (fun i => ‖T i‖) (ω : Filter ι) (𝓝 0) := by
  constructor
  · intro h; simpa [h] using map_norm_tendsto ω T
  · intro h
    exact norm_eq_zero.mp (tendsto_nhds_unique (map_norm_tendsto ω T) h)

end HilbertUltraproduct
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorNorms
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorBoundedSMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct
namespace NuclearUltrapower

section Bounds
variable {A C : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]

attribute [local instance] OAI.NuclearUltrapower.instIsBoundedSMulComplexTensorProductCarrier
def tensorLeftRep {H K : ComplexHilbert.{0}}
    (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : A →⋆ₙₐ[ℂ] (TensorHilbert H K →L[ℂ] TensorHilbert H K) :=
  (tensorLeftHom (E := H) (F := K)).toNonUnitalStarAlgHom.comp R

def tensorRightRep {H K : ComplexHilbert.{0}}
    (S : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : C →⋆ₙₐ[ℂ] (TensorHilbert H K →L[ℂ] TensorHilbert H K) :=
  (tensorRightHom (E := H) (F := K)).toNonUnitalStarAlgHom.comp S

@[simp] theorem tensorLeftRep_apply {H K : ComplexHilbert.{0}}
    (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    tensorLeftRep (K := K) R a = tensorLeftHom (R a) := rfl
@[simp] theorem tensorRightRep_apply {H K : ComplexHilbert.{0}}
    (S : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (c : C) :
    tensorRightRep (H := H) S c = tensorRightHom (S c) := rfl

end Bounds
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SpatialGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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
noncomputable section
open scoped TensorProduct
noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder

section TensorComplement
variable {Γ B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The tensor of two unitaries as a unitary of the completed tensor Hilbert space. -/
def pairedTensorUnitary (u : unitary (E →L[ℂ] E)) (v : unitary (F →L[ℂ] F)) :
    unitary (TensorHilbert E F →L[ℂ] TensorHilbert E F) :=
  ⟨completedTensorMap (u : E →L[ℂ] E) (v : F →L[ℂ] F), by
    rw [Unitary.mem_iff]
    constructor <;> rw [← completedTensorMap_star, ← completedTensorMap_mul]
    · simp only [Unitary.coe_star_mul_self, completedTensorMap_one]
    · simp only [← Unitary.coe_star, Unitary.coe_mul_star_self, completedTensorMap_one]⟩

@[simp] theorem pairedTensorUnitary_coe (u : unitary (E →L[ℂ] E)) (v : unitary (F →L[ℂ] F)) :
    (pairedTensorUnitary u v : TensorHilbert E F →L[ℂ] TensorHilbert E F) =
      completedTensorMap (u : E →L[ℂ] E) (v : F →L[ℂ] F) := rfl

end TensorComplement

end NuclearUltrapower

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NuclearFiniteness
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal TensorProduct
namespace NuclearUltrapower
namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)] (ω : Ultrafilter ι)

omit [∀ i, CompleteSpace (E i)] in
@[simp] theorem map_one : map (E := E) (F := E) ω (1 : lp (fun i => E i →L[ℂ] E i) ∞) = 1 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    rw [map_coe]
    congr 1

/-- The Hilbert-ultraproduct operator action is unital, including zero spaces. -/
def unitalOperatorRep : lp (fun i => E i →L[ℂ] E i) ∞ →⋆ₐ[ℂ]
    (HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω) where
  toFun := map ω
  map_zero' := map_zero ω
  map_one' := map_one ω
  map_add' := map_add ω
  map_mul' := map_mul ω
  commutes' c := by
    change operatorRep (E := E) ω (algebraMap ℂ _ c) = algebraMap ℂ _ c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      _root_.map_smul (operatorRep (E := E) ω)]
    change c • map ω (1 : lp (fun i => E i →L[ℂ] E i) ∞) = c • 1
    rw [map_one]
  map_star' := map_star ω
end HilbertUltraproduct

namespace VariableUltra
section CoordinateHom
variable {ι : Type u} {A : ι → Type v} {C : ι → Type w}
  [∀ i, CStarAlgebra (A i)] [∀ i, CStarAlgebra (C i)]
  [∀ i, Nontrivial (A i)] [∀ i, Nontrivial (C i)]

/-- Contractive coordinate homomorphisms preserve boundedness, with no dimension bound. -/
def sequenceHom (f : ∀ i, A i →⋆ₐ[ℂ] C i) : Seq A →⋆ₐ[ℂ] Seq C where
  toFun x := ⟨fun i => f i (x i), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨i, rfl⟩
    exact (NonUnitalStarAlgHom.norm_apply_le (f i) _).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero x i)⟩⟩
  map_zero' := by ext i; exact map_zero (f i)
  map_one' := by ext i; exact map_one (f i)
  map_add' x y := by ext i; exact map_add (f i) _ _
  map_mul' x y := by ext i; exact map_mul (f i) _ _
  commutes' c := by ext i; exact (f i).commutes c
  map_star' x := by ext i; exact map_star (f i) _

@[simp] theorem sequenceHom_apply (f : ∀ i, A i →⋆ₐ[ℂ] C i) (x : Seq A) (i : ι) :
    sequenceHom f x i = f i (x i) := rfl
end CoordinateHom

section QuotientHilbert
variable {ι : Type u} {A : ι → Type v} {E : ι → Type w}
  [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)]
  (ω : Ultrafilter ι) (f : ∀ i, A i →⋆ₐ[ℂ] (E i →L[ℂ] E i))

theorem coordinateRep_respects {x y : Seq A} (h : Rel A ω x y) :
    HilbertUltraproduct.unitalOperatorRep (E := E) ω (sequenceHom f x) =
      HilbertUltraproduct.unitalOperatorRep (E := E) ω (sequenceHom f y) := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← map_sub]
  apply (HilbertUltraproduct.map_eq_zero_iff ω _).mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun i => NonUnitalStarAlgHom.norm_apply_le (f i) (x i - y i))
  exact h

/-- Every uniformly varying coordinate representation descends to the quotient. -/
def quotientHilbertRep : Algebra A ω →⋆ₐ[ℂ]
    (HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω) where
  __ := (con A ω).liftₐ
    ((HilbertUltraproduct.unitalOperatorRep (E := E) ω).comp (sequenceHom f)).toAlgHom
    (fun _ _ h => coordinateRep_respects ω f h)
  map_star' x := by
    induction x using Quotient.inductionOn with | h x =>
      exact map_star ((HilbertUltraproduct.unitalOperatorRep (E := E) ω).comp (sequenceHom f)) x

@[simp] theorem quotientHilbertRep_mk (x : Seq A) :
    quotientHilbertRep ω f (mk A ω x) = HilbertUltraproduct.unitalOperatorRep (E := E) ω (sequenceHom f x) := rfl
end QuotientHilbert
end VariableUltra

end NuclearUltrapower
end
end

end OAI
end


