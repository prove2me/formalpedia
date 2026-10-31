-- Prove2me | Definitions.Def_OAIQ019N040
-- name    : OAIQ019N040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:04:57.19133+00:00
-- url     : https://prove2.me/theorems/7946a95b-1029-46f9-a591-25f0b02a3b52
-- title:
--   Definitions bundle OAIQ019N040 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 7 definitions, 4 instances and 12 theorems. The definitions and types are `OAI.NuclearUltrapower.HilbertUltraproduct`, `OAI.NuclearUltrapower.HilbertUltraproduct.map`, `OAI.NuclearUltrapower.UltraPreHilbert.core`, `OAI.NuclearUltrapower.UltraPreHilbert.mapContinuous`, `OAI.NuclearUltrapower.UltraPreHilbert.mapLinear`, `OAI.NuclearUltrapower.VariableUltra.quotientRepresentation`, `OAI.NuclearUltrapower.VariableUltra.representationSequence`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_CuntzAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzAlgebra.lean), [`NuclearUltrapower_CuntzWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzWords.lean), [`NuclearUltrapower_HilbertUltraproduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertUltraproduct.lean), [`NuclearUltrapower_RepresentationUltraproduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/RepresentationUltraproduct.lean).
--
--   **Imports.** It imports the bundles `OAIQ019N000`, `OAIQ019N001` and `OAIQ019N002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ019N045`; the statement `OAI.NuclearUltrapower.VariableUltra.quotientRepresentation_weakly_mixing`; the proof of `OAI.NuclearUltrapower.CuntzAveraging.averaged_norm`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ019N000
import Definitions.Def_OAIQ019N001
import Definitions.Def_OAIQ019N002

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzAlgebra
attribute [-instance] _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped InnerProductSpace
namespace NuclearUltrapower.CuntzModel

attribute [local instance] OAI.NuclearUltrapower.CuntzModel.instDecidableEqIndex
instance instNontrivialSubtypePreLpIndexComplexMemAddSubgroupSpace : Nontrivial Space := by
  refine ⟨⟨lp.single 2 (0,0) (1:ℂ), 0, ?_⟩⟩
  intro h
  have := congrArg (fun x : Space => x (0,0)) h
  simp at this

end NuclearUltrapower.CuntzModel
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzWords
attribute [-instance] _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.CuntzWords

instance instDecidableEqWord (n : ℕ) : DecidableEq (Word n) := Classical.decEq _

end NuclearUltrapower.CuntzWords
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertUltraproduct
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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

namespace UltraPreHilbert
variable {ι : Type u} {E : ι → Type v} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (ω : Ultrafilter ι)

theorem inner_tendsto (x y : UltraPreHilbert E ω) :
    Tendsto (fun i => inner ℂ (family ω x i) (family ω y i)) (ω : Filter ι)
      (𝓝 (limUnder (ω : Filter ι) (fun i => inner ℂ (family ω x i) (family ω y i)))) := by
  apply hilbert_tendsto_ultralimit_of_bounded
  refine ⟨‖family ω x‖ * ‖family ω y‖, fun i => ?_⟩
  exact (norm_inner_le_norm _ _).trans (mul_le_mul
    (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _) (norm_nonneg _) (norm_nonneg _))

@[instance_reducible] def core : PreInnerProductSpace.Core ℂ (UltraPreHilbert E ω) where
  inner x y := limUnder (ω : Filter ι) (fun i => inner ℂ (family ω x i) (family ω y i))
  conj_inner_symm x y := by
    exact tendsto_nhds_unique ((inner_tendsto ω y x).star.congr
      (fun i => inner_conj_symm (family ω x i) (family ω y i))) (inner_tendsto ω x y)
  re_inner_nonneg x := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      ((Complex.continuous_re.tendsto _).comp (inner_tendsto ω x x))
      (Filter.Eventually.of_forall (fun i => (inner_self_nonneg (𝕜 := ℂ) (x := family ω x i))))
  add_left x y z := by
    apply tendsto_nhds_unique (inner_tendsto ω (x + y) z)
    simpa only [family_add, lp.coeFn_add, Pi.add_apply, inner_add_left] using
      (inner_tendsto ω x z).add (inner_tendsto ω y z)
  smul_left x y r := by
    apply tendsto_nhds_unique (inner_tendsto ω (r • x) y)
    simpa only [family_smul, lp.coeFn_smul, Pi.smul_apply, inner_smul_left] using
      (inner_tendsto ω x y).const_mul (starRingEnd ℂ r)

instance instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup : SeminormedAddCommGroup (UltraPreHilbert E ω) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ _ _ _ _ (core ω)

instance instInnerProductSpaceComplexSubtypePreLpMemAddSubgroup : InnerProductSpace ℂ (UltraPreHilbert E ω) := InnerProductSpace.ofCore (core ω)

@[simp] theorem inner_def (x y : UltraPreHilbert E ω) :
    inner ℂ x y = limUnder (ω : Filter ι)
      (fun i => inner ℂ (family ω x i) (family ω y i)) := rfl

/-- The seminorm is exactly the ultralimit of pointwise norms. -/
theorem norm_tendsto (x : UltraPreHilbert E ω) :
    Tendsto (fun i => ‖family ω x i‖) (ω : Filter ι) (𝓝 ‖x‖) := by
  have h := ((Complex.continuous_re.tendsto _).comp (inner_tendsto ω x x)).sqrt
  convert h using 1
  · funext i
    exact norm_eq_sqrt_re_inner (𝕜 := ℂ) _
  · congr 1

end UltraPreHilbert

/-- The Hilbert ultraproduct, implemented as the Hausdorff completion of bounded
families for the ultralimit seminorm. This is equivalent to the standard
norm-null quotient, but gives completeness without a separate lifting argument. -/
abbrev HilbertUltraproduct {ι : Type u} (E : ι → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] (ω : Ultrafilter ι) :=
  UniformSpace.Completion (UltraPreHilbert E ω)

namespace UltraPreHilbert
variable {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
    (ω : Ultrafilter ι)

/-- Uniformly bounded operator families act on bounded vector families. -/
def mapLinear (T : lp (fun i => E i →L[ℂ] F i) ∞) :
    UltraPreHilbert E ω →ₗ[ℂ] UltraPreHilbert F ω where
  toFun x := (⟨fun i => T i (family ω x i), memℓp_infty
    ⟨‖T‖ * ‖family ω x‖, by
      rintro _ ⟨i, rfl⟩
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
        (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
        (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _) (norm_nonneg _) (norm_nonneg _))⟩⟩ : lp F ∞)
  map_add' x y := by apply Subtype.ext; funext i; exact map_add (T i) _ _
  map_smul' c x := by apply Subtype.ext; funext i; exact map_smul (T i) _ _

@[simp] theorem family_map (T : lp (fun i => E i →L[ℂ] F i) ∞)
    (x : UltraPreHilbert E ω) (i : ι) :
    family ω (mapLinear ω T x) i = T i (family ω x i) := rfl

/-- Eventual, rather than uniform, bounds suffice after passing to the ultralimit. -/
theorem mapLinear_norm_le (T : lp (fun i => E i →L[ℂ] F i) ∞) (C : ℝ)
    (hT : ∀ᶠ i in (ω : Filter ι), ‖T i‖ ≤ C) (x : UltraPreHilbert E ω) :
    ‖mapLinear ω T x‖ ≤ C * ‖x‖ := by
  apply le_of_tendsto_of_tendsto (norm_tendsto ω (mapLinear ω T x))
    ((norm_tendsto ω x).const_mul C)
  exact hT.mono (fun i hi => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg _)))

def mapContinuous (T : lp (fun i => E i →L[ℂ] F i) ∞) :
    UltraPreHilbert E ω →L[ℂ] UltraPreHilbert F ω :=
  (mapLinear ω T).mkContinuous ‖T‖ (mapLinear_norm_le ω T ‖T‖
    (Filter.Eventually.of_forall (fun i => lp.norm_apply_le_norm ENNReal.top_ne_zero T i)))

end UltraPreHilbert

namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
    (ω : Ultrafilter ι)

/-- The induced operator on the completed Hilbert ultraproduct. -/
def map (T : lp (fun i => E i →L[ℂ] F i) ∞) :
    HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct F ω :=
  (UltraPreHilbert.mapContinuous ω T).completion

@[simp] theorem map_coe (T : lp (fun i => E i →L[ℂ] F i) ∞)
    (x : UltraPreHilbert E ω) :
    map ω T (x : HilbertUltraproduct E ω) =
    (UltraPreHilbert.mapLinear ω T x : HilbertUltraproduct F ω) :=
  ContinuousLinearMap.completion_apply_coe _ _

end HilbertUltraproduct

end NuclearUltrapower

namespace NuclearUltrapower
namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] (ω : Ultrafilter ι)

omit [∀ i, CompleteSpace (E i)] in
theorem map_zero  : map (E := E) (F := E) ω (0 : lp (fun i => E i →L[ℂ] E i) ∞) = 0 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    rw [map_coe]
    have he : UltraPreHilbert.mapLinear (E := E) (F := E) ω 0 x = 0 := by
      apply Subtype.ext; funext i
      change (0 : E i →L[ℂ] E i) (UltraPreHilbert.family ω x i) = 0
      rfl
    rw [he, UniformSpace.Completion.coe_zero]
    rfl

omit [∀ i, CompleteSpace (E i)] in
theorem map_add (T U : lp (fun i => E i →L[ℂ] E i) ∞) : map (E := E) (F := E) ω (T + U) = map (E := E) (F := E) ω T + map (E := E) (F := E) ω U := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    simp only [add_apply, map_coe, ← UniformSpace.Completion.coe_add]
    congr 1

attribute [local instance] OAI.NuclearUltrapower.HilbertUltraproduct.instIsBoundedSMulComplexContinuousLinearMapId
set_option synthInstance.maxHeartbeats 400000 in
theorem map_smul (c : ℂ) (T : lp (fun i => E i →L[ℂ] E i) ∞) :
    map (E := E) (F := E) ω (SMul.smul c T) = c • map (E := E) (F := E) ω T := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (map (E := E) (F := E) ω (SMul.smul c T)).continuous
      (c • map (E := E) (F := E) ω T).continuous
  | ih x =>
    have he : UltraPreHilbert.mapLinear (E := E) (F := E) ω (SMul.smul c T) x =
        c • UltraPreHilbert.mapLinear (E := E) (F := E) ω T x := by
      apply Subtype.ext
      funext i
      rfl
    rw [map_coe, smul_apply, map_coe,
      ← UniformSpace.Completion.coe_smul, he]

theorem map_mul (T U : lp (fun i => E i →L[ℂ] E i) ∞) : map (E := E) (F := E) ω (T * U) = map (E := E) (F := E) ω T * map (E := E) (F := E) ω U := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    change map ω (T * U) (x : HilbertUltraproduct E ω) = map ω T (map ω U x)
    rw [map_coe, map_coe, map_coe]
    congr 1

theorem map_star (T : lp (fun i => E i →L[ℂ] E i) ∞) : map (E := E) (F := E) ω (star T) = star (map (E := E) (F := E) ω T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    simp only [map_coe, UniformSpace.Completion.inner_coe, UltraPreHilbert.inner_def]
    congr 1
    funext i
    simp only [UltraPreHilbert.family_map, lp.coeFn_star, Pi.star_apply]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

end HilbertUltraproduct
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_RepresentationUltraproduct
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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
namespace NuclearUltrapower
open scoped TensorProduct

namespace VariableUltra
variable {ι : Type*} {Γ : Type u} [Group Γ]
variable (π : ι → FiniteUnitaryRep.{u,v} Γ)

/-- The bounded coordinate representation, before taking its quotient. -/
def representationSequence : Γ →* unitary (operatorSeq (fun i => π i)) where
  toFun g := isoSequence _ (fun i => (π i).action g)
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change ((Unitary.linearIsometryEquiv.symm ((π i).action 1) : unitary (π i →L[ℂ] π i)) :
      π i →L[ℂ] π i) = 1
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change ((Unitary.linearIsometryEquiv.symm ((π i).action (g*h)) : unitary (π i →L[ℂ] π i)) :
      π i →L[ℂ] π i) =
      (Unitary.linearIsometryEquiv.symm ((π i).action g) : π i →L[ℂ] π i) *
      (Unitary.linearIsometryEquiv.symm ((π i).action h) : π i →L[ℂ] π i)
    rw [map_mul, map_mul]
    rfl

variable (ω : Ultrafilter ι) {K : Type v}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Any unital representation of the quotient carries the source group tuple. -/
def quotientRepresentation (φ : operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    Γ →* (K ≃ₗᵢ[ℂ] K) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp
    ((Unitary.map (starAlgToStarMonoid φ)).toMonoidHom.comp
      ((Unitary.map (starAlgToStarMonoid (mk _ ω))).toMonoidHom.comp (representationSequence π)))

@[simp] theorem quotientRepresentation_apply
    (φ : operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) (g : Γ) :
    quotientRepresentation π ω φ g = representedIso (fun i => π i) ω φ
      (fun i => (π i).action g) := rfl

end VariableUltra
end NuclearUltrapower

end
end
end
end
end

end OAI
end


