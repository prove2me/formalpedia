-- Prove2me | Definitions.Def_OAIQ019N039
-- name    : OAIQ019N039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:05:21.936499+00:00
-- url     : https://prove2.me/theorems/ee2508b1-ffb7-408d-8222-a495d80f61d8
-- title:
--   Definitions bundle OAIQ019N039 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 89 declarations of OpenAI's Lean: 49 definitions, 11 instances and 29 theorems. The definitions and types are `OAI.NuclearUltrapower.CuntzAveraging.averaged`, `OAI.NuclearUltrapower.CuntzAveraging.concrete`, `OAI.NuclearUltrapower.CuntzAveraging.row`, `OAI.NuclearUltrapower.CuntzAveraging.rowSum`, `OAI.NuclearUltrapower.CuntzAveraging.weight`, `OAI.NuclearUltrapower.CuntzPolynomial.evalWord`, `OAI.NuclearUltrapower.CuntzPolynomial.evaluate`, `OAI.NuclearUltrapower.CuntzPolynomial.generator`, `OAI.NuclearUltrapower.CuntzPolynomial.involutionAdd`, `OAI.NuclearUltrapower.CuntzPolynomial.modelNormSet`, `OAI.NuclearUltrapower.CuntzPolynomial.universalNorm`, `OAI.NuclearUltrapower.CuntzPolynomial.universalSeminorm`, `OAI.NuclearUltrapower.CuntzUniversal.Algebra`, `OAI.NuclearUltrapower.CuntzUniversal.generator`, `OAI.NuclearUltrapower.CuntzUniversal.inclusion`, `OAI.NuclearUltrapower.CuntzUniversal.modelMap`, `OAI.NuclearUltrapower.SOS.label1222`, `OAI.NuclearUltrapower.SOS.label1241`, `OAI.NuclearUltrapower.SOS.label1368`, `OAI.NuclearUltrapower.SOS.label1422`, `OAI.NuclearUltrapower.SOS.label1440`, `OAI.NuclearUltrapower.SOS.label1441`, `OAI.NuclearUltrapower.SOS.label1446`, `OAI.NuclearUltrapower.SOS.label1447`, `OAI.NuclearUltrapower.SOS.label1448`, `OAI.NuclearUltrapower.SOS.label1453`, `OAI.NuclearUltrapower.SOS.label1454`, `OAI.NuclearUltrapower.SOS.label1472`, `OAI.NuclearUltrapower.SOS.label1525`, `OAI.NuclearUltrapower.SOS.label1653`, `OAI.NuclearUltrapower.SOS.label1672`, `OAI.NuclearUltrapower.SOS.label1673`, `OAI.NuclearUltrapower.SOS.label1847`, `OAI.NuclearUltrapower.SOS.label1938`, `OAI.NuclearUltrapower.SOS.label1954`, `OAI.NuclearUltrapower.SOS.label2009`, `OAI.NuclearUltrapower.SOS.label2022`, `OAI.NuclearUltrapower.SOS.label2027`, `OAI.NuclearUltrapower.SOS.label2028`, `OAI.NuclearUltrapower.SOS.label2029` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_CuntzAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzAlgebra.lean), [`NuclearUltrapower_CuntzIntertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzIntertwining.lean), [`NuclearUltrapower_CuntzWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzWords.lean), [`NuclearUltrapower_HilbertInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/HilbertInduction.lean), [`NuclearUltrapower_SOSResidual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSResidual.lean), [`NuclearUltrapower_SOSSemantics`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSSemantics.lean).
--
--   **Imports.** It imports the published bundle `Def_NuclearUltrapower`; the bundles `OAIQ019N000` and `OAIQ019N001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ019N042`; the statements `OAI.NuclearUltrapower.CuntzAveraging.averaged_norm`, `OAI.NuclearUltrapower.CuntzAveraging.averaged_norm_le`, `OAI.NuclearUltrapower.CuntzAveraging.commutingEval_norm_le_min`, `OAI.NuclearUltrapower.CuntzAveraging.rowSum_adjoint` and `OAI.NuclearUltrapower.CuntzAveraging.rowSum_generator`; the proofs of `OAI.NuclearUltrapower.CuntzAveraging.averaged_norm`, `OAI.NuclearUltrapower.CuntzAveraging.rowSum_adjoint` and `OAI.NuclearUltrapower.CuntzAveraging.rowSum_generator`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N000
import Definitions.Def_OAIQ019N001

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertInduction
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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

/-- Bounded maps on a Hilbert direct sum are determined by coordinate vectors. -/
theorem l2_clm_ext {I : Type u} {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T U : L2 I →L[ℂ] E} (h : ∀ i c, T (lp.single 2 i c) = U (lp.single 2 i c)) : T = U := by
  classical
  apply lp.ext_continuousLinearMap (p := 2) ENNReal.ofNat_ne_top
  intro i
  apply ContinuousLinearMap.ext
  intro c
  exact h i c

end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzAlgebra
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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
theorem shiftIndex_surjective (x : Index) : ∃ i y, shiftIndex i y = x := by
  refine ⟨⟨x.2 % 2, Nat.mod_lt _ (by decide)⟩, (x.1-1,x.2/2), ?_⟩
  apply Prod.ext <;> simp only [shiftIndex_apply] <;> omega

theorem relations : CuntzTwoRelations shift := by
  constructor
  · intro i
    change (shift i).adjoint.comp (shift i) = 1
    exact (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mp
      (l2Embedding (shiftIndex i)).isometry
  · apply l2_clm_ext
    intro x c
    obtain ⟨j,y,rfl⟩ := shiftIndex_surjective x
    simp only [sum_apply, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, one_apply_eq_self]
    rw [Finset.sum_eq_single j]
    · simp only [shift_adjoint_single_same, shift_single]
    · intro i _ hij
      rw [shift_adjoint_single_ne hij y c, map_zero]
    · simp

end NuclearUltrapower.CuntzModel
end
end

section

noncomputable section
open scoped MonoidAlgebra
namespace NuclearUltrapower.CuntzPolynomial
instance instStarMulWord : StarMul Word where
  star_mul w v := by
    apply FreeMonoid.toList.injective
    change ((FreeMonoid.toList w ++ FreeMonoid.toList v).reverse.map flip) =
      (FreeMonoid.toList v).reverse.map flip ++ (FreeMonoid.toList w).reverse.map flip
    simp

def involutionAdd : Poly →+ Poly :=
  MonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapDomain.addMonoidHom (star : Word → Word)).comp
      ((Finsupp.mapRange.addMonoidHom (starAddEquiv : ℂ ≃+ ℂ).toAddMonoidHom).comp
        MonoidAlgebra.coeffAddEquiv.toAddMonoidHom))
instance instStarPoly : Star Poly := ⟨involutionAdd⟩
@[simp] theorem star_single (w : Word) (c : ℂ) :
    star (MonoidAlgebra.single w c) = MonoidAlgebra.single (star w) (star c) := by
  change involutionAdd _ = _
  simp [involutionAdd]
instance instInvolutiveStarPoly : InvolutiveStar Poly where
  star_involutive x := by
    have h : involutionAdd.comp involutionAdd = AddMonoidHom.id _ := by
      apply MonoidAlgebra.addMonoidHom_ext
      intro w c
      change star (star (MonoidAlgebra.single w c)) = MonoidAlgebra.single w c
      simp only [star_single, star_star]
    exact congrArg (fun f : Poly →+ Poly => f x) h
instance instStarAddMonoidPoly : StarAddMonoid Poly where
  star_add := involutionAdd.map_add
instance instStarModuleComplexPoly : StarModule ℂ Poly where
  star_smul c x := by
    let f : Poly →+ Poly := involutionAdd.comp (DistribSMul.toAddMonoidHom Poly c)
    let g : Poly →+ Poly := (DistribSMul.toAddMonoidHom Poly (star c)).comp involutionAdd
    have h : f = g := by
      apply MonoidAlgebra.addMonoidHom_ext
      intro a b
      change star (c • MonoidAlgebra.single a b) = star c • star (MonoidAlgebra.single a b)
      simp only [MonoidAlgebra.smul_single, star_single, star_mul, smul_eq_mul, mul_comm]
    exact congrArg (fun f : Poly →+ Poly => f x) h
instance instStarRingPoly : StarRing Poly where
  star_add := involutionAdd.map_add
  star_mul x y := by
    induction x using MonoidAlgebra.induction_on with
    | of a =>
      induction y using MonoidAlgebra.induction_on with
      | of b => simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
          one_mul, star_single, star_one, star_mul]
      | add y z hy hz => simp only [mul_add, star_add, hy, hz, add_mul]
      | smul c y hy => simp only [mul_smul_comm, star_smul, hy, smul_mul_assoc]
    | add x z hx hz => simp only [add_mul, star_add, hx, hz, mul_add]
    | smul c x hx => simp only [smul_mul_assoc, star_smul, hx, mul_smul_comm]

variable {D : Type*} [CStarAlgebra D]

def evalWord (r : Fin 2 → D) : Word →* D := FreeMonoid.lift (evalLetter r)
@[simp] theorem evalWord_of (r : Fin 2 → D) (a : Letter) :
    evalWord r (FreeMonoid.of a) = evalLetter r a := rfl
@[simp] theorem evalWord_star (r : Fin 2 → D) (w : Word) :
    evalWord r (star w) = star (evalWord r w) := by
  induction w using FreeMonoid.recOn with
  | one => simp
  | of_mul a w ih => simp only [star_mul, star_word_of, map_mul, evalWord_of, evalLetter_flip, ih]

def evaluate (r : Fin 2 → D) : Poly →⋆ₐ[ℂ] D where
  __ := MonoidAlgebra.lift ℂ D Word (evalWord r)
  map_star' x := by
    change (MonoidAlgebra.lift ℂ D Word (evalWord r)) (star x) =
      star ((MonoidAlgebra.lift ℂ D Word (evalWord r)) x)
    induction x using MonoidAlgebra.induction_on with
    | of w => simp only [MonoidAlgebra.of_apply,star_single,star_one,
        MonoidAlgebra.lift_single,one_smul,evalWord_star]
    | add x y hx hy => simp only [star_add,map_add,hx,hy]
    | smul c x hx => simp only [star_smul,map_smul,hx]
@[simp] theorem evaluate_single (r : Fin 2 → D) (w : Word) (c : ℂ) :
    evaluate r (MonoidAlgebra.single w c) = c • evalWord r w :=
  MonoidAlgebra.lift_single _ _ _

def generator (i : Fin 2) : Poly := MonoidAlgebra.single (FreeMonoid.of (i,false)) 1
@[simp] theorem evaluate_generator (r : Fin 2 → D) (i : Fin 2) : evaluate r (generator i) = r i := by
  simp [generator,evalLetter]

theorem evalLetter_norm_le (r : Fin 2 → D) (hr : CuntzTwoRelations r) (a : Letter) :
    ‖evalLetter r a‖ ≤ 1 := by
  have hh : ‖r a.1‖ * ‖r a.1‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, hr.1]
    cases subsingleton_or_nontrivial D with
    | inl h => simp [Subsingleton.elim (1 : D) 0]
    | inr h => simp
  have h : ‖r a.1‖ ≤ 1 := by nlinarith [norm_nonneg (r a.1)]
  simp only [evalLetter]
  split_ifs <;> simpa only [norm_star] using h

theorem evalWord_norm_le (r : Fin 2 → D) (hr : CuntzTwoRelations r) (w : Word) :
    ‖evalWord r w‖ ≤ 1 := by
  induction w using FreeMonoid.recOn with
  | one =>
    rw [map_one]
    cases subsingleton_or_nontrivial D with
    | inl h => simp [Subsingleton.elim (1 : D) 0]
    | inr h => simp
  | of_mul a w ih =>
    rw [map_mul, evalWord_of]
    exact (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (evalLetter_norm_le r hr a)).trans ih)

end NuclearUltrapower.CuntzPolynomial
end
end

section

noncomputable section
open scoped MonoidAlgebra
namespace NuclearUltrapower.CuntzPolynomial

/-- The possible operator norms in all unital models of the Cuntz relations. -/
def modelNormSet (x : Poly) : Set ℝ :=
  {t | ∃ (D : Type) (_ : CStarAlgebra D) (ρ : Fin 2 → D) (_ : CuntzTwoRelations ρ), t = ‖evaluate ρ x‖}

theorem modelNormSet_nonempty (x : Poly) : (modelNormSet x).Nonempty := by
  exact ⟨‖evaluate CuntzModel.shift x‖, CuntzModel.Space →L[ℂ] CuntzModel.Space,
    inferInstance, CuntzModel.shift, CuntzModel.relations, rfl⟩

/-- Every finite star-polynomial is bounded uniformly over ALL models. -/
theorem models_bounded (x : Poly) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (D : Type) [CStarAlgebra D] (ρ : Fin 2 → D) (_ : CuntzTwoRelations ρ), ‖evaluate ρ x‖ ≤ M := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    refine ⟨1, zero_le_one, ?_⟩
    intro D _ ρ hρ
    simp only [MonoidAlgebra.of_apply, evaluate_single, one_smul]
    exact evalWord_norm_le ρ hρ g
  | add x y hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M+N, add_nonneg hM hN, ?_⟩
    intro D _ ρ hρ
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hx D ρ hρ) (hy D ρ hρ))
  | smul c x hx =>
    obtain ⟨M, hM, hx⟩ := hx
    refine ⟨‖c‖*M, mul_nonneg (norm_nonneg _) hM, ?_⟩
    intro D _ ρ hρ
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hx D ρ hρ) (norm_nonneg _)

theorem modelNormSet_bdd (x : Poly) : BddAbove (modelNormSet x) := by
  obtain ⟨M, _, hx⟩ := models_bounded x
  refine ⟨M, ?_⟩
  rintro r ⟨D, inst, ρ, hρ, rfl⟩
  exact hx D ρ hρ

/-- The universal C*-seminorm over all Cuntz models. -/
def universalNorm (x : Poly) : ℝ := sSup (modelNormSet x)

theorem model_norm_le (x : Poly) (D : Type) [CStarAlgebra D] (ρ : Fin 2 → D) (hρ : CuntzTwoRelations ρ) :
    ‖evaluate ρ x‖ ≤ universalNorm x :=
  le_csSup (modelNormSet_bdd x) ⟨D, inferInstance, ρ, hρ, rfl⟩

theorem universalNorm_le {x : Poly} {M : ℝ}
    (h : ∀ (D : Type) [CStarAlgebra D] (ρ : Fin 2 → D) (_ : CuntzTwoRelations ρ), ‖evaluate ρ x‖ ≤ M) :
    universalNorm x ≤ M := by
  apply csSup_le (modelNormSet_nonempty x)
  rintro r ⟨D, inst, ρ, hρ, rfl⟩
  exact h D ρ hρ

theorem universalNorm_nonneg (x : Poly) : 0 ≤ universalNorm x :=
  (norm_nonneg _).trans (model_norm_le x (CuntzModel.Space →L[ℂ] CuntzModel.Space)
    CuntzModel.shift CuntzModel.relations)

@[simp] theorem universalNorm_zero : universalNorm (0 : Poly) = 0 := by
  apply le_antisymm _ (universalNorm_nonneg _)
  apply universalNorm_le
  intro D _ ρ hρ
  simp

/-- The universal model supremum is a submultiplicative seminorm. -/
def universalSeminorm : RingSeminorm Poly where
  toFun := universalNorm
  map_zero' := universalNorm_zero
  add_le' x y := by
    apply universalNorm_le
    intro D _ ρ hρ
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (model_norm_le x D ρ hρ) (model_norm_le y D ρ hρ))
  neg' x := by
    apply le_antisymm
    · apply universalNorm_le
      intro D _ ρ hρ
      simpa only [map_neg, norm_neg] using model_norm_le x D ρ hρ
    · have h : universalNorm x ≤ universalNorm (-x) := by
        apply universalNorm_le
        intro D _ ρ hρ
        have := model_norm_le (-x) D ρ hρ
        simpa only [map_neg, norm_neg] using this
      exact h
  mul_le' x y := by
    apply universalNorm_le
    intro D _ ρ hρ
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (model_norm_le x D ρ hρ) (model_norm_le y D ρ hρ)
      (norm_nonneg _) (universalNorm_nonneg _))

instance instSeminormedRingPoly : SeminormedRing Poly := universalSeminorm.toSeminormedRing

@[simp] theorem norm_eq_universalNorm (x : Poly) : ‖x‖ = universalNorm x := rfl

instance instNormedStarGroupPoly : NormedStarGroup Poly where
  norm_star_le x := by
    apply universalNorm_le
    intro D _ ρ hρ
    simpa only [map_star, norm_star, norm_eq_universalNorm] using model_norm_le x D ρ hρ

instance instNormedAlgebraComplexPoly : NormedAlgebra ℂ Poly where
  norm_smul_le c x := by
    apply universalNorm_le
    intro D _ ρ hρ
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (model_norm_le x D ρ hρ) (norm_nonneg _)

/-- C*-identity at the seminorm level, which survives separated completion. -/
theorem norm_mul_self_le (x : Poly) : ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
  have h : ‖x‖ ≤ Real.sqrt ‖star x * x‖ := by
    apply universalNorm_le
    intro D _ ρ hρ
    apply (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mpr
    have hm := model_norm_le (star x*x) D ρ hρ
    simpa only [map_mul, map_star, CStarRing.norm_star_mul_self, pow_two, norm_eq_universalNorm] using hm
  nlinarith [Real.sq_sqrt (norm_nonneg (star x*x)), norm_nonneg x]

/-- Every model evaluation is contractive for the universal seminorm. -/
theorem evaluate_continuous {D : Type} [CStarAlgebra D] (ρ : Fin 2 → D) (hρ : CuntzTwoRelations ρ) :
    Continuous (evaluate ρ) := by
  apply (evaluate ρ).toLinearMap.mkContinuous 1 ?_ |>.continuous
  intro x
  change ‖evaluate ρ x‖ ≤ 1 * universalNorm x
  simpa only [one_mul] using model_norm_le x D ρ hρ

end NuclearUltrapower.CuntzPolynomial

namespace NuclearUltrapower.CuntzUniversal
open UniformSpace CuntzPolynomial

/-- The universal completion is separated; Cuntz relations vanish in its norm. -/
def Algebra := Completion Poly
instance instCStarAlgebraAlgebra : CStarAlgebra Algebra := UniversalCompletion.cstarAlgebra norm_mul_self_le

def inclusion : Poly →⋆ₐ[ℂ] Algebra := UniversalCompletion.inclusion
def generator (i : Fin 2) : Algebra := inclusion (CuntzPolynomial.generator i)

def modelMap {D : Type} [CStarAlgebra D] (r : Fin 2 → D) (hr : CuntzTwoRelations r) :
    Algebra →⋆ₐ[ℂ] D := UniversalCompletion.extend (evaluate r) (evaluate_continuous r hr)

@[simp] theorem modelMap_coe {D : Type} [CStarAlgebra D] (r : Fin 2 → D)
    (hr : CuntzTwoRelations r) (x : Poly) : modelMap r hr (inclusion x) = evaluate r x :=
  UniversalCompletion.extend_coe _ _ _

@[simp] theorem modelMap_generator {D : Type} [CStarAlgebra D] (r : Fin 2 → D)
    (hr : CuntzTwoRelations r) (i : Fin 2) : modelMap r hr (generator i) = r i := by
  rw [generator,modelMap_coe,evaluate_generator]

end NuclearUltrapower.CuntzUniversal
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzWords
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.CuntzWords

instance instFintypeWord (n : ℕ) : Fintype (Word n) := by
  induction n with
  | zero => exact PUnit.fintype
  | succ n ih =>
    letI : Fintype (Word n) := ih
    exact inferInstanceAs (Fintype (Fin 2 × Word n))

@[simp] theorem index_height {n : ℕ} (w : Word n) : (index w).1 = (n : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases w with ⟨i,w⟩
    simp only [index_succ,CuntzModel.shiftIndex_apply,ih,Nat.cast_add,Nat.cast_one]

end NuclearUltrapower.CuntzWords
end
end

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords

attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instDecidableEqIndex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

@[simp] theorem right_coordinate (T : H →L[ℂ] H) (k : Index) (x : H) :
    right T (coordinate k x) = coordinate k (T x) := by
  change completedTensorMap 1 T (coordinate k x) = _
  rw [coordinate_apply,completedTensorMap_coe]
  simp only [TensorProduct.mapL_tmul,one_apply_eq_self,coordinate_apply]

end NuclearUltrapower.CuntzAveraging
end
end

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

def row (n : ℕ) : H →L[ℂ] Target H :=
  ∑ w : Word n, (coordinate (index w)).comp (star (R (value generator w)))

@[simp] theorem row_apply (n : ℕ) (x : H) :
    row R n x = ∑ w : Word n, coordinate (index w) (star (R (value generator w)) x) := by
  simp only [row,sum_apply,ContinuousLinearMap.comp_apply]

@[simp] theorem row_support (n : ℕ) : (row R n).comp (R 1) = row R n := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,row_apply]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  change (star (R (value generator w)) * R 1) x = _
  rw [← map_star,← map_mul,mul_one]

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzIntertwining
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

def rowSum (N : ℕ) : H →L[ℂ] Target H := ∑ k ∈ Finset.range N, row R k

@[simp] theorem rowSum_apply (N : ℕ) (x : H) :
    rowSum R N x = ∑ k ∈ Finset.range N, row R k x := by simp only [rowSum,sum_apply]

/-- Square-length averages avoid square-root denominators while retaining the
exact isometry on the support of an arbitrary nonunital representation. -/
def weight (n : ℕ) : ℂ := (((n : ℝ)+1)⁻¹ : ℝ)

@[simp] theorem weight_norm (n : ℕ) : ‖weight n‖ = ((n : ℝ)+1)⁻¹ := by
  rw [weight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]

def averaged (n : ℕ) : H →L[ℂ] Target H := weight n • rowSum R ((n+1)^2)

end NuclearUltrapower.CuntzAveraging
end
end

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

local instance instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace : IsBoundedSMul ℂ (CuntzModel.Space ⊗[ℂ] H) := NormedSpace.toIsBoundedSMul

local instance instNormedSpaceComplexTarget_r19da16_1 : NormedSpace ℂ (Target H) := inferInstance
def concrete : Algebra →⋆ₐ[ℂ] (Space →L[ℂ] Space) :=
  modelMap shift CuntzModel.relations

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
def label1222 : Mat3 := [1, -1, -1, 0, 1, 0, 0, 1, 1]
def label1241 : Mat3 := [1, -1, -1, 0, 1, 1, 0, 0, 1]
def label1368 : Mat3 := [1, -1, 0, -1, 2, 0, 0, 0, 1]
def label1422 : Mat3 := [1, -1, 0, 0, 1, -1, 0, 0, 1]
def label1440 : Mat3 := [1, -1, 0, 0, 1, 0, -1, 0, 1]
def label1441 : Mat3 := [1, -1, 0, 0, 1, 0, -1, 1, 1]
def label1446 : Mat3 := [1, -1, 0, 0, 1, 0, 0, -1, 1]
def label1447 : Mat3 := [1, -1, 0, 0, 1, 0, 0, 0, 1]
def label1448 : Mat3 := [1, -1, 0, 0, 1, 0, 0, 1, 1]
def label1453 : Mat3 := [1, -1, 0, 0, 1, 0, 1, -1, 1]
def label1454 : Mat3 := [1, -1, 0, 0, 1, 0, 1, 0, 1]
def label1472 : Mat3 := [1, -1, 0, 0, 1, 1, 0, 0, 1]
def label1525 : Mat3 := [1, -1, 0, 1, 0, 0, 0, 0, 1]
def label1653 : Mat3 := [1, -1, 1, 0, 1, -1, 0, 0, 1]
def label1672 : Mat3 := [1, -1, 1, 0, 1, 0, 0, -1, 1]
def label1673 : Mat3 := [1, -1, 1, 0, 1, 0, 0, 0, 1]
def label1847 : Mat3 := [1, 0, -2, 0, 1, 0, 0, 0, 1]
def label1938 : Mat3 := [1, 0, -1, -1, 1, 0, 0, 0, 1]
def label1954 : Mat3 := [1, 0, -1, -1, 1, 1, 0, 0, 1]
def label2009 : Mat3 := [1, 0, -1, 0, 1, -1, 0, 0, 1]
def label2022 : Mat3 := [1, 0, -1, 0, 1, 0, -1, 0, 2]
def label2027 : Mat3 := [1, 0, -1, 0, 1, 0, 0, -1, 1]
def label2028 : Mat3 := [1, 0, -1, 0, 1, 0, 0, 0, 1]
def label2029 : Mat3 := [1, 0, -1, 0, 1, 0, 0, 1, 1]
def label2034 : Mat3 := [1, 0, -1, 0, 1, 0, 1, 0, 0]
def label2047 : Mat3 := [1, 0, -1, 0, 1, 1, 0, 0, 1]
def label2100 : Mat3 := [1, 0, -1, 1, 1, -1, 0, 0, 1]
def label2116 : Mat3 := [1, 0, -1, 1, 1, 0, 0, 0, 1]
def label2247 : Mat3 := [1, 0, 0, -2, 1, 0, 0, 0, 1]
def label2345 : Mat3 := [1, 0, 0, -1, 1, -1, 0, 0, 1]
def label2350 : Mat3 := [1, 0, 0, -1, 1, -1, 1, 0, 1]
def label2369 : Mat3 := [1, 0, 0, -1, 1, 0, -1, 0, 1]
end NuclearUltrapower.SOS
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
def toMatrix (a : Mat3) : Matrix (Fin 3) (Fin 3) ℤ := fun i j => entry a i j

end NuclearUltrapower.SOS

end

end OAI
end


