-- Prove2me | Definitions.Def_OAIQ019N001
-- name    : OAIQ019N001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:58:20.680751+00:00
-- url     : https://prove2.me/theorems/a9007baa-5468-496b-8ebc-8385b2dea6b4
-- title:
--   Definitions bundle OAIQ019N001 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 142 declarations of OpenAI's Lean: 52 definitions, 1 inductive type or structure, 27 instances and 62 theorems. The definitions and types are `OAI.NuclearUltrapower.Displacement.dist`, `OAI.NuclearUltrapower.Elementary.Residue3`, `OAI.NuclearUltrapower.Elementary.stableLetter`, `OAI.NuclearUltrapower.FiniteUnitaryRep`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Embeds`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Equivalent`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Irreducible`, `OAI.NuclearUltrapower.FiniteUnitaryRep.pull`, `OAI.NuclearUltrapower.FiniteUnitaryRep.restrict`, `OAI.NuclearUltrapower.GroupStarAlgebra.evaluate`, `OAI.NuclearUltrapower.GroupStarAlgebra.involutionAdd`, `OAI.NuclearUltrapower.GroupStarAlgebra.modelNormSet`, `OAI.NuclearUltrapower.GroupStarAlgebra.universalNorm`, `OAI.NuclearUltrapower.GroupStarAlgebra.universalSeminorm`, `OAI.NuclearUltrapower.HilbertTensor`, `OAI.NuclearUltrapower.SOS.SL`, `OAI.NuclearUltrapower.SOS.gramRow0`, `OAI.NuclearUltrapower.SOS.gramRow10`, `OAI.NuclearUltrapower.UltraPreHilbert`, `OAI.NuclearUltrapower.UltraPreHilbert.family`, `OAI.NuclearUltrapower.UniversalCompletion.cstarAlgebra`, `OAI.NuclearUltrapower.UniversalCompletion.extend`, `OAI.NuclearUltrapower.UniversalCompletion.inclusion`, `OAI.NuclearUltrapower.VariableUltra.Algebra`, `OAI.NuclearUltrapower.VariableUltra.Rel`, `OAI.NuclearUltrapower.VariableUltra.Seq`, `OAI.NuclearUltrapower.VariableUltra.con`, `OAI.NuclearUltrapower.VariableUltra.entryOrder`, `OAI.NuclearUltrapower.VariableUltra.eval`, `OAI.NuclearUltrapower.VariableUltra.isoSequence`, `OAI.NuclearUltrapower.VariableUltra.matrixEntry`, `OAI.NuclearUltrapower.VariableUltra.matrixFamily`, `OAI.NuclearUltrapower.VariableUltra.matrixQuotient`, `OAI.NuclearUltrapower.VariableUltra.mk`, `OAI.NuclearUltrapower.VariableUltra.null`, `OAI.NuclearUltrapower.VariableUltra.operatorQuotient`, `OAI.NuclearUltrapower.VariableUltra.operatorSeq`, `OAI.NuclearUltrapower.VariableUltra.quotientEquiv`, `OAI.NuclearUltrapower.VariableUltra.quotientIsoUnitary`, `OAI.NuclearUltrapower.VariableUltra.quotientIsometry` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `NuclearUltrapower_CuntzIntertwining`, `NuclearUltrapower_DyadicGroup`, `NuclearUltrapower_FiniteInduction`, `NuclearUltrapower_FiniteRepresentations`, `NuclearUltrapower_FullGroupAlgebra`, `NuclearUltrapower_HilbertSchmidt`, `NuclearUltrapower_HilbertUltraproduct`, `NuclearUltrapower_Kazhdan`, `NuclearUltrapower_SOSResidual`, `NuclearUltrapower_SOSSemantics`, `NuclearUltrapower_TensorGap`, `NuclearUltrapower_TensorNorms`, `NuclearUltrapower_VariableUltraproduct`.
--
--   **Imports.** It imports the published bundle `Def_NuclearUltrapower`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ019N039`, `OAIQ019N040` and `OAIQ019N041`.
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
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FullGroupAlgebra
attribute [-instance] _root_.OAI.NuclearUltrapower.instStarNormUltrapower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped MonoidAlgebra
namespace NuclearUltrapower.GroupStarAlgebra
variable {Γ : Type*} [Group Γ]

/-- Algebraic involution on the complex group ring: conjugate coefficients and
invert group elements. This is not the pointwise star on coefficient functions. -/
def involutionAdd : ℂ[Γ] →+ ℂ[Γ] :=
  MonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapDomain.addMonoidHom (Inv.inv : Γ → Γ)).comp
      ((Finsupp.mapRange.addMonoidHom (starAddEquiv : ℂ ≃+ ℂ).toAddMonoidHom).comp
        MonoidAlgebra.coeffAddEquiv.toAddMonoidHom))

instance instStarMonoidAlgebraComplex_solutions : Star ℂ[Γ] := ⟨involutionAdd⟩

@[simp] theorem star_single (g : Γ) (c : ℂ) :
    star (MonoidAlgebra.single g c) = MonoidAlgebra.single g⁻¹ (star c) := by
  change involutionAdd _ = _
  simp [involutionAdd]

theorem star_add' (x y : ℂ[Γ]) : star (x+y) = star x + star y :=
  involutionAdd.map_add x y

instance instInvolutiveStarMonoidAlgebraComplex_solutions : InvolutiveStar ℂ[Γ] where
  star_involutive x := by
    have h : (involutionAdd (Γ := Γ)).comp involutionAdd = AddMonoidHom.id _ := by
      apply MonoidAlgebra.addMonoidHom_ext
      intro g c
      change star (star (MonoidAlgebra.single g c)) = MonoidAlgebra.single g c
      simp only [star_single, inv_inv, star_star]
    exact congrArg (fun f : ℂ[Γ] →+ ℂ[Γ] => f x) h

instance instStarAddMonoidMonoidAlgebraComplex_solutions : StarAddMonoid ℂ[Γ] where
  star_add := star_add'

instance instStarModuleComplexMonoidAlgebra_solutions : StarModule ℂ ℂ[Γ] where
  star_smul c x := by
    let f : ℂ[Γ] →+ ℂ[Γ] := (involutionAdd (Γ := Γ)).comp
      (DistribSMul.toAddMonoidHom ℂ[Γ] c)
    let g : ℂ[Γ] →+ ℂ[Γ] := (DistribSMul.toAddMonoidHom ℂ[Γ] (star c)).comp involutionAdd
    have h : f = g := by
      apply MonoidAlgebra.addMonoidHom_ext
      intro a b
      change star (c • MonoidAlgebra.single a b) = star c • star (MonoidAlgebra.single a b)
      simp only [MonoidAlgebra.smul_single, star_single, star_mul, smul_eq_mul, mul_comm]
    exact congrArg (fun f : ℂ[Γ] →+ ℂ[Γ] => f x) h

variable {D : Type*} [CStarAlgebra D]

/-- A unitary group representation evaluates finite linear combinations. -/
def evaluate (ρ : Γ →* unitary D) : ℂ[Γ] →⋆ₐ[ℂ] D where
  __ := MonoidAlgebra.lift ℂ D Γ ((unitary D).subtype.comp ρ)
  map_star' x := by
    change (MonoidAlgebra.lift ℂ D Γ ((unitary D).subtype.comp ρ)) (star x) =
      star ((MonoidAlgebra.lift ℂ D Γ ((unitary D).subtype.comp ρ)) x)
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      simp only [MonoidAlgebra.of_apply, star_single, star_one, MonoidAlgebra.lift_single,
        one_smul, MonoidHom.comp_apply, Submonoid.subtype_apply, ρ.map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
    | add x y hx hy => simp only [star_add, map_add, hx, hy]
    | smul c x hx => simp only [star_smul, map_smul, hx]

@[simp] theorem evaluate_single (ρ : Γ →* unitary D) (g : Γ) (c : ℂ) :
    evaluate ρ (MonoidAlgebra.single g c) = c • (ρ g : D) :=
  MonoidAlgebra.lift_single _ _ _

end NuclearUltrapower.GroupStarAlgebra

namespace NuclearUltrapower.GroupStarAlgebra
open scoped MonoidAlgebra
variable {Γ : Type} [Group Γ]

/-- The possible operator norms in all unital C*-models of the group. -/
def modelNormSet (x : ℂ[Γ]) : Set ℝ :=
  {t | ∃ (D : Type) (_ : CStarAlgebra D) (ρ : Γ →* unitary D), t = ‖evaluate ρ x‖}

theorem modelNormSet_nonempty (x : ℂ[Γ]) : (modelNormSet x).Nonempty := by
  exact ⟨‖evaluate (1 : Γ →* unitary ℂ) x‖, ℂ, inferInstance, 1, rfl⟩

/-- Every finite group-ring expression is bounded uniformly over ALL models. -/
theorem models_bounded (x : ℂ[Γ]) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (D : Type) [CStarAlgebra D] (ρ : Γ →* unitary D), ‖evaluate ρ x‖ ≤ M := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    refine ⟨1, zero_le_one, ?_⟩
    intro D _ ρ
    simp only [MonoidAlgebra.of_apply, evaluate_single, one_smul]
    cases subsingleton_or_nontrivial D with
    | inl h => simp [Subsingleton.elim (ρ g : D) 0]
    | inr h => exact (CStarRing.norm_coe_unitary (ρ g)).le
  | add x y hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M+N, add_nonneg hM hN, ?_⟩
    intro D _ ρ
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hx D ρ) (hy D ρ))
  | smul c x hx =>
    obtain ⟨M, hM, hx⟩ := hx
    refine ⟨‖c‖*M, mul_nonneg (norm_nonneg _) hM, ?_⟩
    intro D _ ρ
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hx D ρ) (norm_nonneg _)

theorem modelNormSet_bdd (x : ℂ[Γ]) : BddAbove (modelNormSet x) := by
  obtain ⟨M, _, hx⟩ := models_bounded x
  refine ⟨M, ?_⟩
  rintro r ⟨D, inst, ρ, rfl⟩
  exact hx D ρ

/-- The full, not the reduced, universal C*-seminorm. -/
def universalNorm (x : ℂ[Γ]) : ℝ := sSup (modelNormSet x)

theorem model_norm_le (x : ℂ[Γ]) (D : Type) [CStarAlgebra D] (ρ : Γ →* unitary D) :
    ‖evaluate ρ x‖ ≤ universalNorm x :=
  le_csSup (modelNormSet_bdd x) ⟨D, inferInstance, ρ, rfl⟩

theorem universalNorm_le {x : ℂ[Γ]} {M : ℝ}
    (h : ∀ (D : Type) [CStarAlgebra D] (ρ : Γ →* unitary D), ‖evaluate ρ x‖ ≤ M) :
    universalNorm x ≤ M := by
  apply csSup_le (modelNormSet_nonempty x)
  rintro r ⟨D, inst, ρ, rfl⟩
  exact h D ρ

theorem universalNorm_nonneg (x : ℂ[Γ]) : 0 ≤ universalNorm x :=
  (norm_nonneg _).trans (model_norm_le x ℂ 1)

@[simp] theorem universalNorm_zero : universalNorm (0 : ℂ[Γ]) = 0 := by
  apply le_antisymm _ (universalNorm_nonneg _)
  apply universalNorm_le
  intro D _ ρ
  simp

/-- The universal model supremum is a submultiplicative seminorm. -/
def universalSeminorm : RingSeminorm ℂ[Γ] where
  toFun := universalNorm
  map_zero' := universalNorm_zero
  add_le' x y := by
    apply universalNorm_le
    intro D _ ρ
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (model_norm_le x D ρ) (model_norm_le y D ρ))
  neg' x := by
    apply le_antisymm
    · apply universalNorm_le
      intro D _ ρ
      simpa only [map_neg, norm_neg] using model_norm_le x D ρ
    · have h : universalNorm x ≤ universalNorm (-x) := by
        apply universalNorm_le
        intro D _ ρ
        have := model_norm_le (-x) D ρ
        simpa only [map_neg, norm_neg] using this
      exact h
  mul_le' x y := by
    apply universalNorm_le
    intro D _ ρ
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (model_norm_le x D ρ) (model_norm_le y D ρ)
      (norm_nonneg _) (universalNorm_nonneg _))

instance instSeminormedRingMonoidAlgebraComplex_solutions : SeminormedRing ℂ[Γ] := universalSeminorm.toSeminormedRing

@[simp] theorem norm_eq_universalNorm (x : ℂ[Γ]) : ‖x‖ = universalNorm x := rfl

end NuclearUltrapower.GroupStarAlgebra

noncomputable section
open UniformSpace
namespace NuclearUltrapower.UniversalCompletion

variable {R : Type*} [SeminormedRing R] [StarRing R] [NormedStarGroup R]

instance completionStar : Star (Completion R) := ⟨Completion.map star⟩

@[simp] theorem star_coe (x : R) : star (x : Completion R) = (star x : R) :=
  Completion.map_coe (by exact star_isometry.uniformContinuous) x

instance completionContinuousStar : ContinuousStar (Completion R) where
  continuous_star := Completion.continuous_map

instance completionInvolutiveStar : InvolutiveStar (Completion R) where
  star_involutive x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

instance completionStarRing : StarRing (Completion R) where
  star_mul x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simp only [← Completion.coe_mul, star_coe, star_mul]
  star_add x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simp only [← Completion.coe_add, star_coe, star_add]

variable [NormedAlgebra ℂ R] [StarModule ℂ R]

instance completionNormedAlgebra : NormedAlgebra ℂ (Completion R) where
  norm_smul_le := norm_smul_le

instance completionStarModule : StarModule ℂ (Completion R) where
  star_smul c x := by
    induction x using Completion.induction_on with
    | hp =>
      apply isClosed_eq
      · exact continuous_star.comp (continuous_id.const_smul c)
      · exact continuous_star.const_smul (star c)
    | ih x => simp only [← Completion.coe_smul, star_coe, star_smul]

/-- The separated completion of a C*-seminormed star algebra is a C*-algebra. -/
@[instance_reducible] def cstarAlgebra (hc : ∀ x : R, ‖x‖ * ‖x‖ ≤ ‖star x * x‖) : CStarAlgebra (Completion R) where
  norm_mul_self_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa only [star_coe, ← Completion.coe_mul, Completion.norm_coe] using hc x

/-- The canonical, dense star algebra map to the universal completion. -/
def inclusion : R →⋆ₐ[ℂ] Completion R where
  __ := Completion.coeRingHom
  commutes' c := by
    change ((algebraMap ℂ R c : R) : Completion R) = algebraMap ℂ (Completion R) c
    exact (Completion.algebraMap_def R ℂ c).symm
  map_star' x := by
    change ((star x : R) : Completion R) = star (x : Completion R)
    exact (star_coe x).symm

/-- Any continuous model map extends uniquely over the completed algebra. -/
def extend {D : Type*} [CStarAlgebra D] (f : R →⋆ₐ[ℂ] D) (hf : Continuous f) :
    Completion R →⋆ₐ[ℂ] D where
  __ := Completion.extensionHom f.toRingHom hf
  commutes' c := by
    change Completion.extensionHom f.toRingHom hf (algebraMap ℂ (Completion R) c) = _
    rw [Completion.algebraMap_def, Completion.extensionHom_coe]
    exact f.commutes c
  map_star' x := by
    change Completion.extensionHom f.toRingHom hf (star x) =
      star (Completion.extensionHom f.toRingHom hf x)
    have hc : Continuous (Completion.extensionHom f.toRingHom hf) :=
      Completion.continuous_extension
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (hc.comp continuous_star) (continuous_star.comp hc)
    | ih x =>
      simp only [star_coe, Completion.extensionHom_coe]
      exact map_star f x

omit [StarModule ℂ R] in
@[simp] theorem extend_coe {D : Type*} [CStarAlgebra D]
    (f : R →⋆ₐ[ℂ] D) (hf : Continuous f) (x : R) : extend f hf (x : Completion R) = f x :=
  Completion.extensionHom_coe f.toRingHom hf x

end NuclearUltrapower.UniversalCompletion

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace NuclearUltrapower

section Defects
variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (T : A →⋆ₙₐ[ℂ] (K →L[ℂ] K))

def intertwiningDefect (W : H →L[ℂ] K) : A →ₗ[ℂ] (H →L[ℂ] K) where
  toFun a := W.comp (R a) - (T a).comp W
  map_add' a b := by
    simp only [map_add,ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp]
    abel
  map_smul' c a := by
    simp only [map_smul,ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp,smul_sub,RingHom.id_apply]

@[simp] theorem intertwiningDefect_apply (W : H →L[ℂ] K) (a : A) :
    intertwiningDefect R T W a = W.comp (R a) - (T a).comp W := rfl

end Defects
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_DyadicGroup
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter

namespace NuclearUltrapower

@[simp] theorem dyadicTwo_val : (dyadicTwo : Dyadic) = 2 := by
  simp [dyadicTwo, IsUnit.unit_spec]

/-! The exact integral subgroup and dilation in the tensor-norm formulation. -/

end NuclearUltrapower

end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FiniteRepresentations
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter
noncomputable section
open scoped InnerProductSpace

namespace NuclearUltrapower

/-- A nonzero finite-dimensional unitary representation. -/
structure FiniteUnitaryRep (Γ : Type u) [Group Γ] where
  carrier : Type v
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  [finite : FiniteDimensional ℂ carrier]
  [nontrivial : Nontrivial carrier]
  action : Γ →* (carrier ≃ₗᵢ[ℂ] carrier)

attribute [instance] FiniteUnitaryRep.normed FiniteUnitaryRep.inner
  FiniteUnitaryRep.complete FiniteUnitaryRep.finite FiniteUnitaryRep.nontrivial
instance instCoeSortFiniteUnitaryRepType {Γ : Type u} [Group Γ] : CoeSort (FiniteUnitaryRep.{u,v} Γ) (Type v) :=
  ⟨FiniteUnitaryRep.carrier⟩

variable {Γ : Type u} [Group Γ]

namespace FiniteUnitaryRep

/-- Irreducibility with exactly the invariant-subspace convention of the source. -/
def Irreducible (π : FiniteUnitaryRep.{u,v} Γ) : Prop :=
  ∀ W : Submodule ℂ π, (∀ g x, x ∈ W → π.action g x ∈ W) → W = ⊥ ∨ W = ⊤

def pull (π : FiniteUnitaryRep.{u,v} Γ) (θ : Monoid.End Γ) : FiniteUnitaryRep.{u,v} Γ :=
  { π with action := π.action.comp θ }

@[simp] theorem pull_action (π : FiniteUnitaryRep.{u,v} Γ) (θ : Monoid.End Γ) (g : Γ) :
    (π.pull θ).action g = π.action (θ g) := rfl

@[simp] theorem pull_one (π : FiniteUnitaryRep.{u,v} Γ) : π.pull 1 = π := by
  cases π
  simp [pull, show (1 : Monoid.End Γ) = MonoidHom.id Γ from rfl]

@[simp] theorem pull_pull (π : FiniteUnitaryRep.{u,v} Γ) (θ ψ : Monoid.End Γ) :
    (π.pull θ).pull ψ = π.pull (θ * ψ) := rfl

/-- Isometric inclusion as a subrepresentation: no quotients of representations. -/
def Embeds (π τ : FiniteUnitaryRep.{u,v} Γ) : Prop :=
  ∃ T : π →ₗᵢ[ℂ] τ, ∀ g x, T (π.action g x) = τ.action g (T x)

/-- Unitary equivalence, not merely equality of dimensions. -/
def Equivalent (π τ : FiniteUnitaryRep.{u,v} Γ) : Prop :=
  ∃ T : π ≃ₗᵢ[ℂ] τ, ∀ g x, T (π.action g x) = τ.action g (T x)

@[refl] theorem embeds_refl (π : FiniteUnitaryRep.{u,v} Γ) : π.Embeds π :=
  ⟨LinearIsometry.id, fun _ _ => rfl⟩

@[refl] theorem equivalent_refl (π : FiniteUnitaryRep.{u,v} Γ) : π.Equivalent π :=
  ⟨LinearIsometryEquiv.refl ℂ π, fun _ _ => rfl⟩

@[trans] theorem Embeds.trans {π τ ρ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Embeds τ) (k : τ.Embeds ρ) : π.Embeds ρ := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨U, hU⟩ := k
  exact ⟨U.comp T, fun g x => by change U (T (π.action g x)) = _; rw [hT, hU]; rfl⟩

@[symm] theorem Equivalent.symm {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Equivalent τ) : τ.Equivalent π := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun g x => ?_⟩
  apply T.injective
  simp only [T.apply_symm_apply, hT]

@[trans] theorem Equivalent.trans {π τ ρ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Equivalent τ) (k : τ.Equivalent ρ) : π.Equivalent ρ := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨U, hU⟩ := k
  exact ⟨T.trans U, fun g x => by change U (T (π.action g x)) = _; rw [hT, hU]; rfl⟩

/-- Restriction to an invariant subspace, with the inherited Hilbert norm. -/
def restrict (π : FiniteUnitaryRep.{u,v} Γ) (W : Submodule ℂ π)
    (hW : ∀ g x, x ∈ W → π.action g x ∈ W) [Nontrivial W] : FiniteUnitaryRep.{u,v} Γ where
  carrier := W
  action := {
    toFun g := {
      toFun x := ⟨π.action g x, hW g x x.property⟩
      invFun x := ⟨π.action g⁻¹ x, hW g⁻¹ x x.property⟩
      left_inv x := by ext; change (π.action g⁻¹ * π.action g) x.val = x.val; rw [← map_mul]; simp
      right_inv x := by ext; change (π.action g * π.action g⁻¹) x.val = x.val; rw [← map_mul]; simp
      map_add' x y := by ext; simp
      map_smul' c x := by ext; simp
      norm_map' x := (π.action g).norm_map x }
    map_one' := by ext; simp
    map_mul' g h := by ext; simp [map_mul] }

end FiniteUnitaryRep
end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertSchmidt
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
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

namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev HilbertTensor (E K : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  UniformSpace.Completion (E ⊗[ℂ] K)

end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FiniteInduction
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
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

instance lp_finiteDimensional {ι V : Type u} [Finite ι]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] :
    FiniteDimensional ℂ (lp (fun _ : ι => V) 2) := by
  let := Fintype.ofFinite ι
  let f : lp (fun _ : ι => V) 2 →ₗ[ℂ] (ι → V) := {
    toFun x := x
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  exact FiniteDimensional.of_injective f (fun _ _ h => lp.ext h)

end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertUltraproduct
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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

/-- A type synonym for bounded Hilbert families, equipped below with the
ultralimit semi-inner-product (not with the supremum norm). -/
def UltraPreHilbert {ι : Type u} (E : ι → Type v)
    [∀ i, NormedAddCommGroup (E i)] (_ω : Ultrafilter ι) := lp E ∞

namespace UltraPreHilbert
variable {ι : Type u} {E : ι → Type v} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (ω : Ultrafilter ι)

instance instAddCommGroupSubtypePreLpMemAddSubgroup : AddCommGroup (UltraPreHilbert E ω) := inferInstanceAs (AddCommGroup (lp E ∞))
instance instModuleComplexSubtypePreLpMemAddSubgroup : Module ℂ (UltraPreHilbert E ω) := inferInstanceAs (Module ℂ (lp E ∞))

def family (x : UltraPreHilbert E ω) : lp E ∞ := x

omit [∀ i, InnerProductSpace ℂ (E i)] in
@[simp] theorem family_add (x y : UltraPreHilbert E ω) :
    family ω (x + y) = family ω x + family ω y := rfl
@[simp] theorem family_smul (r : ℂ) (x : UltraPreHilbert E ω) :
    family ω (r • x) = r • family ω x := rfl

end UltraPreHilbert

end NuclearUltrapower

namespace NuclearUltrapower
namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] (ω : Ultrafilter ι)

local instance instIsBoundedSMulComplexContinuousLinearMapId (i : ι) : IsBoundedSMul ℂ (E i →L[ℂ] E i) :=
  NormedSpace.toIsBoundedSMul

end HilbertUltraproduct
end NuclearUltrapower
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
def gramRow0 : List ℤ := [276726576341, -7158468946, -7158700808, 67943, 143683124409, 48398339509, -2112432855, -22603795307, -10173711233, -49221359593, -22603577948, -49221110918, 48397911061, -584106529928, 48397862720, -49220953326, -22603365175, -49221038044, -33595105247, -22603525174, -2112613445, 48397998398, -31146853137, -178089, -10370617592, 44817326883, -15710113406, -2112231710, 3525718952, -14631458507, -17927153224, 31388205025, -4715328105, 32770695042, -23154518737, 10370155384, 9509214253, 10370342674, -352634, -10370827745, 512550, -10370193209, 709723, 10370168783, 9509008655, 10370007391, -17926436965, -17926364819, -26688393082, 9509214227, -21997317929, 4934586101, -7158611935, 27131515001, -26688594389, 31388107505, 4935046968, 44817061578, -31146179104, 3524588985, 150554815730, 3525935281, -31146228448, 44816894413, 4934976534, 31387642853, -26688483839, 27131622053, -7158804393, 4933924037, -21996906631, 9509409248, -26688321670, -15709902083, -15709632313, 27131623222, -25072393716, 32771182256, -25072470360, -4715360261, -949092746, -4714913936, -25072279549, 32770570539, -25072429447, 27131475938, 6071507041, -10370551994, 46684, 31387946196, -17926531666, -14630766981, 3525950778, -2112708456, -15710126276, 44817029971, 32770776612, -4715113722, -31146478055, -618157, -14631282756, 46809448375, 46309104079, -31610400766, -31610781402, -74272, 46809143273, -43294372576, 46808982670, -73582, -31610613879, -31610993013, 2087038159, 46808742562, -14631002075, 174217, -2161, 155082088249, -21997008296, -21997216354, -168935]
def gramRow10 : List ℤ := [-22603577948, 43944, 32770103282, 25056, 63524004605, -85285970334, -274233670998, -131447720424, 25072476887, 88272635484, 1051569680070, -697491657564, -14422396783, -730548627144, 415694283817, -8834273177, 201509446044, 82297086446, -4715113722, -131447533472, 32890023454, 142096493962, -46808845991, 7158886948, -19018179523, 14629986771, 17441778309, 148126496168, 116807618307, 138873432466, -31610609278, 21455649761, 192624, 21997017023, 31610866237, 8963553384, -236760, 107268427024, -33643920211, 239083127070, -108388601406, 53377654995, -274233246999, -11173430595, -32116830271, 15710453474, 9509284520, 27131881402, 241665, 88271975521, 45193479243, -19342937200, -14630772792, 285120, -63397163183, -558271247132, 294949752009, -122785517483, 13531322291, 228339404838, 72487011808, 58534375314, 11532892405, -158052403957, 116952299417, -70033628797, -30993, 82297085470, -2112533370, -76122031376, -41067966955, -118510, -685845, -7383, -134393, -32115662885, 18635, 32890470880, -32955387096, -44544144096, 149058972336, -44544556678, -708878, 2337795286, 112913, -305678, 148347, -54262774563, 21997760549, 30929167571, -49221190728, -67770476975, -215534093777, -67770842645, 176313, 41068499178, -7107551656, -179190, 14427374143, -232691, -33643531262, 31145966223, -10370749234, 246189, -8833889531, -25581650861, -67878311274, 133201156762, 18311547668, 851483, -544792, 766783, -167327, 49321445818, 2337344481, -1113552, 237987, -75213161605, -32770215665, -77449, 347877]
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

abbrev SL := Matrix.SpecialLinearGroup (Fin 3) ℤ

end NuclearUltrapower.SOS

end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Kazhdan
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary

/-- The stable letter t=(0,I,1). -/
def stableLetter : G :=
  SemidirectProduct.inr (1, Multiplicative.ofAdd (1 : ℤ))

abbrev Residue3 := Fin 3 → ZMod 2

end NuclearUltrapower.Elementary
end
end

section

noncomputable section
namespace NuclearUltrapower.Displacement
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (ρ : Γ →* (H ≃ₗᵢ[ℂ] H))

def dist (g : Γ) (x : H) : ℝ := ‖ρ g x - x‖

end NuclearUltrapower.Displacement
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_VariableUltraproduct
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.instStarRingNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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
namespace NuclearUltrapower

/-- A bounded scalar family has a genuine ultralimit. -/
theorem tendsto_ultralimit_of_bounded {ι : Type u} (ω : Ultrafilter ι)
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

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)

abbrev Seq := lp A ∞
instance instCStarAlgebraSubtypePreLpMemAddSubgroupSeq : CStarAlgebra (Seq A) where

/-- Equality modulo norm-null sequences, with unrestricted varying dimensions. -/
def Rel (x y : Seq A) : Prop :=
  Tendsto (fun i => ‖x i - y i‖) (ω : Filter ι) (𝓝 0)

omit [∀ i, Nontrivial (A i)] in
theorem null_add {x y : Seq A}
    (hx : Tendsto (fun i => ‖x i‖) (ω : Filter ι) (𝓝 0))
    (hy : Tendsto (fun i => ‖y i‖) (ω : Filter ι) (𝓝 0)) :
    Tendsto (fun i => ‖(x+y) i‖) (ω : Filter ι) (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => norm_add_le (x i) (y i))
  simpa using hx.add hy

omit [∀ i, Nontrivial (A i)] in
theorem null_mul_left {x : Seq A}
    (hx : Tendsto (fun i => ‖x i‖) (ω : Filter ι) (𝓝 0)) (y : Seq A) :
    Tendsto (fun i => ‖(x*y) i‖) (ω : Filter ι) (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun i => (norm_mul_le (x i) (y i)).trans
      (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero y i) (norm_nonneg _)))
  simpa using hx.mul_const ‖y‖

omit [∀ i, Nontrivial (A i)] in
theorem null_mul_right (x : Seq A) {y : Seq A}
    (hy : Tendsto (fun i => ‖y i‖) (ω : Filter ι) (𝓝 0)) :
    Tendsto (fun i => ‖(x*y) i‖) (ω : Filter ι) (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun i => (norm_mul_le (x i) (y i)).trans
      (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero x i) (norm_nonneg _)))
  simpa using hy.const_mul ‖x‖

def con : RingCon (Seq A) where
  r := Rel A ω
  iseqv := {
    refl := fun x => by simp [Rel]
    symm := fun {x y} h => by simpa only [Rel, norm_sub_rev] using h
    trans := fun {x y z} hxy hyz => by
      have h := null_add A ω (x := x-y) (y := y-z) hxy hyz
      simpa only [Rel, sub_add_sub_cancel, lp.coeFn_sub, Pi.sub_apply] using h }
  add' := by
    intro x y z t hxy hzt
    have h := null_add A ω (x := x-y) (y := z-t) hxy hzt
    change Tendsto (fun i => ‖(x+z-(y+t)) i‖) (ω : Filter ι) (𝓝 0)
    have he : x+z-(y+t) = (x-y)+(z-t) := by abel
    rw [he]
    exact h
  mul' := by
    intro x y z t hxy hzt
    have h := null_add A ω (null_mul_left A ω (x := x-y) hxy z)
      (null_mul_right A ω y (y := z-t) hzt)
    simpa only [Rel, sub_mul, mul_sub, sub_add_sub_cancel, lp.coeFn_sub, Pi.sub_apply] using h

abbrev Algebra := (con A ω).Quotient

omit [∀ i, Nontrivial (A i)] in
theorem rel_star {x y : Seq A} (h : Rel A ω x y) :
    Rel A ω (star x) (star y) := by
  simpa only [Rel, lp.coeFn_star, Pi.star_apply, ← star_sub, norm_star] using h

instance instStarAlgebra : Star (Algebra A ω) where
  star := Quotient.map' star (fun _ _ h => rel_star A ω h)
instance instStarRingAlgebra : StarRing (Algebra A ω) where
  star_involutive x := by
    induction x using Quotient.inductionOn with | h x =>
      exact congrArg Quotient.mk'' (star_star x)
  star_mul x y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg Quotient.mk'' (star_mul x y)
  star_add x y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg Quotient.mk'' (star_add x y)
instance instStarModuleComplexAlgebra : StarModule ℂ (Algebra A ω) where
  star_smul c x := by
    induction x using Quotient.inductionOn with | h x =>
      exact congrArg Quotient.mk'' (star_smul c x)

def mk : Seq A →⋆ₐ[ℂ] Algebra A ω where
  __ := (con A ω).mkₐ ℂ
  map_star' _ := rfl

def seqNorm (x : Seq A) : ℝ := limUnder (ω : Filter ι) (fun i => ‖x i‖)

omit [∀ i, Nontrivial (A i)] in
theorem seqNorm_tendsto (x : Seq A) :
    Tendsto (fun i => ‖x i‖) (ω : Filter ι) (𝓝 (seqNorm A ω x)) :=
  tendsto_ultralimit_of_bounded ω _ ⟨‖x‖, fun i => by
    simpa only [Real.norm_eq_abs, abs_norm] using lp.norm_apply_le_norm ENNReal.top_ne_zero x i⟩

omit [∀ i, Nontrivial (A i)] in
theorem seqNorm_nonneg (x : Seq A) : 0 ≤ seqNorm A ω x :=
  ge_of_tendsto (seqNorm_tendsto A ω x) (Filter.Eventually.of_forall fun _ => norm_nonneg _)

omit [∀ i, Nontrivial (A i)] in
theorem seqNorm_le (x : Seq A) : seqNorm A ω x ≤ ‖x‖ :=
  le_of_tendsto (seqNorm_tendsto A ω x)
    (Filter.Eventually.of_forall (lp.norm_apply_le_norm ENNReal.top_ne_zero x))

theorem seqNorm_lipschitz : LipschitzWith 1 (seqNorm A ω) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply le_of_tendsto (((seqNorm_tendsto A ω x).sub (seqNorm_tendsto A ω y)).abs)
  exact Filter.Eventually.of_forall (fun i =>
    (abs_norm_sub_norm_le (x i) (y i)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero (x-y) i))

def null : Submodule ℂ (Seq A) where
  carrier := {x | Tendsto (fun i => ‖x i‖) (ω : Filter ι) (𝓝 0)}
  zero_mem' := by simp
  add_mem' := null_add A ω
  smul_mem' c x hx := by
    change Tendsto (fun i => ‖(c • x) i‖) (ω : Filter ι) (𝓝 0)
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, mul_zero] using hx.const_mul ‖c‖

theorem mem_null_iff (x : Seq A) : x ∈ null A ω ↔ seqNorm A ω x = 0 := by
  constructor
  · intro hx
    exact tendsto_nhds_unique (seqNorm_tendsto A ω x) hx
  · intro hx
    change Tendsto (fun i => ‖x i‖) (ω : Filter ι) (𝓝 0)
    simpa only [hx] using seqNorm_tendsto A ω x

instance null_closed : IsClosed ((null A ω : Submodule ℂ (Seq A)) : Set (Seq A)) := by
  have he : (null A ω : Set (Seq A)) = (seqNorm A ω) ⁻¹' {0} := by
    ext x
    exact mem_null_iff A ω x
  rw [he]
  exact isClosed_singleton.preimage (seqNorm_lipschitz A ω).continuous

/-- Identification with the ordinary complete normed linear quotient. -/
def quotientEquiv : Algebra A ω ≃ₗ[ℂ] (Seq A ⧸ null A ω) :=
  LinearEquiv.ofBijective
    (show Algebra A ω →ₗ[ℂ] (Seq A ⧸ null A ω) from
    { toFun := Quotient.lift (fun x : Seq A => (Submodule.Quotient.mk x : Seq A ⧸ null A ω))
        (by intro x y h; exact (Submodule.Quotient.eq _).mpr h)
      map_add' := by
        intro x y
        induction x using Quotient.inductionOn with | h x =>
          induction y using Quotient.inductionOn with | h y => rfl
      map_smul' := by
        intro c x
        induction x using Quotient.inductionOn with | h x => rfl })
    ⟨by
      intro x y h
      induction x using Quotient.inductionOn with | h x =>
        induction y using Quotient.inductionOn with | h y =>
          exact Quotient.sound ((Submodule.Quotient.eq _).mp h),
     by
      intro x
      obtain ⟨y, rfl⟩ := Quotient.exists_rep x
      exact ⟨mk A ω y, rfl⟩⟩

instance instNormedAddCommGroupAlgebra : NormedAddCommGroup (Algebra A ω) :=
  NormedAddCommGroup.induced _ _ (quotientEquiv A ω).toAddEquiv (quotientEquiv A ω).injective

@[simp] theorem norm_eq_quotient_norm (x : Algebra A ω) :
    ‖x‖ = ‖quotientEquiv A ω x‖ := rfl

omit [∀ i, Nontrivial (A i)] in
theorem seqNorm_eq_of_rel {x y : Seq A} (h : Rel A ω x y) :
    seqNorm A ω x = seqNorm A ω y := by
  have hd : Tendsto (fun i => ‖x i‖ - ‖y i‖) (ω : Filter ι) (𝓝 0) :=
    squeeze_zero_norm (fun i => (by simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (x i) (y i))) h
  exact sub_eq_zero.mp (tendsto_nhds_unique
    ((seqNorm_tendsto A ω x).sub (seqNorm_tendsto A ω y)) hd)

/-- Exact quotient norm, including the truncation upper bound. -/
theorem mk_norm (x : Seq A) : ‖mk A ω x‖ = seqNorm A ω x := by
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    have hr0 : 0 ≤ r := (seqNorm_nonneg A ω x).trans hr.le
    let y : Seq A := ⟨fun i => if ‖x i‖ < r then x i else 0, memℓp_infty ⟨r, by
      rintro _ ⟨i, rfl⟩
      by_cases hi : ‖x i‖ < r
      · simp [hi, hi.le]
      · simp [hi, hr0]⟩⟩
    have he : mk A ω x = mk A ω y := by
      apply Quotient.sound
      have hv : ∀ᶠ i in (ω : Filter ι), ‖x i - y i‖ = 0 := by
        filter_upwards [(seqNorm_tendsto A ω x).eventually (gt_mem_nhds hr)] with i hi
        simp [y, hi]
      exact tendsto_const_nhds.congr' (hv.mono fun _ h => h.symm)
    rw [he, norm_eq_quotient_norm]
    apply (Submodule.Quotient.norm_mk_le (null A ω) y).trans
    apply lp.norm_le_of_forall_le hr0
    intro i
    change ‖(if ‖x i‖ < r then x i else 0 : A i)‖ ≤ r
    by_cases hi : ‖x i‖ < r
    · simp [hi, hi.le]
    · simp [hi, hr0]
  · change seqNorm A ω x ≤ ‖(Submodule.Quotient.mk x : Seq A ⧸ null A ω)‖
    apply QuotientAddGroup.le_norm_iff.mpr
    intro y hy
    have hr : Rel A ω y x := (Submodule.Quotient.eq _).mp hy
    rw [← seqNorm_eq_of_rel A ω hr]
    exact seqNorm_le A ω y

instance instNormedRingAlgebra : NormedRing (Algebra A ω) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        change ‖mk A ω (x*y)‖ ≤ ‖mk A ω x‖ * ‖mk A ω y‖
        simp only [mk_norm]
        exact le_of_tendsto_of_tendsto (seqNorm_tendsto A ω (x*y))
          ((seqNorm_tendsto A ω x).mul (seqNorm_tendsto A ω y))
          (Filter.Eventually.of_forall fun i => norm_mul_le (x i) (y i))
instance instNormedAlgebraComplexAlgebra : NormedAlgebra ℂ (Algebra A ω) where
  norm_smul_le c x := by
    induction x using Quotient.inductionOn with | h x =>
      change ‖mk A ω (c • x)‖ ≤ ‖c‖ * ‖mk A ω x‖
      simp only [mk_norm]
      exact le_of_tendsto_of_tendsto (seqNorm_tendsto A ω (c • x))
        (tendsto_const_nhds.mul (seqNorm_tendsto A ω x))
        (Filter.Eventually.of_forall fun i => norm_smul_le c (x i))
instance instCStarRingAlgebra : CStarRing (Algebra A ω) where
  norm_mul_self_le x := by
    induction x using Quotient.inductionOn with | h x =>
      change ‖mk A ω x‖ * ‖mk A ω x‖ ≤ ‖mk A ω (star x * x)‖
      simp only [mk_norm]
      exact le_of_tendsto_of_tendsto
        ((seqNorm_tendsto A ω x).mul (seqNorm_tendsto A ω x))
        (seqNorm_tendsto A ω (star x * x))
        (Filter.Eventually.of_forall fun i => (CStarRing.norm_star_mul_self (x := x i)).ge)

def quotientIsometry : Algebra A ω ≃ₗᵢ[ℂ] (Seq A ⧸ null A ω) where
  __ := quotientEquiv A ω
  norm_map' _ := rfl
instance instCompleteSpaceAlgebra : CompleteSpace (Algebra A ω) :=
  (quotientIsometry A ω).toIsometryEquiv.completeSpace_iff.mpr inferInstance
instance instCStarAlgebraAlgebra : CStarAlgebra (Algebra A ω) where

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower
namespace VariableUltra
open scoped WithCStarModule

/-- A dimension-controlled bound for the C*-matrix norm, independent of the
entry algebra. This also proves continuity for bounded varying-algebra families. -/
theorem matrix_norm_le_sum {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n]
    (M : CStarMatrix n n A) : ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  classical
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum, Finset.sum_mul]
  apply WithCStarModule.pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact WithCStarModule.norm_apply_le_norm v j

variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)
variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]

local instance entryOrder (i : ι) : PartialOrder (A i) := CStarAlgebra.spectralOrder _
local instance entryStarOrder (i : ι) : StarOrderedRing (A i) := CStarAlgebra.spectralOrderedRing _

local instance quotientOrder_r3bfbef_1 : PartialOrder (Algebra A ω) := CStarAlgebra.spectralOrder _
local instance quotientStarOrder_r3bfbef_1 : StarOrderedRing (Algebra A ω) := CStarAlgebra.spectralOrderedRing _
/-- One entry of a bounded family of matrices is a bounded family. -/
def matrixEntry (M : Seq (fun i => CStarMatrix n n (A i))) (j k : n) : Seq A :=
  ⟨fun i => M i j k, memℓp_infty ⟨‖M‖, by
    rintro _ ⟨i, rfl⟩
    exact CStarMatrix.norm_entry_le_norm.trans (lp.norm_apply_le_norm ENNReal.top_ne_zero M i)⟩⟩

omit [∀ i, Nontrivial (A i)] [Nonempty n] in
@[simp] theorem matrixEntry_apply (M : Seq (fun i => CStarMatrix n n (A i))) (j k : n) (i : ι) :
    matrixEntry A n M j k i = M i j k := rfl

/-- Assemble a finite matrix of bounded families. There is no bound on the
dimension of any of the entry algebras. -/
def matrixFamily (M : CStarMatrix n n (Seq A)) : Seq (fun i => CStarMatrix n n (A i)) :=
  ⟨fun i => CStarMatrix.ofMatrix (fun j k => M j k i), memℓp_infty
    ⟨∑ k, ∑ j, ‖M j k‖, by
      rintro _ ⟨i, rfl⟩
      apply (matrix_norm_le_sum _).trans
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro j _
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (M j k) i⟩⟩

omit [∀ i, Nontrivial (A i)] [Nonempty n] in
@[simp] theorem matrixFamily_apply (M : CStarMatrix n n (Seq A)) (i : ι) (j k : n) :
    matrixFamily A n M i j k = M j k i := rfl

/-- Pass to the ultraproduct in every matrix entry. -/
def matrixQuotient : Algebra (fun i => CStarMatrix n n (A i)) ω →⋆ₐ[ℂ]
    CStarMatrix n n (Algebra A ω) where
  toFun := Quotient.lift
    (fun M => CStarMatrix.ofMatrix (fun j k => mk A ω (matrixEntry A n M j k)))
    (by
      intro M N h
      apply CStarMatrix.ext
      intro j k
      apply Quotient.sound
      apply squeeze_zero (fun _ => norm_nonneg _)
        (fun i => CStarMatrix.norm_entry_le_norm (M := M i - N i) (i := j) (j := k))
      exact h)
  map_zero' := by
    apply CStarMatrix.ext
    intro j k
    change mk A ω 0 = 0
    exact map_zero _
  map_one' := by
    apply CStarMatrix.ext
    intro j k
    change mk A ω (matrixEntry A n 1 j k) = (1 : CStarMatrix n n (Algebra A ω)) j k
    have he : matrixEntry A n 1 j k = if j = k then 1 else 0 := by
      ext i
      by_cases h : j = k <;> simp [matrixEntry, h]
    rw [he, CStarMatrix.one_apply]
    split <;> simp
  map_add' := by
    intro M N
    induction M using Quotient.inductionOn with | h M =>
      induction N using Quotient.inductionOn with | h N =>
        apply CStarMatrix.ext
        intro j k
        change mk A ω (matrixEntry A n (M+N) j k) =
          mk A ω (matrixEntry A n M j k) + mk A ω (matrixEntry A n N j k)
        have he : matrixEntry A n (M+N) j k = matrixEntry A n M j k + matrixEntry A n N j k := rfl
        rw [he, map_add]
  map_mul' := by
    intro M N
    induction M using Quotient.inductionOn with | h M =>
      induction N using Quotient.inductionOn with | h N =>
        apply CStarMatrix.ext
        intro j k
        change mk A ω (matrixEntry A n (M*N) j k) = ∑ l, _
        have he : matrixEntry A n (M*N) j k =
            ∑ l, matrixEntry A n M j l * matrixEntry A n N l k := by
          ext i
          change (M i * N i) j k = _
          rw [CStarMatrix.mul_apply]
          change (∑ l, M i j l * N i l k) =
            (∑ l, matrixEntry A n M j l * matrixEntry A n N l k) i
          rw [lp.coeFn_sum]
          change (∑ l, M i j l * N i l k) =
            (∑ l, (fun i : ι => M i j l * N i l k)) i
          rw [Finset.sum_apply]
        rw [he, map_sum]
        simp only [map_mul]
        rfl
  commutes' c := by
    apply CStarMatrix.ext
    intro j k
    change mk A ω (matrixEntry A n (algebraMap ℂ (Seq (fun i => CStarMatrix n n (A i))) c) j k) = _
    have he : matrixEntry A n (algebraMap ℂ (Seq (fun i => CStarMatrix n n (A i))) c) j k =
        if j = k then algebraMap ℂ (Seq A) c else 0 := by
      ext i
      by_cases h : j = k
      · subst k
        simp only
        change (algebraMap ℂ (CStarMatrix n n (A i)) c) j j = algebraMap ℂ (A i) c
        simp [CStarMatrix.algebraMap_apply]
      · simp only [ite_eq_right h]
        change (algebraMap ℂ (CStarMatrix n n (A i)) c) j k = 0
        simp [CStarMatrix.algebraMap_apply, h]
    rw [he, CStarMatrix.algebraMap_apply]
    split
    · exact (mk A ω).commutes c
    · exact map_zero _
  map_star' := by
    intro M
    induction M using Quotient.inductionOn with | h M =>
      apply CStarMatrix.ext
      intro j k
      change mk A ω (star (matrixEntry A n M k j)) = star (mk A ω (matrixEntry A n M k j))
      exact map_star _ _

@[simp] theorem matrixQuotient_mk (M : Seq (fun i => CStarMatrix n n (A i))) (j k : n) :
    matrixQuotient A ω n (mk _ ω M) j k = mk A ω (matrixEntry A n M j k) := rfl

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower

/-- Entrywise amplification of a unital star homomorphism. -/
def matrixMap {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (n : Type*) [Fintype n] [DecidableEq n] (f : A →⋆ₐ[ℂ] B) :
    CStarMatrix n n A →⋆ₐ[ℂ] CStarMatrix n n B where
  toFun := CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := map_mul _
  map_star' := map_star _
  map_one' := by
    ext i j
    change f ((1 : CStarMatrix n n A) i j) = (1 : CStarMatrix n n B) i j
    simp only [CStarMatrix.one_apply]
    split <;> simp
  commutes' c := by
    ext i j
    change f ((algebraMap ℂ (CStarMatrix n n A) c) i j) =
      (algebraMap ℂ (CStarMatrix n n B) c) i j
    simp only [CStarMatrix.algebraMap_apply]
    split
    · exact f.commutes c
    · exact map_zero _

@[simp] theorem matrixMap_apply {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {n : Type*} [Fintype n] [DecidableEq n] (f : A →⋆ₐ[ℂ] B)
    (M : CStarMatrix n n A) (i j : n) : matrixMap n f M i j = f (M i j) := rfl

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)
variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]

local instance normEntryOrder_r3bfbef_1 (i : ι) : PartialOrder (A i) := CStarAlgebra.spectralOrder _
local instance normEntryStarOrder_r3bfbef_1 (i : ι) : StarOrderedRing (A i) := CStarAlgebra.spectralOrderedRing _
local instance seqOrder_r3bfbef_1 : PartialOrder (Seq A) := CStarAlgebra.spectralOrder _
local instance seqStarOrder_r3bfbef_1 : StarOrderedRing (Seq A) := CStarAlgebra.spectralOrderedRing _
local instance normQuotientOrder_r3bfbef_1 : PartialOrder (Algebra A ω) := CStarAlgebra.spectralOrder _
local instance normQuotientStarOrder_r3bfbef_1 : StarOrderedRing (Algebra A ω) := CStarAlgebra.spectralOrderedRing _
@[simp] theorem matrixQuotient_matrixFamily (M : CStarMatrix n n (Seq A)) :
    matrixQuotient A ω n (mk _ ω (matrixFamily A n M)) = matrixMap n (mk A ω) M := by
  apply CStarMatrix.ext
  intro j k
  rfl

end VariableUltra
end NuclearUltrapower

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorGap
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.instStarRingNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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

section MatrixAction
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual left action of an operator-valued matrix on a Hilbert direct sum. -/
def operatorMatrixAction (M : CStarMatrix n n (H →L[ℂ] H)) :
    PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H) where
  toFun x := WithLp.toLp 2 (fun i => ∑ j, M i j (x j))
  map_add' x y := by ext i; simp [map_add, Finset.sum_add_distrib]
  map_smul' c x := by ext i; simp [map_smul, Finset.smul_sum]
  cont := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    exact continuous_finsetSum _ (fun j _ => (M i j).continuous.comp (PiLp.proj (𝕜 := ℂ) 2 (fun _ : n => H) j).continuous)

omit [DecidableEq n] [CompleteSpace H] in
@[simp] theorem operatorMatrixAction_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : n => H)) (i : n) : operatorMatrixAction M x i = ∑ j, M i j (x j) := rfl

/-- Matrix amplification is a genuine unital star homomorphism. -/
def operatorMatrixActionHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₐ[ℂ]
    (PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H)) where
  toFun := operatorMatrixAction
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp [CStarMatrix.one_apply, apply_ite, ite_apply]
  map_add' M N := by ext x i; simp [CStarMatrix.add_apply, Finset.sum_add_distrib]
  map_mul' M N := by
    ext x i
    simp only [operatorMatrixAction_apply, CStarMatrix.mul_apply, sum_apply,
      mul_apply_eq_comp, map_sum]
    rw [Finset.sum_comm]
  commutes' c := by
    ext x i
    simp [CStarMatrix.algebraMap_apply, apply_ite, ite_apply]
  map_star' M := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [PiLp.inner_apply, operatorMatrixAction_apply, CStarMatrix.star_apply,
      sum_inner, inner_sum]
    change (∑ i, ∑ j, inner ℂ ((M j i).adjoint (x j)) (y i)) = _
    simp only [ContinuousLinearMap.adjoint_inner_left]
    rw [Finset.sum_comm]

@[simp] theorem operatorMatrixActionHom_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : n => H)) (i : n) : operatorMatrixActionHom (n := n) (H := H) M x i = ∑ j, M i j (x j) := rfl

end MatrixAction

open scoped TensorProduct
section TensorMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- This matrix has scalar coefficients in the fixed factor; the first factor
may be infinite-dimensional. -/
def tensorOperatorMatrix (b : OrthonormalBasis n ℂ F)
    (U : E →L[ℂ] E) (V : F →L[ℂ] F) : CStarMatrix n n (E →L[ℂ] E) :=
  CStarMatrix.ofMatrix (fun i j => b.repr (V (b j)) i • U)

omit [DecidableEq n] in
@[simp] theorem tensorOperatorMatrix_apply (b : OrthonormalBasis n ℂ F)
    (U : E →L[ℂ] E) (V : F →L[ℂ] F) (i j : n) :
    tensorOperatorMatrix b U V i j = b.repr (V (b j)) i • U := rfl

end TensorMatrix
end NuclearUltrapower

namespace NuclearUltrapower

section CoefficientMatrix
variable {A B Γ n : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [Fintype n] [DecidableEq n]

/-- An elementary tensor in coordinates of the fixed second factor. -/
def coefficientMatrix (c : n → n → ℂ) (a : A) : CStarMatrix n n A :=
  CStarMatrix.ofMatrix (fun j k => c j k • a)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem coefficientMatrix_apply (c : n → n → ℂ) (a : A) (j k : n) :
    coefficientMatrix c a j k = c j k • a := rfl

@[simp] theorem matrixMap_coefficientMatrix (φ : A →⋆ₐ[ℂ] B) (c : n → n → ℂ) (a : A) :
    matrixMap n φ (coefficientMatrix c a) = coefficientMatrix c (φ a) := by
  ext j k
  exact map_smul φ _ _

end CoefficientMatrix

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)

/-- Evaluation is an actual unital star homomorphism. -/
def eval (i : ι) : Seq A →⋆ₐ[ℂ] A i where
  toFun x := x i
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  commutes' _ := rfl

@[simp] theorem eval_apply (i : ι) (x : Seq A) : eval A i x = x i := rfl

/-- Arbitrary coordinate unitaries are bounded, without a dimension bound. -/
def unitarySequence (u : ∀ i, unitary (A i)) : unitary (Seq A) :=
  ⟨⟨fun i => (u i : A i), memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩
    exact (CStarRing.norm_coe_unitary (u i)).le⟩⟩, by
    constructor <;> ext i
    · exact Unitary.coe_star_mul_self (u i)
    · exact Unitary.coe_mul_star_self (u i)⟩

@[simp] theorem unitarySequence_apply (u : ∀ i, unitary (A i)) (i : ι) :
    (unitarySequence A u : Seq A) i = u i := rfl

variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]

local instance gapEntryOrder_r3bfbef_1 (i : ι) : PartialOrder (A i) := CStarAlgebra.spectralOrder _
local instance gapEntryStarOrder_r3bfbef_1 (i : ι) : StarOrderedRing (A i) := CStarAlgebra.spectralOrderedRing _
local instance gapSeqOrder_r3bfbef_1 : PartialOrder (Seq A) := CStarAlgebra.spectralOrder _
local instance gapSeqStarOrder_r3bfbef_1 : StarOrderedRing (Seq A) := CStarAlgebra.spectralOrderedRing _
local instance gapQuotientOrder_r3bfbef_1 : PartialOrder (Algebra A ω) := CStarAlgebra.spectralOrder _
local instance gapQuotientStarOrder_r3bfbef_1 : StarOrderedRing (Algebra A ω) := CStarAlgebra.spectralOrderedRing _
omit [Nonempty n] in
@[simp] theorem matrixFamily_eval (M : CStarMatrix n n (Seq A)) (i : ι) :
    matrixFamily A n M i = matrixMap n (eval A i) M := rfl

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct

namespace VariableUltra
variable {ι : Type u} (E : ι → Type v)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)] (ω : Ultrafilter ι)

abbrev operatorSeq := Seq (fun i => E i →L[ℂ] E i)
abbrev operatorQuotient := Algebra (fun i => E i →L[ℂ] E i) ω

def isoSequence (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) : unitary (operatorSeq E) :=
  unitarySequence _ (fun i => Unitary.linearIsometryEquiv.symm (U i))

def starAlgToStarMonoid {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) : A →⋆* B where
  toFun := φ
  map_one' := map_one φ
  map_mul' := map_mul φ
  map_star' := map_star φ

def quotientIsoUnitary (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) : unitary (operatorQuotient E ω) :=
  Unitary.map (starAlgToStarMonoid (mk (fun i => E i →L[ℂ] E i) ω)) (isoSequence E U)

variable {K F : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def representedIso (φ : operatorQuotient E ω →⋆ₐ[ℂ] (K →L[ℂ] K))
    (U : ∀ i, E i ≃ₗᵢ[ℂ] E i) : K ≃ₗᵢ[ℂ] K :=
  Unitary.linearIsometryEquiv (Unitary.map (starAlgToStarMonoid φ) (quotientIsoUnitary E ω U))

end VariableUltra
end NuclearUltrapower

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorNorms
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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
namespace NuclearUltrapower

section NormTransfer

variable {B : Type u} {C : Type v} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

local instance spatialTensorBoundedSMul_r3bfbef_1 (H K : ComplexHilbert.{w}) :
    IsBoundedSMul ℂ (H ⊗[ℂ] K) := NormedSpace.toIsBoundedSMul
@[simp] theorem spatialEval_tmul (H K : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (b : B) (c : C) :
    spatialEval H K ρ σ (b ⊗ₜ[ℂ] c) = TensorProduct.mapL (ρ b) (σ c) := rfl

@[simp] theorem commutingEval_tmul (H : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (b : B) (c : C) :
    commutingEval H ρ σ (b ⊗ₜ[ℂ] c) = ρ b * σ c := rfl

end NormTransfer
end NuclearUltrapower

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower

section Support
variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The nondegenerate support of a possibly nonunital representation. -/
def representationSupport (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Submodule ℂ H :=
  (φ 1 - 1).ker

@[simp] theorem mem_representationSupport (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) :
    x ∈ representationSupport φ ↔ φ 1 x = x := by
  simp [representationSupport, sub_eq_zero]

instance supportComplete (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    CompleteSpace (representationSupport φ) :=
  (φ 1 - 1).isClosed_ker.completeSpace_coe

/-- Projection to the support, without invoking separability or nonzero spaces. -/
def supportProjection (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    H →L[ℂ] representationSupport φ :=
  (φ 1).codRestrict _ (fun x => by
    rw [mem_representationSupport]
    change (φ 1 * φ 1) x = φ 1 x
    rw [← map_mul, one_mul])

@[simp] theorem supportProjection_coe (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) :
    (supportProjection φ x : H) = φ 1 x := rfl

@[simp] theorem supportProjection_subtype (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (x : representationSupport φ) : supportProjection φ x = x := by
  ext
  exact (mem_representationSupport φ x).mp x.property

/-- A possibly degenerate representation becomes unital on its actual support. -/
def supportRepresentation (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₐ[ℂ] (representationSupport φ →L[ℂ] representationSupport φ) where
  toFun a := (φ a).restrict (fun x _ => by
    rw [mem_representationSupport]
    change (φ 1 * φ a) x = φ a x
    rw [← map_mul, one_mul])
  map_zero' := by ext x; simp
  map_one' := by
    ext x
    exact (mem_representationSupport φ x).mp x.property
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one,
    (mem_representationSupport φ x).mp x.property]
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    change inner ℂ (φ (star a) (x : H)) (y : H) = inner ℂ (x : H) (φ a (y : H))
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]

@[simp] theorem supportRepresentation_coe (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (a : A) (x : representationSupport φ) : (supportRepresentation φ a x : H) = φ a x := rfl

end Support
end NuclearUltrapower

end
end
end
end
end
end
end
end

section

noncomputable section
open scoped TensorProduct
namespace NuclearUltrapower

section Bounds
local instance instIsBoundedSMulComplexTensorProductCarrier (H K : ComplexHilbert.{0}) : IsBoundedSMul ℂ (H ⊗[ℂ] K) :=
  NormedSpace.toIsBoundedSMul
end Bounds
end NuclearUltrapower
end
end

end OAI
end


