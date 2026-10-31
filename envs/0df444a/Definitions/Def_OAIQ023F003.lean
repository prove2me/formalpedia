-- Prove2me | Definitions.Def_OAIQ023F003
-- name    : OAIQ023F003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:38:47.28703+00:00
-- url     : https://prove2.me/theorems/25635487-69de-4f83-9a2f-c4348396c948
-- title:
--   Definitions bundle OAIQ023F003 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 161 declarations of OpenAI's Lean: 67 definitions, 20 instances and 74 theorems. The definitions and types are `OAI.LittleFinitistic.FiniteProjectiveHomotopy.ComplexProperty`, `OAI.LittleFinitistic.FiniteProjectiveHomotopy.K`, `OAI.LittleFinitistic.FiniteProjectiveHomotopy.boundedDerivedEquivalence`, `OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbedding`, `OAI.LittleFinitistic.FiniteProjectiveHomotopy.inclusion`, `OAI.LittleFinitistic.FiniteProjectiveHomotopy.objects`, `OAI.LittleFinitistic.FirstVertex.biprodInlIso`, `OAI.LittleFinitistic.FunctorExtension.restrictionIso`, `OAI.LittleFinitistic.GroupAlgebraPresentation.EquationIndex`, `OAI.LittleFinitistic.GroupAlgebraPresentation.Letter`, `OAI.LittleFinitistic.GroupAlgebraPresentation.PresentedAlgebra`, `OAI.LittleFinitistic.GroupAlgebraPresentation.equation`, `OAI.LittleFinitistic.GroupAlgebraPresentation.evaluation`, `OAI.LittleFinitistic.GroupAlgebraPresentation.fromGroupAlgebra`, `OAI.LittleFinitistic.GroupAlgebraPresentation.generatorUnit`, `OAI.LittleFinitistic.GroupAlgebraPresentation.groupAlgebraUnit`, `OAI.LittleFinitistic.GroupAlgebraPresentation.groupToUnits`, `OAI.LittleFinitistic.GroupAlgebraPresentation.polynomial`, `OAI.LittleFinitistic.GroupAlgebraPresentation.quotientEquiv`, `OAI.LittleFinitistic.GroupAlgebraPresentation.quotientMap`, `OAI.LittleFinitistic.GroupAlgebraPresentation.relations`, `OAI.LittleFinitistic.GroupAlgebraPresentation.toGroupAlgebra`, `OAI.LittleFinitistic.GroupAlgebraPresentation.word`, `OAI.LittleFinitistic.GroupAlgebraPresentation.zeroQuotientEquiv`, `OAI.LittleFinitistic.GroupAlgebraPresentation.zeroRelations`, `OAI.LittleFinitistic.OrdinarySimulation.ChainAlgebra`, `OAI.LittleFinitistic.OrdinarySimulation.OrdinaryTerms`, `OAI.LittleFinitistic.OrdinarySimulation.SupportedExtension.component`, `OAI.LittleFinitistic.QuadraticEncoding.FiniteVectorDerived`, `OAI.LittleFinitistic.QuadraticEncoding.FiniteVectorHomotopy`, `OAI.LittleFinitistic.QuadraticEncoding.completedCommutationIso`, `OAI.LittleFinitistic.QuadraticEncoding.completedExtensionFactors`, `OAI.LittleFinitistic.QuadraticEncoding.completedExtensionImageIso`, `OAI.LittleFinitistic.QuadraticEncoding.derivedTargetInclusion`, `OAI.LittleFinitistic.QuadraticEncoding.identifiedEndHom`, `OAI.LittleFinitistic.QuadraticEncoding.imageCornerEnd`, `OAI.LittleFinitistic.QuadraticEncoding.imageInclusion`, `OAI.LittleFinitistic.QuadraticEncoding.imageProjection`, `OAI.LittleFinitistic.QuadraticEncoding.liftedEndHom`, `OAI.LittleFinitistic.QuadraticEncoding.splitKaroubiIso` and 27 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Encoding_QuadraticCoefficients`, `Finitistic_Localization_BoundedDerivedEmbedding`, `Finitistic_Localization_CompletedCornerEvaluation`, `Finitistic_Localization_CompletedDerivedEvaluation`, `Finitistic_Localization_CompletedImageEvaluation`, `Finitistic_Localization_CompletedShiftEvaluation`, `Finitistic_Localization_FiniteDerivedEvaluation`, `Finitistic_Localization_FiniteEvaluationTarget`, `Finitistic_Localization_FiniteProjectiveHomotopy`, `Finitistic_Localization_HomotopyVertexEvaluation`, `Finitistic_Localization_IdempotentImageEvaluation`, `Finitistic_Localization_KaroubiEvaluation`, `Finitistic_Localization_PresentedActionCompatibility`, `Finitistic_Localization_SourceCornerEvaluation`, `Finitistic_Localization_SourceImageEvaluation`, `Finitistic_Localization_SourceOddDoubleEvaluation`, `Finitistic_Localization_TwoConeVerdier`, `Finitistic_Localization_VectorComplexFormality`, `Finitistic_Localization_VectorIdempotentCompleteness`, `Finitistic_Ordinary_OrdinaryChainAlgebra`, `Finitistic_Ordinary_OrdinaryComplexAction`, `Finitistic_Ordinary_OrdinaryFunctorExtension`, `Finitistic_Ordinary_OrdinarySupportedExtension`, `Finitistic_Rectification_FirstVertex`, `Finitistic_Rectification_LeftVertexHomology`, `Finitistic_Rectification_RectificationAcyclic`, `Finitistic_Rectification_ZeroColumnTotal`, `Finitistic_Selected_SelectedCohomologyAssembly`, `Finitistic_Selected_SelectedReferenceCohomology`, `Finitistic_Selected_SelectedTargetHomology`, `Finitistic_Selection_FiniteQuotient`, `Finitistic_Selection_GroupAlgebraPresentation`, `Finitistic_Selection_GroupSelection`, `Finitistic_Selection_MatrixModel`, `Finitistic_Selection_SelectionCharacter`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F008` and `OAIQ023F013`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_GroupAlgebraPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Section 2 bridge. All algebras here are associative, unital, and may be
noncommutative. The defining congruence is generated by finitely many equations
in a free associative algebra; no commutative finite-presentation API is used. -/
noncomputable section
namespace LittleFinitistic.GroupAlgebraPresentation

variable (R : Type*) [CommRing R] (α : Type*)

/-- A representative word, chosen only to turn a group relator into a polynomial. -/
def word (g : FreeGroup α) : List (α × Bool) :=
  Classical.choose (Quot.exists_rep g)

theorem word_spec (g : FreeGroup α) : FreeGroup.mk (word α g) = g :=
  Classical.choose_spec (Quot.exists_rep g)

def polynomial (g : FreeGroup α) : FreeAlgebra R (α × Bool) :=
  ((word α g).map (FreeAlgebra.ι R)).prod

variable {α R}

theorem eval_polynomial {A : Type*} [Ring A] [Algebra R A]
    (f : α → Aˣ) (F : FreeAlgebra R (α × Bool) →ₐ[R] A)
    (hf : ∀ a b, F (FreeAlgebra.ι R (a,b)) =
      ↑(if b then f a else (f a)⁻¹)) (g : FreeGroup α) :
    F (polynomial R α g) = ↑(FreeGroup.lift f g) := by
  conv_rhs => rw [← word_spec α g]
  simp only [polynomial, map_list_prod, List.map_map, FreeGroup.lift_mk]
  induction word α g with
  | nil => simp
  | cons a l ih =>
    rcases a with ⟨a,b⟩
    simp only [List.map_cons, List.prod_cons, Function.comp_apply, Units.val_mul]
    rw [hf, ih]
    cases b <;> rfl

variable (R α) (rels : Set (FreeGroup α))

abbrev Letter := α × Bool
abbrev EquationIndex := (α × Bool) ⊕ rels

/-- Two inverse equations per generator, and one polynomial per group relator. -/
def equation : EquationIndex α rels → FreeAlgebra R (Letter α)
  | .inl (a,b) => FreeAlgebra.ι R (a,b) * FreeAlgebra.ι R (a,!b)
  | .inr r => polynomial R α r

def relations : RingCon (FreeAlgebra R (Letter α)) :=
  ringConGen (fun x y => ∃ i : EquationIndex α rels, x = equation R α rels i ∧ y = 1)

abbrev PresentedAlgebra := (relations R α rels).Quotient

def quotientMap : FreeAlgebra R (Letter α) →ₐ[R] PresentedAlgebra R α rels :=
  (relations R α rels).mkₐ R

theorem equation_holds (i : EquationIndex α rels) :
    quotientMap R α rels (equation R α rels i) = 1 := by
  exact (relations R α rels).eq.mpr (RingConGen.Rel.of _ _ ⟨i,rfl,rfl⟩)

def generatorUnit (a : α) : (PresentedAlgebra R α rels)ˣ where
  val := quotientMap R α rels (FreeAlgebra.ι R (a,true))
  inv := quotientMap R α rels (FreeAlgebra.ι R (a,false))
  val_inv := by simpa [equation, map_mul] using equation_holds R α rels (.inl (a,true))
  inv_val := by simpa [equation, map_mul] using equation_holds R α rels (.inl (a,false))

theorem quotient_letter (a : α) (b : Bool) :
    quotientMap R α rels (FreeAlgebra.ι R (a,b)) =
      ↑(if b then generatorUnit R α rels a else (generatorUnit R α rels a)⁻¹) := by
  cases b <;> rfl

theorem unit_relator (r : FreeGroup α) (hr : r ∈ rels) :
    FreeGroup.lift (generatorUnit R α rels) r = 1 := by
  apply Units.ext
  rw [← eval_polynomial _ _ (quotient_letter R α rels)]
  exact equation_holds R α rels (.inr ⟨r,hr⟩)

def groupToUnits : PresentedGroup rels →* (PresentedAlgebra R α rels)ˣ :=
  PresentedGroup.toGroup (unit_relator R α rels)

def fromGroupAlgebra : MonoidAlgebra R (PresentedGroup rels) →ₐ[R] PresentedAlgebra R α rels :=
  MonoidAlgebra.lift R _ _ ((Units.coeHom _).comp (groupToUnits R α rels))

def groupAlgebraUnit (a : α) : (MonoidAlgebra R (PresentedGroup rels))ˣ :=
  (MonoidAlgebra.of R (PresentedGroup rels)).toHomUnits (PresentedGroup.of a)

def evaluation : FreeAlgebra R (Letter α) →ₐ[R] MonoidAlgebra R (PresentedGroup rels) :=
  FreeAlgebra.lift R (fun (a,b) =>
    ↑(if b then groupAlgebraUnit R α rels a else (groupAlgebraUnit R α rels a)⁻¹))

theorem evaluation_polynomial (r : FreeGroup α) :
    evaluation R α rels (polynomial R α r) =
      MonoidAlgebra.of R _ (PresentedGroup.mk rels r) := by
  rw [eval_polynomial (groupAlgebraUnit R α rels) _ (by intros; simp [evaluation])]
  have h : FreeGroup.lift (groupAlgebraUnit R α rels) =
      (MonoidAlgebra.of R (PresentedGroup rels)).toHomUnits.comp (PresentedGroup.mk rels) := by
    apply FreeGroup.ext_hom
    intro a
    simp [groupAlgebraUnit, PresentedGroup.of]
  rw [h]
  rfl

theorem evaluation_equation (i : EquationIndex α rels) :
    evaluation R α rels (equation R α rels i) = 1 := by
  rcases i with ⟨a,b⟩ | ⟨r,hr⟩
  · cases b <;> simp [equation, evaluation]
  · rw [equation, evaluation_polynomial]
    have h : PresentedGroup.mk rels r = 1 := by
      exact PresentedGroup.one_of_mem hr
    rw [h, map_one]

def toGroupAlgebra : PresentedAlgebra R α rels →ₐ[R] MonoidAlgebra R (PresentedGroup rels) :=
  (relations R α rels).liftₐ (evaluation R α rels)
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨i,rfl,rfl⟩
      exact (evaluation_equation R α rels i).trans (map_one _).symm))

@[simp] theorem toGroupAlgebra_quotient (x : FreeAlgebra R (Letter α)) :
    toGroupAlgebra R α rels (quotientMap R α rels x) = evaluation R α rels x := rfl

@[simp] theorem fromGroupAlgebra_of (a : α) :
    fromGroupAlgebra R α rels (MonoidAlgebra.of R _ (PresentedGroup.of a)) =
      quotientMap R α rels (FreeAlgebra.ι R (a,true)) := by
  simp [fromGroupAlgebra, groupToUnits, generatorUnit]

@[simp] theorem fromGroupAlgebra_inv_of (a : α) :
    fromGroupAlgebra R α rels (MonoidAlgebra.of R _ (PresentedGroup.of a)⁻¹) =
      quotientMap R α rels (FreeAlgebra.ι R (a,false)) := by
  simp [fromGroupAlgebra, groupToUnits, generatorUnit]

@[simp] theorem from_to_letter (a : α) (b : Bool) :
    fromGroupAlgebra R α rels (evaluation R α rels (FreeAlgebra.ι R (a,b))) =
      quotientMap R α rels (FreeAlgebra.ι R (a,b)) := by
  cases b
  · simpa only [evaluation, FreeAlgebra.lift_ι_apply, Bool.false_eq_true, ite_false, if_false, groupAlgebraUnit, ← map_inv, MonoidHom.coe_toHomUnits]
      using fromGroupAlgebra_inv_of R α rels a
  · simpa only [evaluation, FreeAlgebra.lift_ι_apply, ite_true, if_true, groupAlgebraUnit, MonoidHom.coe_toHomUnits]
      using fromGroupAlgebra_of R α rels a

theorem from_to : (fromGroupAlgebra R α rels).comp (toGroupAlgebra R α rels) =
    AlgHom.id R (PresentedAlgebra R α rels) := by
  have h : ((fromGroupAlgebra R α rels).comp (toGroupAlgebra R α rels)).comp
      (quotientMap R α rels) = quotientMap R α rels := by
    apply FreeAlgebra.hom_ext
    funext ⟨a,b⟩
    exact from_to_letter R α rels a b
  apply AlgHom.ext
  intro x
  obtain ⟨p,rfl⟩ := (relations R α rels).mkₐ_surjective (α := R) x
  exact DFunLike.congr_fun h p

theorem to_from : (toGroupAlgebra R α rels).comp (fromGroupAlgebra R α rels) =
    AlgHom.id R (MonoidAlgebra R (PresentedGroup rels)) := by
  apply (MonoidAlgebra.lift R _ _).symm.injective
  have hext (f g : PresentedGroup rels →* MonoidAlgebra R (PresentedGroup rels))
      (h : ∀ a, f (PresentedGroup.of a) = g (PresentedGroup.of a)) : f = g := by
    have hh : f.comp (PresentedGroup.mk rels) = g.comp (PresentedGroup.mk rels) :=
      FreeGroup.ext_hom _ _ h
    apply MonoidHom.ext
    intro x
    obtain ⟨r,rfl⟩ := PresentedGroup.mk_surjective rels x
    exact DFunLike.congr_fun hh r
  apply hext
  intro a
  change toGroupAlgebra R α rels
    (fromGroupAlgebra R α rels (MonoidAlgebra.of R _ (PresentedGroup.of a))) = _
  rw [fromGroupAlgebra_of, toGroupAlgebra_quotient]
  simp [evaluation, groupAlgebraUnit]

/-- Explicit free associative algebra quotient presenting the group algebra. -/
def quotientEquiv : PresentedAlgebra R α rels ≃ₐ[R] MonoidAlgebra R (PresentedGroup rels) :=
  AlgEquiv.ofAlgHom (toGroupAlgebra R α rels) (fromGroupAlgebra R α rels)
    (to_from R α rels) (from_to R α rels)


/-- Polynomial zero relations for the same explicit presentation. -/
def zeroRelations : RingCon (FreeAlgebra R (Letter α)) :=
  ringConGen (fun x y => ∃ i : EquationIndex α rels,
    x = equation R α rels i - 1 ∧ y = 0)

/-- Writing each equation p = 1 as p - 1 = 0 does not change the quotient.
This matches the manuscript notation k⟨x₁,...,x_d⟩/(p₁,...,p_t). -/
theorem relations_eq_zeroRelations : relations R α rels = zeroRelations R α rels := by
  apply le_antisymm
  · apply RingCon.ringConGen_le.mpr
    rintro x y ⟨i,rfl,rfl⟩
    have h : zeroRelations R α rels (equation R α rels i - 1) 0 :=
      RingConGen.Rel.of _ _ ⟨i,rfl,rfl⟩
    have hh := (zeroRelations R α rels).add h ((zeroRelations R α rels).refl 1)
    simpa only [sub_add_cancel, zero_add] using hh
  · apply RingCon.ringConGen_le.mpr
    rintro x y ⟨i,rfl,rfl⟩
    have h : relations R α rels (equation R α rels i) 1 :=
      RingConGen.Rel.of _ _ ⟨i,rfl,rfl⟩
    have hh := (relations R α rels).add h ((relations R α rels).refl (-1))
    simpa only [← sub_eq_add_neg, sub_self] using hh

/-- The explicit presentation is also a quotient by finitely many polynomial
zero relations, in the exact form used by Section 3 of the manuscript. -/
def zeroQuotientEquiv : (zeroRelations R α rels).Quotient ≃ₐ[R]
    MonoidAlgebra R (PresentedGroup rels) :=
  relations_eq_zeroRelations R α rels ▸ quotientEquiv R α rels

end LittleFinitistic.GroupAlgebraPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticPresentation

variable (R : Type*) [CommRing R] (α : Type*)

abbrev Term := Unit ⊕ (α ⊕ (α × α))

def term : Term α → FreeAlgebra R α
  | .inl _ => 1
  | .inr (.inl a) => FreeAlgebra.ι R a
  | .inr (.inr (a,b)) => FreeAlgebra.ι R a * FreeAlgebra.ι R b

/-- Finite coefficient form, suitable for the source's homogenization rule. -/
def coefficientPolynomial [Fintype α] (c : R) (l : α → R) (q : α → α → R) :
    FreeAlgebra R α :=
  algebraMap R (FreeAlgebra R α) c +
    ∑ a, l a • FreeAlgebra.ι R a +
    ∑ a, ∑ b, q a b • (FreeAlgebra.ι R a * FreeAlgebra.ι R b)

end LittleFinitistic.QuadraticPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteProjectiveHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject
namespace LittleFinitistic.FiniteProjectiveHomotopy
universe u v
variable (R : Type u) [Ring R]

/-- Actual bounded complexes of finitely generated projective right/left modules,
according to the chosen scalar ring R. -/
def ComplexProperty (K : CochainComplex (ModuleCat.{v} R) ℤ) : Prop :=
  (∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (K.X i)) ∧
  ∀ i, Module.Finite R (K.X i) ∧ Projective (K.X i)

def objects : ObjectProperty (HomotopyCategory (ModuleCat.{v} R) (.up ℤ)) :=
  fun T => ComplexProperty R T.as

@[simp] theorem objects_quotient (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    objects R ((HomotopyCategory.quotient _ _).obj K) ↔ ComplexProperty R K := Iff.rfl

lemma finite_projective_of_isZero (M : ModuleCat.{v} R) (h : IsZero M) :
    Module.Finite R M ∧ Projective M := by
  have := ModuleCat.subsingleton_of_isZero h
  exact ⟨inferInstance,h.projective⟩

instance objectsZero : (objects.{u,v} R).ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient _ _).obj 0,
    (HomotopyCategory.quotient _ _).map_isZero (isZero_zero _), by
      have hz (i : ℤ) : IsZero ((0 : CochainComplex (ModuleCat.{v} R) ℤ).X i) :=
        (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
      exact ⟨⟨0,0,fun i _ => hz i⟩,fun i => finite_projective_of_isZero R _ (hz i)⟩⟩

instance objectsShift : (objects.{u,v} R).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift T hT := by
        obtain ⟨K,rfl⟩ := T.quotient_obj_surjective
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj]
        change ComplexProperty R (K⟦n⟧)
        obtain ⟨⟨a,b,hb⟩,hp⟩ := hT
        constructor
        · refine ⟨a-n,b-n,fun i hi => ?_⟩
          change IsZero (K.X (i+n))
          exact hb (i+n) (by omega)
        · intro i
          exact hp (i+n) }

/-- K^b(proj-R), as a full subcategory with actual bounded f.g. projective representatives. -/
abbrev K := (objects.{u,v} R).FullSubcategory

/-- Its full and faithful inclusion into the ambient homotopy category. -/
abbrev inclusion : K.{u,v} R ⥤ HomotopyCategory (ModuleCat.{v} R) (.up ℤ) := (objects R).ι
end LittleFinitistic.FiniteProjectiveHomotopy

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_BoundedDerivedEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.FiniteProjectiveHomotopy
universe u v
variable (R : Type u) [Ring R]

instance underlyingKProjective (T : K.{u,v} R) : CochainComplex.IsKProjective T.obj.as := by
  obtain ⟨⟨a,b,hb⟩,hp⟩ := T.property
  have : ∀ n, Projective (T.obj.as.X n) := fun n => (hp n).2
  have : CochainComplex.IsStrictlyLE T.obj.as b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hb i (Or.inr hi)
  exact CochainComplex.isKProjective_of_projective T.obj.as b

/-- The canonical derived-category functor on the actual bounded projective source. -/
def derivedEmbedding : K.{u,v} R ⥤ DerivedCategory (ModuleCat.{v} R) :=
  inclusion R ⋙ DerivedCategory.Qh

instance derivedEmbeddingFaithful : (derivedEmbedding.{u,v} R).Faithful where
  map_injective {M N} {f g} h := by
    apply (inclusion R).map_injective
    exact (CochainComplex.IsKProjective.Qh_map_bijective M.obj.as N.obj).injective h

instance derivedEmbeddingFull : (derivedEmbedding.{u,v} R).Full where
  map_surjective {M N} f := by
    obtain ⟨g,hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective M.obj.as N.obj).surjective f
    refine ⟨(inclusion R).preimage g,?_⟩
    change DerivedCategory.Qh.map ((inclusion R).map ((inclusion R).preimage g)) = f
    erw [Functor.map_preimage]
    exact hg

instance derivedEmbeddingShift : (derivedEmbedding.{u,v} R).CommShift ℤ :=
  inferInstanceAs ((inclusion R ⋙ DerivedCategory.Qh).CommShift ℤ)

/-- Bounded complexes of f.g. projectives form a full subcategory of the actual derived category. -/
def boundedDerivedEquivalence : K.{u,v} R ≌ (derivedEmbedding.{u,v} R).EssImageSubcategory :=
  (derivedEmbedding R).toEssImage.asEquivalence
end LittleFinitistic.FiniteProjectiveHomotopy

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteEvaluationTarget
attribute [-instance] _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy
universe u v
variable {k : Type u}
  [Field k]
  {d t : ℕ}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]

/-- The concrete bounded homotopy category of finite-dimensional vector spaces. -/
abbrev FiniteVectorHomotopy := K.{u,max u v} k

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteDerivedEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy
universe u v
variable {k : Type u}
  [Field k]
  {d t : ℕ}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]

/-- The full subcategory of the canonical derived category represented by bounded
finite-dimensional complexes. Over a field all its terms are projective. -/
abbrev FiniteVectorDerived := (derivedEmbedding.{u,max u v} k).EssImageSubcategory

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_HomotopyVertexEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy
universe u v
variable {k : Type u}
  [Field k]
  {d t : ℕ}
variable {Y : Type v}
  [AddCommGroup Y]
  [Module k Y]

abbrev vectorStalk := HomotopyCategory.singleFunctor (ModuleCat.{max u v} k) 0

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_PresentedActionCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
universe u v w z

section LinearFunctor
variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable {D : Type z} [Category D] [Preadditive D] [Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k] (L : C) {T : D} (e : F.obj L ≅ T)

/-- Evaluation of endomorphisms, expressed in a specified identification of the target. -/
def identifiedEndHom : End L →ₐ[k] End T where
  toFun a := e.inv ≫ F.map a ≫ e.hom
  map_zero' := by simp
  map_add' a b := by
    change e.inv ≫ F.map ((a : L ⟶ L) + b) ≫ e.hom =
      (e.inv ≫ F.map a ≫ e.hom) + (e.inv ≫ F.map b ≫ e.hom)
    rw [F.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_one' := by simp
  map_mul' a b := by simp [End.mul_def, Functor.map_comp, Category.assoc]
  commutes' c := by
    change e.inv ≫ F.map (c • 𝟙 L) ≫ e.hom = c • 𝟙 T
    simp [Linear.comp_smul, Linear.smul_comp]
end LinearFunctor

variable {k : Type u}
  [Field k]
  {d t : ℕ}
variable {Y : Type v}
  [AddCommGroup Y]
  [Module k Y]

/-- Canonical transport of every endomorphism of Y to its universe lift. -/
def liftedEndHom : Module.End k Y →ₐ[k] End (ModuleCat.of k (ULift.{u} Y)) where
  toFun a := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    (a.comp ULift.moduleEquiv.toLinearMap))
  map_zero' := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; rfl
  map_add' a b := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; rfl
  map_one' := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; rfl
  map_mul' a b := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; rfl
  commutes' c := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; rfl

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_KaroubiEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
namespace LittleFinitistic.QuadraticEncoding
universe u v w
section General
variable {C : Type u} [Category.{v} C]

/-- An actual splitting realizes the corresponding formal Karoubi object. -/
def splitKaroubiIso {A I : C} (p : A ⟶ A) (hp : p ≫ p = p)
    (π : A ⟶ I) (ι : I ⟶ A) (hπι : π ≫ ι = p) (hιπ : ι ≫ π = 𝟙 I) :
    (⟨A,p,hp⟩ : Karoubi C) ≅ (toKaroubi C).obj I where
  hom := ⟨π, by simp only [toKaroubi_obj_p]; rw [← hπι]; simp [Category.assoc,hιπ]⟩
  inv := ⟨ι, by simp only [toKaroubi_obj_p]; rw [← hπι]; simp [← Category.assoc,hιπ]⟩
  hom_inv_id := by ext; exact hπι
  inv_hom_id := by ext; exact hιπ

end General

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_IdempotentImageEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
universe u v w z
section Image
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable (p : Module.End k V) (hp : p*p=p)

def imageProjection : ModuleCat.of k V ⟶ ModuleCat.of k (LinearMap.range p) :=
  ModuleCat.ofHom p.rangeRestrict

def imageInclusion : ModuleCat.of k (LinearMap.range p) ⟶ ModuleCat.of k V :=
  ModuleCat.ofHom (LinearMap.range p).subtype

lemma image_projection_inclusion : imageProjection p ≫ imageInclusion p = ModuleCat.ofHom p := rfl
include hp in
lemma image_inclusion_projection : imageInclusion p ≫ imageProjection p = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y,hy⟩ := x.property
  change p x.val = x.val
  rw [← hy]
  exact LinearMap.congr_fun hp y

end Image

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_VectorComplexFormality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.VectorComplexFormality
open FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k]

/-- A graded vector space regarded as a complex with zero differential. -/
def zeroComplex (V : ℤ → ModuleCat.{v} k) : CochainComplex (ModuleCat.{v} k) ℤ where
  X := V
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def homologySection (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ) :
    C.homology i ⟶ C.cycles i := by
  haveI : Projective (C.homology i) := ModuleCat.projective_of_categoryTheory_projective _
  exact Projective.factorThru (𝟙 _) (C.homologyπ i)

lemma homologySection_comp (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ) :
    homologySection C i ≫ C.homologyπ i = 𝟙 _ := by
  have : Projective (C.homology i) := ModuleCat.projective_of_categoryTheory_projective _
  exact Projective.factorThru_comp (𝟙 _) (C.homologyπ i)

/-- Choose cycle representatives for each homology vector space. -/
def formalityMap (C : CochainComplex (ModuleCat.{v} k) ℤ) :
    zeroComplex (fun i => C.homology i) ⟶ C where
  f i := homologySection C i ≫ C.iCycles i
  comm' i j _ := by
    change (homologySection C i ≫ C.iCycles i) ≫ C.d i j = 0 ≫ _
    rw [Category.assoc, C.iCycles_d, Limits.comp_zero, Limits.zero_comp]

lemma formality_cycles (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ) :
    cyclesMap (formalityMap C) i = (zeroComplex (fun i => C.homology i)).iCycles i ≫ homologySection C i := by
  apply (cancel_mono (C.iCycles i)).mp
  erw [cyclesMap_i, Category.assoc]
  rfl

lemma formality_homology (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ) :
    (zeroComplex (fun i => C.homology i)).homologyπ i ≫ homologyMap (formalityMap C) i =
      (zeroComplex (fun i => C.homology i)).iCycles i := by
  erw [homologyπ_naturality, formality_cycles, Category.assoc, homologySection_comp]
  exact Category.comp_id _

instance formalityMapQuasiIso (C : CochainComplex (ModuleCat.{v} k) ℤ) :
    QuasiIso (formalityMap C) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := (zeroComplex (fun i => C.homology i)).isIso_homologyπ (i-1) i (by simp) rfl
  apply (isIso_comp_left_iff ((zeroComplex (fun i => C.homology i)).homologyπ i)
    (homologyMap (formalityMap C) i)).mp
  erw [formality_homology C i]
  exact (zeroComplex (fun i => C.homology i)).isIso_iCycles i (i+1) (by simp) rfl

lemma homology_finite (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ)
    [Module.Finite k (C.X i)] : Module.Finite k (C.homology i) := by
  have : Module.Finite k (C.cycles i) := Module.Finite.of_injective (C.iCycles i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (C.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

lemma zeroHomology_property (C : CochainComplex (ModuleCat.{v} k) ℤ) (hC : ComplexProperty k C) :
    ComplexProperty k (zeroComplex (fun i => C.homology i)) := by
  obtain ⟨⟨a,b,hb⟩,hf⟩ := hC
  constructor
  · exact ⟨a,b,fun i hi => (HomologicalComplex.ExactAt.of_isZero (hb i hi)).isZero_homology⟩
  · intro i
    have := (hf i).1
    exact ⟨homology_finite C i, ModuleCat.projective_of_categoryTheory_projective _⟩

/-- The bounded homology representative has the same finite support and finite terms. -/
def zeroHomologyK (T : K.{u,v} k) : K.{u,v} k :=
  ⟨(HomotopyCategory.quotient _ _).obj (zeroComplex (fun i => T.obj.as.homology i)),
    zeroHomology_property T.obj.as T.property⟩

/-- Every bounded complex of vector spaces is isomorphic to its homology with zero differential. -/
def formalityIso (T : K.{u,v} k) : zeroHomologyK T ≅ T := by
  let C := T.obj.as
  let H := zeroComplex (fun i => C.homology i)
  let e : (derivedEmbedding k).obj (zeroHomologyK T) ≅ (derivedEmbedding k).obj T :=
    (DerivedCategory.quotientCompQhIso _).app H ≪≫
      asIso (DerivedCategory.Q.map (formalityMap C)) ≪≫
      ((DerivedCategory.quotientCompQhIso _).app C).symm
  exact (derivedEmbedding k).preimageIso e
end LittleFinitistic.VectorComplexFormality

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_VectorIdempotentCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents HomologicalComplex
namespace LittleFinitistic.VectorComplexFormality
open FiniteProjectiveHomotopy QuadraticEncoding
universe u v
variable {k : Type u} [Field k]

lemma zeroDifferential_homotopy_eq {C D : CochainComplex (ModuleCat.{v} k) ℤ}
    (hC : ∀ i j, C.d i j = 0) (hD : ∀ i j, D.d i j = 0) (f g : C ⟶ D)
    (h : (HomotopyCategory.quotient _ _).map f = (HomotopyCategory.quotient _ _).map g) : f=g := by
  ext i : 1
  have h' := (HomotopyCategory.homotopyOfEq f g h).comm i
  simpa [dNext, prevD, hC, hD] using h'

lemma zeroDifferential_idempotents_split (T : K.{u,v} k)
    (hT : ∀ i j, T.obj.as.d i j = 0) (p : T ⟶ T) (hp : p ≫ p=p) :
    ∃ (I : K.{u,v} k) (ι : I ⟶ T) (π : T ⟶ I), ι ≫ π = 𝟙 I ∧ π ≫ ι = p := by
  let C := T.obj.as
  let q := HomotopyCategory.quotient (ModuleCat.{v} k) (.up ℤ)
  let J := inclusion k
  obtain ⟨f,hf⟩ := q.map_surjective (J.map p)
  have hff : f ≫ f=f := zeroDifferential_homotopy_eq hT hT _ _ (by
    erw [q.map_comp, hf, ← J.map_comp, hp])
  have hi (i : ℤ) : (f.f i).hom * (f.f i).hom = (f.f i).hom := by
    exact congrArg (fun g => (g.f i).hom) hff
  let V (i : ℤ) : ModuleCat.{v} k := ModuleCat.of k (LinearMap.range (f.f i).hom)
  let D := zeroComplex V
  let inc : D ⟶ C := {
    f := fun i => imageInclusion (f.f i).hom
    comm' := fun i j _ => by simp [D, zeroComplex, hT, C] }
  let pr : C ⟶ D := {
    f := fun i => imageProjection (f.f i).hom
    comm' := fun i j _ => by simp [D, zeroComplex, hT, C] }
  have hip : inc ≫ pr = 𝟙 D := by
    ext i : 1
    exact image_inclusion_projection (f.f i).hom (hi i)
  have hpi : pr ≫ inc = f := by
    ext i : 1
    exact image_projection_inclusion (f.f i).hom
  have hD : ComplexProperty k D := by
    obtain ⟨⟨a,b,hb⟩,hfin⟩ := T.property
    constructor
    · refine ⟨a,b,fun i hi => ?_⟩
      have hm : Mono (imageInclusion (f.f i).hom) := by
        rw [ModuleCat.mono_iff_injective]
        exact Submodule.subtype_injective _
      exact @IsZero.of_mono (ModuleCat k) _ _ _ _
        (imageInclusion (f.f i).hom) hm (hb i hi)
    · intro i
      have := (hfin i).1
      refine ⟨?_,ModuleCat.projective_of_categoryTheory_projective _⟩
      exact Module.Finite.of_injective (LinearMap.range (f.f i).hom).subtype
        (Submodule.subtype_injective _)
  let I : K.{u,v} k := ⟨q.obj D,hD⟩
  refine ⟨I,J.preimage (q.map inc),J.preimage (q.map pr),?_,?_⟩
  · apply J.map_injective
    rw [J.map_comp, J.map_id]
    erw [Functor.map_preimage, Functor.map_preimage]
    exact (q.map_comp inc pr).symm.trans ((congrArg q.map hip).trans (q.map_id D))
  · apply J.map_injective
    rw [J.map_comp]
    erw [Functor.map_preimage, Functor.map_preimage]
    exact (q.map_comp pr inc).symm.trans ((congrArg q.map hpi).trans hf)

/-- Bounded finite-dimensional homotopy complexes split every idempotent. -/
instance finiteVectorHomotopyIdempotentComplete : IsIdempotentComplete (K.{u,v} k) where
  idempotents_split T p hp := by
    let e := formalityIso T
    let p' := e.hom ≫ p ≫ e.inv
    have hp' : p' ≫ p'=p' := by
      dsimp [p']
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc p p, hp]
    have hz : ∀ i j, (zeroHomologyK T).obj.as.d i j = 0 := fun _ _ => rfl
    exact split_imp_of_iso e p' p (by simp [p',Category.assoc])
      (zeroDifferential_idempotents_split (zeroHomologyK T) hz p' hp')

/-- The actual bounded finite-dimensional derived target is idempotent complete. -/
instance finiteVectorDerivedIdempotentComplete :
    IsIdempotentComplete (FiniteVectorDerived.{u,v} (k := k)) :=
  CategoryTheory.Idempotents.Equivalence.isIdempotentComplete (boundedDerivedEquivalence k) inferInstance
end LittleFinitistic.VectorComplexFormality

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_CompletedDerivedEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy VectorComplexFormality
universe u v w z
section General
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type w} [Category.{z} D] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]

instance karoubiExtensionAdditive : ((functorExtension₂ C D).obj F).Additive where
  map_add := by
    intro A B f g
    apply Karoubi.Hom.ext
    exact F.map_add

variable [IsIdempotentComplete D]

instance completedExtensionAdditive : ((functorExtension C D).obj F).Additive :=
  inferInstanceAs (((functorExtension₂ C D).obj F ⋙ (toKaroubiEquivalence D).inverse).Additive)

/-- The extension restricts to the original functor under the canonical embedding. -/
def completedExtensionFactors :
    toKaroubi C ⋙ (functorExtension C D).obj F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F)
      (toKaroubiEquivalence D).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (toKaroubiEquivalence D).unitIso.symm ≪≫
    Functor.rightUnitor F
/-- An explicitly split evaluated idempotent identifies the value of the completion. -/
def completedExtensionImageIso (U : Karoubi C) (I : D)
    (π : F.obj U.X ⟶ I) (ι : I ⟶ F.obj U.X)
    (hπι : π ≫ ι = F.map U.p) (hιπ : ι ≫ π = 𝟙 I) :
    ((functorExtension C D).obj F).obj U ≅ I :=
  (toKaroubiEquivalence D).inverse.mapIso
    (splitKaroubiIso (F.map U.p) (by rw [← F.map_comp, U.idem]) π ι hπι hιπ) ≪≫
    (toKaroubiEquivalence D).unitIso.symm.app I

end General

variable {k : Type u}
  [Field k]
  {d t : ℕ}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]

instance derivedEmbeddingAdditive : (derivedEmbedding.{u,max u v} k).Additive :=
  inferInstanceAs ((inclusion k ⋙ DerivedCategory.Qh).Additive)

instance derivedToEssImageAdditive : ((derivedEmbedding.{u,max u v} k).toEssImage).Additive := by
  dsimp [Functor.toEssImage]
  infer_instance

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_CompletedImageEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy
universe u v

variable {k : Type u}
  [Field k]
  {d t : ℕ}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]

abbrev derivedTargetInclusion := (derivedEmbedding.{u,max u v} k).essImage.ι

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_CompletedCornerEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
universe u v w z
section General
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type w} [Category.{z} D] [Preadditive D] [IsIdempotentComplete D]
variable (F : C ⥤ D) [F.Additive] (U : Karoubi C) (I : D)
variable (π : F.obj U.X ⟶ I) (ι : I ⟶ F.obj U.X)
variable (hπι : π ≫ ι = F.map U.p) (hιπ : ι ≫ π = 𝟙 I)

omit [Preadditive C] [Preadditive D] [F.Additive] in
theorem completedExtensionImageSquare (a : U ⟶ U) (b : I ⟶ I)
    (h : F.map a.f ≫ π = π ≫ b) :
    ((functorExtension C D).obj F).map a ≫
      (completedExtensionImageIso F U I π ι hπι hιπ).hom =
    (completedExtensionImageIso F U I π ι hπι hιπ).hom ≫ b := by
  let e := splitKaroubiIso (F.map U.p) (by rw [← F.map_comp, U.idem]) π ι hπι hιπ
  have he : ((functorExtension₂ C D).obj F).map a ≫ e.hom =
      e.hom ≫ (toKaroubi D).map b := by
    apply Karoubi.Hom.ext
    exact h
  change (toKaroubiEquivalence D).inverse.map (((functorExtension₂ C D).obj F).map a) ≫
    ((toKaroubiEquivalence D).inverse.map e.hom ≫ (toKaroubiEquivalence D).unitIso.inv.app I) =
    ((toKaroubiEquivalence D).inverse.map e.hom ≫ (toKaroubiEquivalence D).unitIso.inv.app I) ≫ b
  erw [← Category.assoc, ← Functor.map_comp, he, Functor.map_comp, Category.assoc]
  erw [(toKaroubiEquivalence D).unitIso.inv.naturality b]
  exact (Category.assoc _ _ _).symm
end General

section Image
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable (p a : Module.End k V) (hp : p*p=p)

def imageCornerEnd : ModuleCat.of k (LinearMap.range p) ⟶ ModuleCat.of k (LinearMap.range p) :=
  imageInclusion p ≫ ModuleCat.ofHom a ≫ imageProjection p

include hp in
lemma image_corner_square :
    ModuleCat.ofHom (p*a*p) ≫ imageProjection p = imageProjection p ≫ imageCornerEnd p a := by
  change ((ModuleCat.ofHom p ≫ ModuleCat.ofHom a) ≫ ModuleCat.ofHom p) ≫ imageProjection p = _
  rw [← image_projection_inclusion p]
  simp only [imageCornerEnd, Category.assoc, image_inclusion_projection p hp, Category.comp_id]

include hp in
/-- When a commutes with p, the corner operator is the restriction of a to the image. -/
lemma imageCornerEnd_apply (ha : p*a=a*p) (x : LinearMap.range p) :
    ((imageCornerEnd p a) x).val = a x.val := by
  change p (a x.val) = a x.val
  have h := LinearMap.congr_fun ha x.val
  change p (a x.val) = a (p x.val) at h
  rw [h]
  obtain ⟨y,hy⟩ := x.property
  have hp' : p x.val = x.val := by rw [← hy]; exact LinearMap.congr_fun hp y
  rw [hp']
end Image

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_CompletedShiftEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
universe u v w z
section General
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type w} [Category.{z} D] [Preadditive D] [IsIdempotentComplete D]
variable (F : C ⥤ D) [F.Additive]

/-- Commutation with any endofunctor extends uniquely across idempotent completion. -/
def completedCommutationIso (S : C ⥤ C) (T : D ⥤ D) (e : S ⋙ F ≅ F ⋙ T) :
    (functorExtension₂ C C).obj S ⋙ (functorExtension C D).obj F ≅
      (functorExtension C D).obj F ⋙ T := by
  let G := (functorExtension C D).obj F
  let S' := (functorExtension₂ C C).obj S
  let h : toKaroubi C ⋙ (S' ⋙ G) ≅ toKaroubi C ⋙ (G ⋙ T) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso C C).app S) G ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft S (completedExtensionFactors F) ≪≫ e ≪≫
      Functor.isoWhiskerRight (completedExtensionFactors F).symm T ≪≫
      Functor.associator _ _ _
  exact (whiskeringLeftObjToKaroubiFullyFaithful (C := C) (D := D)).preimageIso h
end General

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TwoConeVerdier
attribute [-instance] _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits Pretriangulated Category
namespace LittleFinitistic.TwoConeVerdier

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

namespace ConePair

variable {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

instance zeroRetracts : ObjectProperty.IsStableUnderRetracts (IsZero (C := D)) where
  of_retract r h := by
    rw [IsZero.iff_id_eq_zero, ← r.retract, h.eq_of_tgt r.i 0, zero_comp]

instance zeroShift : ObjectProperty.IsStableUnderShift (IsZero (C := D)) ℤ where
  isStableUnderShiftBy n := { le_shift := fun _ h => (shiftFunctor D n).map_isZero h }

instance zeroTriangulated : ObjectProperty.IsTriangulated (IsZero (C := D)) where
  toIsTriangulatedClosed₂ := .mk' (fun U hU h₁ h₃ => U.isZero₂_of_isZero₁₃ hU h₁ h₃)

variable (F : C ⥤ D)
  [F.CommShift ℤ]
  [F.IsTriangulated]

instance kernelRetracts : F.kernel.IsStableUnderRetracts where
  of_retract r h := ObjectProperty.IsStableUnderRetracts.of_retract (P := IsZero (C := D)) (r.map F) h

end ConePair
end LittleFinitistic.TwoConeVerdier

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_GroupSelection
attribute [-instance] _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Group identities used in Section 2 of v5s9.15. -/

open scoped commutatorElement

namespace LittleFinitistic

section GroupTransfer

variable {G : Type*} [Group G]

/-- The commutator transfer identity establishing independence of the
internal index in the paper's central involutions. -/
theorem commutator_transfer (x y v u w : G)
    (hu : x*y = u*y*x) (hw : y*v = w*v*y)
    (hxv : Commute x v) (hwu : Commute w u) (hwv : Commute w v) :
    ⁅x,w⁆ = ⁅u,v⁆ := by
  have hconj : y*x*y⁻¹ = u⁻¹*x := by
    apply (mul_left_cancel_iff (a := u)).mp
    calc
      u*(y*x*y⁻¹) = (u*y*x)*y⁻¹ := by group
      _ = (x*y)*y⁻¹ := by rw [← hu]
      _ = u*(u⁻¹*x) := by group
  have hmove : x*w*v*y = u*w*v*y*x := by
    calc
      x*w*v*y = x*(y*v) := by rw [hw]; group
      _ = (x*y)*v := by group
      _ = (u*y*x)*v := by rw [hu]
      _ = u*y*(v*x) := by simp only [mul_assoc, hxv.eq]
      _ = u*(y*v)*x := by group
      _ = u*w*v*y*x := by rw [hw]; group
  have hxw : x*w = u*w*v*u⁻¹*v⁻¹*x := by
    calc
      x*w = (x*w*v*y)*y⁻¹*v⁻¹ := by group
      _ = (u*w*v*y*x)*y⁻¹*v⁻¹ := by rw [hmove]
      _ = u*w*v*(y*x*y⁻¹)*v⁻¹ := by group
      _ = u*w*v*(u⁻¹*x)*v⁻¹ := by rw [hconj]
      _ = u*w*v*u⁻¹*(v⁻¹*x) := by simp only [mul_assoc]; rw [hxv.inv_right.eq]
      _ = u*w*v*u⁻¹*v⁻¹*x := by group
  have hwc : Commute w (v*u⁻¹*v⁻¹) := by
    simpa only [mul_assoc] using hwv.mul_right (hwu.inv_right.mul_right hwv.inv_right)
  calc
    ⁅x,w⁆ = x*w*x⁻¹*w⁻¹ := rfl
    _ = u*w*v*u⁻¹*v⁻¹*w⁻¹ := by rw [hxw]; group
    _ = u*(w*(v*u⁻¹*v⁻¹))*w⁻¹ := by group
    _ = u*((v*u⁻¹*v⁻¹)*w)*w⁻¹ := by rw [hwc.eq]
    _ = ⁅u,v⁆ := by simp only [commutatorElement_def]; group

/-- A central commutator of an involution has order dividing two. -/
theorem central_commutator_involution (x y : G) (hx : x*x = 1)
    (hc : Commute x ⁅x,y⁆) : ⁅x,y⁆ * ⁅x,y⁆ = 1 := by
  calc
    ⁅x,y⁆ * ⁅x,y⁆ = x * ⁅x,y⁆ * x⁻¹ * ⁅x,y⁆ := by rw [hc.eq]; group
    _ = ⁅x*x,y⁆ := (commutatorElement_mul_left_eq_conj_mul x x y).symm
    _ = 1 := by rw [hx]; exact commutatorElement_one_left y

end GroupTransfer

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceImageEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation
theorem sandwich_map_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : D} {B I : C} (e : A ≅ F.obj B)
    (p : B ⟶ I) (i : I ⟶ B) (b : B ⟶ B) (a : A ⟶ A)
    (h : p ≫ i = b) (sq : a ≫ e.hom = e.hom ≫ F.map b) :
    (e.hom ≫ F.map p) ≫ (F.map i ≫ e.inv) = a := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [← F.map_comp, h, sq]

open QuadraticEncoding FiniteProjectiveHomotopy
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

abbrev action (r : R) : End (ModuleCat.of k (ULift.{u} Y)) :=
  liftedEndHom ((Algebra.lsmul k k Y) r)

/-- Literal range of the selecting operator on the canonical universe lift of Y. -/
abbrev imageSpace (e : R) := LinearMap.range (action (k := k) (Y := Y) e).hom

omit [FiniteDimensional k Y] in
lemma action_idem (e : R) (he : e*e=e) :
    (action (k := k) (Y := Y) e).hom * (action (k := k) (Y := Y) e).hom = (action (k := k) (Y := Y) e).hom := by
  have h := congrArg (fun r => (action (k := k) (Y := Y) r).hom) he
  simp only [action,map_mul] at h
  exact h

end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceCornerEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation
theorem map_projection_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : D} {B I : C} (e : A ≅ F.obj B)
    (p : B ⟶ I) (b : B ⟶ B) (c : I ⟶ I) (a : A ⟶ A)
    (sq : a ≫ e.hom = e.hom ≫ F.map b) (h : b ≫ p = p ≫ c) :
    a ≫ (e.hom ≫ F.map p) = (e.hom ≫ F.map p) ≫ F.map c := by
  rw [← Category.assoc, sq, Category.assoc, ← F.map_comp, h, F.map_comp, ← Category.assoc]

open QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
  [Module R Y] [IsScalarTower k R Y]

omit [FiniteDimensional k Y] in
/-- The central corner is exactly restriction of a, on actual vectors in eY. -/
theorem imageCorner_restriction (e a : R) (he : e*e=e) (hc : e*a=a*e)
    (x : imageSpace (k := k) (Y := Y) e) :
    ((imageCornerEnd (action (k := k) (Y := Y) e).hom (action (k := k) (Y := Y) a).hom) x).val =
      (action (k := k) (Y := Y) a).hom x.val := by
  apply imageCornerEnd_apply _ _ (action_idem (k := k) (Y := Y) e he)
  have h := congrArg (fun r => (action (k := k) (Y := Y) r).hom) hc
  simp only [action,map_mul] at h
  exact h

end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SourceOddDoubleEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceImageEvaluation
theorem compose_square {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ A) (g : B ⟶ B) (h : D ⟶ D) (e : A ⟶ B) (p : B ⟶ D)
    (he : f ≫ e = e ≫ g) (hp : g ≫ p = p ≫ h) :
    f ≫ (e ≫ p) = (e ≫ p) ≫ h := by
  rw [← Category.assoc, he, Category.assoc, hp, ← Category.assoc]

open QuadraticEncoding
universe u v w
end LittleFinitistic.SourceImageEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryChainAlgebra
attribute [-instance] _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable (k : Type u) [Field k] (l : ℕ)

/-- The radical-square-zero chain algebra, in vertex and arrow coordinates.
Arrow i goes from i to i+1, with the manuscript's right-projective convention. -/
def ChainAlgebra := (Fin (l+1) → k) × (Fin l → k)
namespace ChainAlgebra
instance instAddCommGroup : AddCommGroup (ChainAlgebra k l) :=
  inferInstanceAs (AddCommGroup ((Fin (l+1) → k) × (Fin l → k)))
end ChainAlgebra

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryComplexAction
attribute [-instance] _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {k : Type u} [Field k] {l : ℕ}

/-- Actual finite direct sum of terms; the finite product is canonically that sum. -/
abbrev OrdinaryTerms (V : Fin (l+1) → Type v) := ∀ i, V i

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinarySupportedExtension
attribute [-instance] _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
attribute [local instance] Classical.propDecidable
open CategoryTheory Limits
namespace LittleFinitistic.OrdinarySimulation.SupportedExtension
universe u v w w'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable {I : Type w} {J : Type w'} {c : ComplexShape I} {c' : ComplexShape J}
variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff] [K.IsStrictlySupported e]

/-- The supported complex's restriction and extension have its actual components. -/
def component (j : J) : (K.stupidTrunc e).X j ≅ K.X j :=
  if hj : ∃ i, e.f i = j then K.stupidTruncXIso e hj.choose_spec
  else (K.isZero_stupidTrunc_X e j (by simpa using hj)).iso
    (K.isZero_X_of_isStrictlySupported e j (by simpa using hj))

omit [K.IsStrictlySupported e] in
theorem component_iso_unique {i j : I} {n : J} (hi : e.f i = n) (hj : e.f j = n) :
    K.stupidTruncXIso e hi = K.stupidTruncXIso e hj := by
  have h : i = j := e.injective_f (hi.trans hj.symm)
  subst j
  rfl

end LittleFinitistic.OrdinarySimulation.SupportedExtension

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFunctorExtension
attribute [-instance] _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.FunctorExtension
universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] [HasZeroObject D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]
variable {I : Type w} {J : Type w'} {c : ComplexShape I} {c' : ComplexShape J}
variable (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff]

omit [HasZeroObject D] [e.IsRelIff] in
/-- Mapping an extended complex retains its proved zero terms outside the embedded degrees. -/
theorem mappedSupport : ((F.mapHomologicalComplex c').obj (K.extend e)).IsStrictlySupported e where
  isZero j hj := F.map_isZero (K.isZero_extend_X e j hj)

/-- On the actual supported degrees, mapping and extension have the same original terms. -/
def restrictionIso : ((F.mapHomologicalComplex c').obj (K.extend e)).restriction e ≅
    (F.mapHomologicalComplex c).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => F.mapIso (K.extendXIso e (i := i) rfl)) (by
    intro i j _
    change F.map (K.extendXIso e (i := i) rfl).hom ≫ F.map (K.d i j) =
      F.map ((K.extend e).d (e.f i) (e.f j)) ≫ F.map (K.extendXIso e (i := j) rfl).hom
    rw [← F.map_comp,← F.map_comp]
    congr 1
    rw [HomologicalComplex.extend_d_eq _ _ rfl rfl]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id])

end LittleFinitistic.FunctorExtension

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_RectificationAcyclic
attribute [-instance] _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.RectificationAcyclic
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

variable {C : Type*} [Category C] [Abelian C]

/-- Bounded-above acyclic complexes of projectives admit an actual contraction. -/
noncomputable def contractBoundedProjective (K : CochainComplex C ℤ) (hi : ℤ)
    [K.IsStrictlyLE hi] [∀ i, Projective (K.X i)] (hK : K.Acyclic) :
    Homotopy (𝟙 K) 0 := by
  letI := CochainComplex.isKProjective_of_projective K hi
  exact CochainComplex.IsKProjective.homotopyZero (𝟙 K) hK

/-- A short exact inclusion with acyclic quotient is a quasi-isomorphism. -/
theorem quasiIso_of_acyclic_quotient (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (hQ : S.X₃.Acyclic) : QuasiIso S.f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₁ (i-1) i (by change i-1+1=i; omega)).mono_g
      ((hQ (i-1)).isZero_homology.eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₂ i).epi_f ((hQ i).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end LittleFinitistic.RectificationAcyclic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ZeroColumnTotal
attribute [-instance] _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
namespace LittleFinitistic.ZeroColumnTotal
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

def biprodInrIso {X Y : D} (hX : IsZero X) : Y ≅ X ⊞ Y where
  hom := biprod.inr
  inv := biprod.snd
  hom_inv_id := by simp
  inv_hom_id := by
    apply biprod.hom_ext
    · exact hX.eq_of_tgt _ _
    · simp

omit [HasBinaryBiproducts D] in
theorem complex_zero {X : CochainComplex D ℤ} (hX : ∀ i, IsZero (X.X i)) : IsZero X := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.Hom.ext
  funext i
  exact (hX i).eq_of_src _ _

/-- If the cone source is zero, its original inclusion is an isomorphism. -/
theorem cone_inr_isIso {X Y : CochainComplex D ℤ} (f : X ⟶ Y) (hX : IsZero X) :
    IsIso (mappingCone.inr f) := by
  have hi : ∀ i, IsIso ((mappingCone.inr f).f i) := by
    intro i
    let e : (mappingCone f).X i ≅ X.X (i+1) ⊞ Y.X i :=
      homotopyCofiber.XIsoBiprod f i (i+1) (by simp)
    rw [← isIso_comp_right_iff ((mappingCone.inr f).f i) e.hom]
    have he : (mappingCone.inr f).f i ≫ e.hom = biprod.inr :=
      homotopyCofiber.inrX_XIsoBiprod_hom f (i+1) i (by simp)
    rw [he]
    exact (biprodInrIso ((HomologicalComplex.eval D (.up ℤ) (i+1)).map_isZero hX)).isIso_hom
  let := hi
  exact HomologicalComplex.Hom.isIso_of_components _

/-- A mapped cone whose two columns vanish is actually zero. -/
theorem mappedCone_zero {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (F : C ⥤ D) [F.Additive]
    (hX : ∀ i, IsZero (F.obj (X.X i))) (hY : ∀ i, IsZero (F.obj (Y.X i))) :
    IsZero ((F.mapHomologicalComplex (.up ℤ)).obj (mappingCone f)) := by
  apply (mappingCone.mapHomologicalComplexIso f F).isZero_iff.mpr
  apply complex_zero
  intro i
  rw [mappingCone.isZero_X_iff]
  exact ⟨hX (i+1),hY i⟩

end LittleFinitistic.ZeroColumnTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FirstVertex
attribute [-instance] _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.FirstVertex
section General
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
def biprodInlIso {X Y : D} (hY : IsZero Y) : X ≅ X ⊞ Y where
  hom := biprod.inl
  inv := biprod.fst
  hom_inv_id := by simp
  inv_hom_id := by
    apply biprod.hom_ext
    · simp
    · exact hY.eq_of_tgt _ _

theorem mapped_inl_isIso (F : C ⥤ D) [F.Additive] (X Y : C) (hY : IsZero (F.obj Y)) :
    IsIso (F.map (biprod.inl : X ⟶ X ⊞ Y)) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts F
  rw [← isIso_comp_right_iff _ (F.mapBiprod X Y).hom]
  have he : F.map (biprod.inl : X ⟶ X ⊞ Y) ≫ (F.mapBiprod X Y).hom = biprod.inl := by
    apply biprod.hom_ext
    · erw [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
        ← Functor.map_comp, biprod.inl_fst, F.map_id, biprod.inl_fst]
    · erw [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd,
        ← Functor.map_comp, biprod.inl_snd, F.map_zero, biprod.inl_snd]
  rw [he]
  exact (biprodInlIso hY).isIso_hom
end General

universe u
end LittleFinitistic.FirstVertex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_LeftVertexHomology
attribute [-instance] _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.LeftVertexHomology
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

instance scalarTower (M : ModuleCat.{u} B) :
    IsScalarTower k B ((ModuleCat.restrictScalars (algebraMap k B)).obj M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

end LittleFinitistic.LeftVertexHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_FiniteQuotient
attribute [-instance] _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
Exact prerequisites for Section 2 of v5s9.15.

These are the variable-coefficient elementary-matrix calculations in the
finite-quotient construction, over the actual rings F₂[t]/(t^m - 1).
They do not establish the paper's main homological theorem.
-/

open Matrix Polynomial

namespace LittleFinitistic

section ElementaryMatrices

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def transvection (i j : ι) (a : R) : Matrix ι ι R := 1 + Matrix.single i j a

theorem single_square_zero (i j : ι) (hij : i ≠ j) (a : R) :
    (Matrix.single i j a : Matrix ι ι R) * Matrix.single i j a = 0 := by
  exact Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) a

theorem transvection_mul_neg (i j : ι) (hij : i ≠ j) (a : R) :
    transvection i j a * transvection i j (-a) = 1 := by
  simp only [transvection, ← Matrix.single_neg, mul_add, add_mul, mul_one, one_mul,
    mul_neg, single_square_zero i j hij]
  abel

def transvectionUnit (i j : ι) (hij : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := transvection i j a
  inv := transvection i j (-a)
  val_inv := transvection_mul_neg i j hij a
  inv_val := by simpa using transvection_mul_neg i j hij (-a)

theorem transvection_same (i j : ι) (hij : i ≠ j) (a b : R) :
    transvection i j a * transvection i j b = transvection i j (a + b) := by
  simp only [transvection, mul_add, add_mul, mul_one, one_mul,
    Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) b, Matrix.single_add]
  abel

theorem nilpotent_commutator {A : Type*} [Ring A] (a b : A)
    (haa : a * a = 0) (hbb : b * b = 0) (hba : b * a = 0) :
    (1+a)*(1+b)*(1-a)*(1-b) = 1+a*b := by
  calc
    (1+a)*(1+b)*(1-a)*(1-b) =
        1 + a*b - a*a - b*a - a*b*a - b*b - a*b*b + a*a*b + b*a*b + a*b*a*b := by
          noncomm_ring
    _ = 1 + a*b := by
      simp [haa, hbb, hba, mul_assoc]

theorem transvection_commutator (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    transvection i j a * transvection j k b *
      transvection i j (-a) * transvection j k (-b) =
      transvection i k (a*b) := by
  have haa := single_square_zero i j hij a
  have hbb := single_square_zero j k hjk b
  have hba : (Matrix.single j k b : Matrix ι ι R) * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne b j k i (Ne.symm hik) a
  simpa [transvection, ← Matrix.single_neg, sub_eq_add_neg] using
    nilpotent_commutator (Matrix.single i j a) (Matrix.single j k b) haa hbb hba

theorem transvection_commute (i j k l : ι)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    Commute (transvection i j a) (transvection k l b) := by
  show transvection i j a * transvection k l b =
    transvection k l b * transvection i j a
  simp only [transvection, mul_add, add_mul, mul_one, one_mul,
    Matrix.single_mul_single_of_ne a i j k hjk b,
    Matrix.single_mul_single_of_ne b k l i hli a]
  abel

def diagonalUnit (d : ι → Rˣ) : (Matrix ι ι R)ˣ where
  val := Matrix.diagonal (fun i => (d i : R))
  inv := Matrix.diagonal (fun i => ((d i)⁻¹ : Rˣ))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

theorem diagonal_single_conjugation (d : ι → Rˣ) (i j : ι) (a : R) :
    (diagonalUnit d : Matrix ι ι R) * Matrix.single i j a *
      ((diagonalUnit d)⁻¹ : (Matrix ι ι R)ˣ) =
      Matrix.single i j ((d i : R) * a * ((d j)⁻¹ : Rˣ)) := by
  ext k l
  change (Matrix.diagonal (fun s => (d s : R)) * Matrix.single i j a *
      Matrix.diagonal (fun s => (((d s)⁻¹ : Rˣ) : R))) k l = _
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hi : i=k <;> by_cases hj : j=l <;>
    simp [hi, hj]

theorem diagonal_transvection_conjugation (d : ι → Rˣ) (i j : ι) (a : R) :
    (diagonalUnit d : Matrix ι ι R) * transvection i j a *
      ((diagonalUnit d)⁻¹ : (Matrix ι ι R)ˣ) =
      transvection i j ((d i : R) * a * ((d j)⁻¹ : Rˣ)) := by
  simp only [transvection,mul_add,add_mul,mul_one,Units.mul_inv,diagonal_single_conjugation]

theorem diagonalUnit_commute (d e : ι → Rˣ) : Commute (diagonalUnit d) (diagonalUnit e) := by
  apply Units.ext
  exact (Matrix.commute_diagonal (d₁ := fun i => (d i : R))
    (d₂ := fun i => (e i : R))).eq

theorem transvectionUnit_commute (i j k l : ι) (hij : i≠j) (hkl : k≠l)
    (hjk : j≠k) (hli : l≠i) (a b : R) :
    Commute (transvectionUnit i j hij a) (transvectionUnit k l hkl b) := by
  apply Units.ext
  exact (transvection_commute i j k l hjk hli a b).eq

open scoped commutatorElement in
theorem transvectionUnit_commutator (i j k : ι)
    (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    ⁅transvectionUnit i j hij a,transvectionUnit j k hjk b⁆ =
      transvectionUnit i k hik (a*b) := by
  apply Units.ext
  exact transvection_commutator i j k hij hjk hik a b

theorem transvectionUnit_conjugation (d : ι → Rˣ) (i j : ι) (hij : i≠j) (a : R) :
    diagonalUnit d * transvectionUnit i j hij a * (diagonalUnit d)⁻¹ =
      transvectionUnit i j hij ((d i : R) * a * ((d j)⁻¹ : Rˣ)) := by
  apply Units.ext
  exact diagonal_transvection_conjugation d i j a

end ElementaryMatrices

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_MatrixModel
attribute [-instance] _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped commutatorElement

namespace LittleFinitistic

def internalIndex (i : Fin 3) : Fin 5 := ⟨i.val+1,by omega⟩

@[simp] theorem internalIndex_ne_zero (i : Fin 3) : internalIndex i ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val+1=0 at hv
  omega
@[simp] theorem internalIndex_ne_four (i : Fin 3) : internalIndex i ≠ 4 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val+1=4 at hv
  omega
@[simp] theorem internalIndex_inj (i j : Fin 3) : internalIndex i = internalIndex j ↔ i=j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change i.val+1=j.val+1 at hv
    omega
  · rintro rfl
    rfl

section MatrixRepresentation

variable {R : Type*} [CommRing R]


def matrixU (r : Rˣ) (i : Fin 3) (a : ℤ) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  transvectionUnit 0 (internalIndex i) (Ne.symm (internalIndex_ne_zero i)) (↑(r^a) : R)

def matrixV (r : Rˣ) (i : Fin 3) (a : ℤ) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  transvectionUnit (internalIndex i) 4 (internalIndex_ne_four i) (↑(r^a) : R)

def matrixW (r : Rˣ) (i j : Fin 3) (a : ℤ) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  if h : i=j then 1 else
    transvectionUnit (internalIndex i) (internalIndex j) (by simpa using h) (↑(r^a) : R)

def matrixT (r : Rˣ) (i : Fin 3) : (Matrix (Fin 5) (Fin 5) R)ˣ :=
  diagonalUnit (fun j => if j=internalIndex i then r else 1)

theorem matrixU_square [CharP R 2] (r : Rˣ) (i : Fin 3) (a : ℤ) : matrixU r i a * matrixU r i a = 1 := by
  apply Units.ext
  change transvection 0 (internalIndex i) (↑(r^a) : R) *
      transvection 0 (internalIndex i) (↑(r^a) : R) = 1
  rw [transvection_same 0 (internalIndex i) (Ne.symm (internalIndex_ne_zero i))]
  simp [CharTwo.add_self_eq_zero,transvection]

theorem matrix_UU_commute (r : Rˣ) (i j : Fin 3) (a b : ℤ) :
    Commute (matrixU r i a) (matrixU r j b) := by
  exact transvectionUnit_commute _ _ _ _ _ _
    (internalIndex_ne_zero i) (internalIndex_ne_zero j) _ _

theorem matrix_VV_commute (r : Rˣ) (i j : Fin 3) (a b : ℤ) :
    Commute (matrixV r i a) (matrixV r j b) := by
  exact transvectionUnit_commute _ _ _ _ _ _
    (Ne.symm (internalIndex_ne_four j)) (Ne.symm (internalIndex_ne_four i)) _ _

theorem matrix_UV_commute (r : Rˣ) (i j : Fin 3) (a b : ℤ) (hij : i≠j) :
    Commute (matrixU r i a) (matrixV r j b) := by
  exact transvectionUnit_commute _ _ _ _ _ _ (by simpa using hij) (by decide) _ _

theorem matrix_WU_commute (r : Rˣ) (i j h : Fin 3) (a b : ℤ) (hhi : h≠i) :
    Commute (matrixW r i j a) (matrixU r h b) := by
  unfold matrixW
  split_ifs with hij
  · exact Commute.one_left _
  · exact transvectionUnit_commute _ _ _ _ _ _
      (internalIndex_ne_zero j) (by simpa using hhi) _ _

theorem matrix_WV_commute (r : Rˣ) (i j h : Fin 3) (a b : ℤ) (hhj : h≠j) :
    Commute (matrixW r i j a) (matrixV r h b) := by
  unfold matrixW
  split_ifs with hij
  · exact Commute.one_left _
  · exact transvectionUnit_commute _ _ _ _ _ _
      (by simpa using hhj.symm) (Ne.symm (internalIndex_ne_four i)) _ _

theorem matrix_TT_commute (r : Rˣ) (i j : Fin 3) : Commute (matrixT r i) (matrixT r j) :=
  diagonalUnit_commute _ _

theorem matrix_W_diagonal (r : Rˣ) (i : Fin 3) (a : ℤ) : matrixW r i i a = 1 := by
  simp [matrixW]

theorem matrix_TU_conjugation (r : Rˣ) (l i : Fin 3) (a : ℤ) :
    matrixT r l * matrixU r i a * (matrixT r l)⁻¹ =
      matrixU r i (a-if l=i then 1 else 0) := by
  unfold matrixT matrixU
  rw [transvectionUnit_conjugation]
  have h0 : (0 : Fin 5) ≠ internalIndex l := (internalIndex_ne_zero l).symm
  by_cases h : l=i
  · subst l
    simp [h0,zpow_sub]
  · have hi : internalIndex i ≠ internalIndex l := by simpa using Ne.symm h
    simp [h0,hi,h]

theorem matrix_TV_conjugation (r : Rˣ) (l i : Fin 3) (a : ℤ) :
    matrixT r l * matrixV r i a * (matrixT r l)⁻¹ =
      matrixV r i (a+if l=i then 1 else 0) := by
  unfold matrixT matrixV
  rw [transvectionUnit_conjugation]
  have h4 : (4 : Fin 5) ≠ internalIndex l := (internalIndex_ne_four l).symm
  by_cases h : l=i
  · subst l
    simp [h4,zpow_add,mul_comm]
  · have hi : internalIndex i ≠ internalIndex l := by simpa using Ne.symm h
    simp [h4,hi,h]


end MatrixRepresentation

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_SelectionCharacter
attribute [-instance] _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace LittleFinitistic

noncomputable def parityValue (a : ZMod 2) : ℂˣ := if a = 0 then 1 else -1

@[simp] theorem parityValue_zero : parityValue 0 = 1 := by simp [parityValue]
@[simp] theorem parityValue_one : parityValue 1 = -1 := by norm_num [parityValue]

theorem parityValue_add (a b : ZMod 2) : parityValue (a+b) = parityValue a * parityValue b := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl,parityValue_zero,parityValue_one]
    simp

def lastIndex (m : ℕ) [NeZero m] : Fin m := ⟨m-1,by have := NeZero.ne m; omega⟩

noncomputable def selectionCharacter (m : ℕ) [NeZero m] :
    Multiplicative (Fin m → ZMod 2) →* ℂˣ where
  toFun c := parityValue (c.toAdd (lastIndex m))
  map_one' := parityValue_zero
  map_mul' first second := parityValue_add (first.toAdd (lastIndex m))
    (second.toAdd (lastIndex m))

@[simp] theorem selectionCharacter_basis (m : ℕ) [NeZero m] (i : Fin m) :
    selectionCharacter m (Multiplicative.ofAdd (Pi.single i 1)) =
      if i = lastIndex m then -1 else 1 := by
  classical
  change parityValue ((Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) (lastIndex m)) = _
  by_cases h : i = lastIndex m
  · subst i
    simp
  · simp [h,Ne.symm h]

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedCohomologyAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.SelectedCohomologyAssembly
open QuadraticEncoding
section General
variable {C : Type*} [Category C]
variable {X0 X1 M0 M1 N0 N1 : C}
lemma transfer_square (f : X0 ⟶ X1) (m : M0 ⟶ M1) (n : N0 ⟶ N1)
    (c0 : X0 ≅ M0) (c1 : X1 ≅ M1) (e0 : X0 ≅ N0) (e1 : X1 ≅ N1)
    (hc : f ≫ c1.hom = c0.hom ≫ m) (he : f ≫ e1.hom = e0.hom ≫ n) :
    m ≫ (c1.symm ≪≫ e1).hom = (c0.symm ≪≫ e0).hom ≫ n := by
  apply (cancel_epi c0.hom).1
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  calc
    c0.hom ≫ m ≫ c1.inv ≫ e1.hom = (c0.hom ≫ m) ≫ c1.inv ≫ e1.hom := by simp only [Category.assoc]
    _ = (f ≫ c1.hom) ≫ c1.inv ≫ e1.hom := by rw [← hc]
    _ = f ≫ e1.hom := by simp
    _ = e0.hom ≫ n := he
    _ = c0.hom ≫ (c0.inv ≫ e0.hom) ≫ n := by simp
end General

end LittleFinitistic.SelectedCohomologyAssembly

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedReferenceCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.SelectedReferenceCohomology
open QuadraticEncoding

lemma transfer_to_vertices {C : Type*} [Category C]
    {A₀ A₁ B₀ B₁ Y₀ Y₁ : C} (f : A₀ ⟶ A₁) (g : B₀ ⟶ B₁) (h : Y₀ ⟶ Y₁)
    (e₀ : A₀ ≅ Y₀) (e₁ : A₁ ≅ Y₁) (v₀ : B₀ ≅ Y₀) (v₁ : B₁ ≅ Y₁)
    (hf : f ≫ e₁.hom = e₀.hom ≫ h) (hg : g ≫ v₁.hom = v₀.hom ≫ h) :
    f ≫ (e₁ ≪≫ v₁.symm).hom = (e₀ ≪≫ v₀.symm).hom ≫ g := by
  apply (cancel_mono v₁.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [hg, Iso.inv_hom_id_assoc]
  exact hf

end LittleFinitistic.SelectedReferenceCohomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTargetHomology
attribute [-instance] _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedTargetHomology
open QuadraticEncoding FiniteProjectiveHomotopy
universe v
variable {Y : Type v}
  [AddCommGroup Y]
  [Module ℂ Y]
  [FiniteDimensional ℂ Y]
abbrev C := ModuleCat.{v} ℂ
abbrev I := derivedTargetInclusion.{0,v} (k := ℂ)
abbrev cohomology (n : ℤ) := I ⋙ DerivedCategory.homologyFunctor C n
instance instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology (n : ℤ) : (cohomology.{v} n).Additive := by dsimp [cohomology]; infer_instance

lemma single_zero (M : C) (i n : ℤ) (hn : n ≠ i) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj
      ((DerivedCategory.singleFunctor C i).obj M)) := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact DerivedCategory.isZero_of_isGE _ i n h
  · exact DerivedCategory.isZero_of_isLE _ i n h
end LittleFinitistic.SelectedTargetHomology

end

end OAI
end


