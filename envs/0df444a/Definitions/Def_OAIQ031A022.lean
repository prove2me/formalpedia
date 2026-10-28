-- Prove2me | Definitions.Def_OAIQ031A022
-- name    : OAIQ031A022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:57:41.024581+00:00
-- url     : https://prove2.me/theorems/ca54580b-1d8d-45f1-ba7e-d22d8ba07df9
-- title:
--   Definitions bundle OAIQ031A022 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 3 definitions, 1 instance and 13 theorems. The definitions and types are `OAI.ArExplicit.coneComparisonCochain`, `OAI.ArExplicit.fullHomZeroRepresentative`, `OAI.ArExplicit.mappedBiproductHomEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ConcreteNativeBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ConcreteNativeBar.lean), [`AuslanderReiten_Cones_ConeCohomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeCohomology.lean), [`AuslanderReiten_Cones_ConeComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeComparison.lean), [`AuslanderReiten_Coordinates_GradedRowCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/GradedRowCoordinates.lean), [`AuslanderReiten_Coordinates_MappedBiproductHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/MappedBiproductHom.lean), [`AuslanderReiten_Coordinates_ShiftedBoundaryComponents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ShiftedBoundaryComponents.lean), [`AuslanderReiten_Evaluation_EvaluatedConnectingCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedConnectingCoordinates.lean), [`AuslanderReiten_HomComplex_FullHomZeroRepresentative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomZeroRepresentative.lean), [`AuslanderReiten_Homology_TriangleConnectingProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TriangleConnectingProduct.lean), [`AuslanderReiten_Resolutions_ConcreteKoszulColumn`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ConcreteKoszulColumn.lean), [`AuslanderReiten_Triangular_TriangularProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularProjective.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A041`, `OAIQ031A042` and `OAIQ031A043`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ConcreteNativeBar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

theorem compose_native_squares {Cat : Type*} [Category Cat]
    {source middle target source' middle' target' : Cat}
    {sourceMap : source ⟶ source'} {middleMap : middle ⟶ middle'}
    {targetMap : target ⟶ target'} {first : source ⟶ middle}
    {first' : source' ⟶ middle'} {second : middle ⟶ target}
    {second' : middle' ⟶ target'}
    (firstSquare : sourceMap ≫ first' = first ≫ middleMap)
    (secondSquare : middleMap ≫ second' = second ≫ targetMap) :
    sourceMap ≫ (first' ≫ second') = (first ≫ second) ≫ targetMap := by
  rw [← Category.assoc, firstSquare, Category.assoc, secondSquare, ← Category.assoc]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

def coneComparisonCochain : (Cochain G G n × Cochain F F n) →ₗ[ℤ] Cochain F G n where
  toFun x := x.2.comp (Cochain.ofHom φ) (add_zero n) +
    (n + 1).negOnePow • (Cochain.ofHom φ).comp x.1 (zero_add n)
  map_add' x y := by simp [smul_add]; abel
  map_smul' r x := by simp [smul_add, smul_comm r (n + 1).negOnePow]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

theorem cohomology_eq_iff (x y : Cocycle F G n) :
    CohomologyClass.mk x = CohomologyClass.mk y ↔
      ∃ e : Cochain F G (n - 1), δ (n - 1) n e = x.1 - y.1 := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ShiftedBoundaryComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X U V W Z : C}

theorem shiftedComp_pre (a : ℤ) (v : X ⟶ U⟦a⟧) (p : U ⟶ V)
    (s : V ⟶ W⟦(1 : ℤ)⟧) :
    ShiftedHom.comp v (p ≫ s) (add_comm 1 a) =
      ShiftedHom.comp (v ≫ p⟦a⟧') s (add_comm 1 a) := by
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]

theorem shiftedComp_post (a : ℤ) (v : X ⟶ U⟦a⟧)
    (s : U ⟶ W⟦(1 : ℤ)⟧) (c : W ⟶ Z) :
    ShiftedHom.comp v (s ≫ c⟦(1 : ℤ)⟧') (add_comm 1 a) =
      ShiftedHom.comp v s (add_comm 1 a) ≫ c⟦a+1⟧' := by
  have h := ShiftedHom.comp_assoc v s (ShiftedHom.mk₀ (0 : ℤ) rfl c)
    (add_comm 1 a) (by omega : (0 : ℤ)+1=1) (by omega : (0 : ℤ)+1+a=a+1)
  simpa only [ShiftedHom.comp_mk₀] using h.symm

theorem shiftedComp_prepost (a : ℤ) (v : X ⟶ U⟦a⟧) (p : U ⟶ V)
    (s : V ⟶ W⟦(1 : ℤ)⟧) (c : W ⟶ Z) :
    ShiftedHom.comp v ((p ≫ s) ≫ c⟦(1 : ℤ)⟧') (add_comm 1 a) =
      ShiftedHom.comp (v ≫ p⟦a⟧') s (add_comm 1 a) ≫ c⟦a+1⟧' := by
  rw [shiftedComp_post, shiftedComp_pre]

variable [Preadditive C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]

theorem shiftedComp_row (a : ℤ) (v : X ⟶ U⟦a⟧) (p r : U ⟶ V)
    (s : V ⟶ W⟦(1 : ℤ)⟧) (c d : W ⟶ Z) :
    ShiftedHom.comp v (((p ≫ s) ≫ c⟦(1 : ℤ)⟧') + ((r ≫ s) ≫ d⟦(1 : ℤ)⟧'))
        (add_comm 1 a) =
      (ShiftedHom.comp (v ≫ p⟦a⟧') s (add_comm 1 a) ≫ c⟦a+1⟧') +
      (ShiftedHom.comp (v ≫ r⟦a⟧') s (add_comm 1 a) ≫ d⟦a+1⟧') := by
  rw [ShiftedHom.comp_add, shiftedComp_prepost, shiftedComp_prepost]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleConnectingProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace ArExplicit.TriangleGradedSequence
universe u v w
variable (k : Type u) [CommRing k] [CharP k 2]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
variable (T : Triangle C) (X : C)

theorem integerUnit_smul {M : Type*} [AddCommGroup M] [Module k M]
    (s : ℤˣ) (x : M) : s • x = x := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact one_smul _ x
  · change (-1 : ℤ) • x = x
    rw [neg_one_zsmul]
    apply neg_eq_iff_add_eq_zero.mpr
    rw [← two_smul k, show (2 : k) = 0 from CharP.cast_eq_zero k 2, zero_smul]

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_GradedRowCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w

theorem additiveRowCoordinates
    {G H I J : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup I]
    (e : G →+ H) (d : I →+ H) (f g : J → I)
    {w w₁ w₂ : G} {x₁ x₂ m₁ m₂ : J}
    (hw : w = w₁ + w₂) (h₁ : e w₁ = d (f x₁)) (h₂ : e w₂ = d (g x₂))
    (hm₁ : m₁ = x₁) (hm₂ : m₂ = x₂) :
    e w = d (f m₁ + g m₂) := by
  rw [hw, map_add, h₁, h₂, hm₁, hm₂, map_add]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_MappedBiproductHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Limits
universe u v w v' w'
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {D : Type w'} [Category.{v'} D] [Preadditive D] [Linear k D]
variable (F : C ⥤ D) [F.Additive] (X : D) (Y Z : C) [HasBinaryBiproduct Y Z]

def mappedBiproductHomEquiv : (X ⟶ F.obj (Y ⊞ Z)) ≃ₗ[k]
    ((X ⟶ F.obj Y) × (X ⟶ F.obj Z)) where
  toFun f := (f ≫ F.map biprod.fst, f ≫ F.map biprod.snd)
  invFun p := p.1 ≫ F.map biprod.inl + p.2 ≫ F.map biprod.inr
  left_inv f := by
    dsimp
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      ← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id, Category.comp_id]
  right_inv p := by
    ext <;> simp [Preadditive.add_comp, Category.assoc, ← F.map_comp]
  map_add' f g := by ext <;> simp [Preadditive.add_comp]
  map_smul' a f := by ext <;> simp

@[simp] theorem mappedBiproductHomEquiv_fst (f : X ⟶ F.obj (Y ⊞ Z)) :
    (mappedBiproductHomEquiv k F X Y Z f).1 = f ≫ F.map biprod.fst := rfl

@[simp] theorem mappedBiproductHomEquiv_snd (f : X ⟶ F.obj (Y ⊞ Z)) :
    (mappedBiproductHomEquiv k F X Y Z f).2 = f ≫ F.map biprod.snd := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedConnectingCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u v
theorem rowBoundary {C : Type u} [Category.{v} C] [Preadditive C]
    (F : C ⥤ C) [F.Additive] {U V W B : C}
    (a b : U ⟶ V) (t : V ⟶ F.obj W) (s : U ⟶ F.obj B)
    (p r : B ⟶ W) {Z : C} (c d : W ⟶ Z) (row : B ⟶ Z)
    (delta : U ⟶ F.obj Z) (hrow : row = p ≫ c + r ≫ d)
    (hdelta : delta = s ≫ F.map row)
    (ha : a ≫ t = s ≫ F.map p) (hb : b ≫ t = s ≫ F.map r) :
    delta = (a ≫ t) ≫ F.map c + (b ≫ t) ≫ F.map d := by
  rw [hdelta, hrow, F.map_add, F.map_comp, F.map_comp, Preadditive.comp_add, ha, hb]
  simp only [Category.assoc]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomZeroRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {K L : CochainComplex C ℤ}

def fullHomZeroRepresentative (x : CohomologyClass K L 0) : K ⟶ L :=
  Cocycle.homOf (Classical.choose (CohomologyClass.mk_surjective x))

@[simp] theorem fullHomZeroRepresentative_class (x : CohomologyClass K L 0) :
    CohomologyClass.mk (Cocycle.ofHom (fullHomZeroRepresentative x)) = x := by
  rw [fullHomZeroRepresentative, Cocycle.ofHom_homOf_eq_self]
  exact Classical.choose_spec (CohomologyClass.mk_surjective x)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ConcreteKoszulColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

theorem columnNeg {M : Type u} [AddCommGroup M] [Module k M] (x : M) : -x=x := by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [← two_smul k, show (2:k)=0 from CharP.cast_eq_zero k 2, zero_smul]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

instance finitePiProjective {S P ι : Type*} [Ring S] [AddCommGroup P]
    [Module S P] [Module.Projective S P] [Fintype ι] : Module.Projective S (ι → P) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype :
    (Π₀ _ : ι, P) ≃ₗ[S] (ι → P))

end ArExplicit.TriangularInduction

end

end OAI
end


