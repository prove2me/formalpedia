-- Prove2me | Definitions.Def_OAIQ031A075
-- name    : OAIQ031A075
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:18:28.07071+00:00
-- url     : https://prove2.me/theorems/3ebbb90c-3837-4fd0-b533-bdff104506cd
-- title:
--   Definitions bundle OAIQ031A075 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 6 definitions, 1 inductive type or structure, 5 instances and 18 theorems. The definitions and types are `OAI.ArExplicit.TriangularModule`, `OAI.ArExplicit.TriangularModule.bottomMap`, `OAI.ArExplicit.TriangularModule.coordinateAddEquiv`, `OAI.ArExplicit.TriangularModule.coordinates`, `OAI.ArExplicit.TriangularModule.hom`, `OAI.ArExplicit.TriangularModule.topMap`, `OAI.ArExplicit.twoTriangleHomFiltration`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_TensorFrobenius`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorFrobenius.lean), [`AuslanderReiten_Cones_TwoTriangleFiltration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoTriangleFiltration.lean), [`AuslanderReiten_Coordinates_CubicShiftNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/CubicShiftNaturality.lean), [`AuslanderReiten_Triangular_TriangularHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularHom.lean), [`AuslanderReiten_Triangular_TriangularModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularModule.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A047`, `OAIQ031A049`, `OAIQ031A057`, `OAIQ031A058` and `OAIQ031A059` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A089` and `OAIQ031A090`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A047
import Definitions.Def_OAIQ031A049
import Definitions.Def_OAIQ031A057
import Definitions.Def_OAIQ031A058
import Definitions.Def_OAIQ031A059

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorFrobenius
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

instance instInjectiveA (k : Type*) [Field k] (q : k) : Module.Injective (A k q) (A k q) :=
  (AFrobeniusTrace k q).regular_injective

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoTriangleFiltration
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit

universe u w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable {B D E K W : C} (X : C)
variable (f : B ⟶ K) (g : K ⟶ D) (δ : D ⟶ B⟦(1 : ℤ)⟧)
variable (i : K ⟶ W) (p : W ⟶ E) (ε : E ⟶ K⟦(1 : ℤ)⟧)
variable (h₁ : Triangle.mk f g δ ∈ distTriang C)
variable (h₂ : Triangle.mk i p ε ∈ distTriang C)

def twoTriangleHomFiltration :
    TwoConeFiltration (k := k) (fun n => X ⟶ B⟦n⟧) (fun n => X ⟶ D⟦n⟧)
      (fun n => X ⟶ E⟦n⟧) (fun n => X ⟶ K⟦n⟧) (fun n => X ⟶ W⟦n⟧) where
  row := TriangleGradedSequence.connecting k (Triangle.mk f g δ) X
  column n := (TriangleGradedSequence.second k (Triangle.mk f g δ) X (n + 1)).comp
    (TriangleGradedSequence.connecting k (Triangle.mk i p ε) X n)
  bottom := TriangleGradedSequence.first k (Triangle.mk f g δ) X
  middle := TriangleGradedSequence.second k (Triangle.mk f g δ) X
  attach := TriangleGradedSequence.connecting k (Triangle.mk i p ε) X
  inclusion := TriangleGradedSequence.first k (Triangle.mk i p ε) X
  projection := TriangleGradedSequence.second k (Triangle.mk i p ε) X
  row_bottom := TriangleGradedSequence.exact_next k _ X h₁
  bottom_middle := TriangleGradedSequence.exact_middle k _ X h₁
  middle_row := TriangleGradedSequence.exact_top k _ X h₁
  attach_inclusion := TriangleGradedSequence.exact_next k _ X h₂
  inclusion_projection := TriangleGradedSequence.exact_middle k _ X h₂
  projection_attach := TriangleGradedSequence.exact_top k _ X h₂
  adjacent _ := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_CubicShiftNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)
variable {X S : C} (u : X ≅ Y 0) (c : ∀ n, Y (n+3) ⟶ Y n)

variable (hs : ∀ n, c n ≫ (s n).hom =
  (s (n+3)).hom ≫ (c (n+1))⟦(1 : ℤ)⟧')
include hs

theorem coverCubic_square (n : ℕ) :
    ShiftedHom.comp (coverCubic Y s u c) (basedIteration Y s u n).hom
        (by omega : (n : ℤ)+3=((n+3 : ℕ) : ℤ)) =
      ShiftedHom.comp (basedIteration Y s u (n+3)).hom
        (ShiftedHom.mk₀ (0 : ℤ) rfl (c n)) (by omega) := by
  have hn := iteratedShiftIso_natural (Y := fun j => Y (j+3))
    (s := fun j => s (j+3)) s c hs n
  have hbase : (c 0 ≫ u.inv) ≫ (basedIteration Y s u n).hom =
      (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) n).hom ≫
        (c n)⟦(n : ℤ)⟧' := by
    simpa only [basedIteration, Iso.trans_hom, Category.assoc,
      Iso.inv_hom_id_assoc] using hn
  erw [coverCubic, ← ShiftedHom.comp_mk₀ (basedIteration Y s u 3).hom (0 : ℤ) rfl (c 0 ≫ u.inv)]
  change ShiftedHom.comp
    (ShiftedHom.comp (basedIteration Y s u 3).hom
      (ShiftedHom.mk₀ (0 : ℤ) rfl (c 0 ≫ u.inv)) (by omega : (0 : ℤ)+3=3))
    (basedIteration Y s u n).hom _ = _
  rw [ShiftedHom.comp_assoc (basedIteration Y s u 3).hom
    (ShiftedHom.mk₀ (0 : ℤ) rfl (c 0 ≫ u.inv)) (basedIteration Y s u n).hom
    (by omega : (0 : ℤ)+3=3) (by omega : (n : ℤ)+0=n) (by omega),
    ShiftedHom.mk₀_comp, hbase]
  rw [basedIteration_three_hom Y s u n]
  rw [ShiftedHom.comp_assoc (basedIteration Y s u 3).hom
    (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) n).hom
    (ShiftedHom.mk₀ (0 : ℤ) rfl (c n)) (by omega) (by omega : 0+(n : ℤ)=n) (by omega),
    ShiftedHom.comp_mk₀]

theorem coverCubic_eq_conjugate (n : ℕ) :
    gradedConjugate (n : ℤ) ((n+3 : ℕ) : ℤ) 3 (by omega)
      (basedIteration Y s u n) (basedIteration Y s u (n+3)) (c n) =
      coverCubic Y s u c :=
  gradedConjugate_eq_of_square _ _ _ _ _ _ _ _ (coverCubic_square Y s u c hs n)

theorem coverCubic_action (n : ℕ) (a : ℤ) (v : S ⟶ (Y (n+3))⟦a⟧) :
    ShiftedHom.comp (v ≫ (c n)⟦a⟧')
        (negativeShiftIso (n : ℤ) (basedIteration Y s u n)).hom (by omega) =
      ShiftedHom.comp
        (ShiftedHom.comp v
          (negativeShiftIso ((n+3 : ℕ) : ℤ) (basedIteration Y s u (n+3))).hom
          (by omega : -((n+3 : ℕ) : ℤ)+a=a-((n+3 : ℕ) : ℤ)))
        (coverCubic Y s u c) (by omega : 3+(a-((n+3 : ℕ) : ℤ))=a-(n : ℤ)) := by
  rw [← coverCubic_eq_conjugate Y s u c hs n]
  exact gradedConjugate_action _ _ _ _ _ _ _ a v

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable (k R F M N : Type*) [CommRing k] [Ring R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [AddCommGroup N] [Module R N]

@[ext] structure TriangularModule (φ : BalancedTensor k R F M →ₗ[R] N) where
  top : M
  bottom : N

namespace TriangularModule

variable {k R F M N}
variable (φ : BalancedTensor k R F M →ₗ[R] N)

def coordinates : TriangularModule k R F M N φ ≃ M × N where
  toFun x := (x.top, x.bottom)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (TriangularModule k R F M N φ) := (coordinates φ).addCommGroup

def coordinateAddEquiv : TriangularModule k R F M N φ ≃+ M × N where
  __ := coordinates φ
  map_add' _ _ := rfl

@[simp] theorem top_add (x y : TriangularModule k R F M N φ) : (x + y).top = x.top + y.top := rfl
@[simp] theorem bottom_add (x y : TriangularModule k R F M N φ) :
    (x + y).bottom = x.bottom + y.bottom := rfl
@[simp] theorem top_zero : (0 : TriangularModule k R F M N φ).top = 0 := rfl
@[simp] theorem bottom_zero : (0 : TriangularModule k R F M N φ).bottom = 0 := rfl

instance instSMulTriangular : SMul (Triangular R F) (TriangularModule k R F M N φ) :=
  ⟨fun a x => ⟨a.top • x.top, φ (BalancedTensor.tmul a.off x.top) + a.bottom • x.bottom⟩⟩

@[simp] theorem top_smul (a : Triangular R F) (x : TriangularModule k R F M N φ) :
    (a • x).top = a.top • x.top := rfl
@[simp] theorem bottom_smul (a : Triangular R F) (x : TriangularModule k R F M N φ) :
    (a • x).bottom = φ (BalancedTensor.tmul a.off x.top) + a.bottom • x.bottom := rfl

instance instModuleTriangular : Module (Triangular R F) (TriangularModule k R F M N φ) where
  one_smul x := by ext <;> simp
  mul_smul a b x := by
    ext
    · exact mul_smul a.top b.top x.top
    · simp only [bottom_smul, top_smul, Triangular.off_mul, Triangular.bottom_mul,
        BalancedTensor.add_tmul, BalancedTensor.balance, map_add, mul_smul, smul_add]
      rw [← BalancedTensor.smul_tmul, φ.map_smul]
      abel
  smul_add a x y := by
    ext <;> simp [BalancedTensor.tmul_add, smul_add, add_add_add_comm]
  smul_zero a := by ext <;> simp
  add_smul a b x := by
    ext <;> simp [BalancedTensor.add_tmul, add_smul, add_add_add_comm]
  zero_smul x := by ext <;> simp

section Scalars

variable [Module k N]

instance instModule : Module k (TriangularModule k R F M N φ) := (coordinateAddEquiv φ).module k

@[simp] theorem top_scalar (c : k) (x : TriangularModule k R F M N φ) :
    (c • x).top = c • x.top := rfl
@[simp] theorem bottom_scalar (c : k) (x : TriangularModule k R F M N φ) :
    (c • x).bottom = c • x.bottom := rfl

end Scalars

end TriangularModule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TriangularModule

variable {k R F M N M' N' : Type*} [CommRing k] [Ring R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup M'] [Module k M'] [Module R M']
variable [AddCommGroup N'] [Module R N']
variable {φ : BalancedTensor k R F M →ₗ[R] N}
variable {ψ : BalancedTensor k R F M' →ₗ[R] N'}

def hom (a : M →ₗ[R] M') (b : N →ₗ[R] N')
    (h : ∀ f m, b (φ (BalancedTensor.tmul f m)) = ψ (BalancedTensor.tmul f (a m))) :
    TriangularModule k R F M N φ →ₗ[Triangular R F] TriangularModule k R F M' N' ψ where
  toFun x := ⟨a x.top, b x.bottom⟩
  map_add' x y := by ext <;> simp
  map_smul' t x := by
    ext
    · exact a.map_smul t.top x.top
    · simp only [bottom_smul, map_add, h, map_smul, RingHom.id_apply]

@[simp] theorem hom_top (a : M →ₗ[R] M') (b : N →ₗ[R] N')
    (h : ∀ f m, b (φ (BalancedTensor.tmul f m)) = ψ (BalancedTensor.tmul f (a m)))
    (x : TriangularModule k R F M N φ) : (hom a b h x).top = a x.top := rfl

@[simp] theorem hom_bottom (a : M →ₗ[R] M') (b : N →ₗ[R] N')
    (h : ∀ f m, b (φ (BalancedTensor.tmul f m)) = ψ (BalancedTensor.tmul f (a m)))
    (x : TriangularModule k R F M N φ) : (hom a b h x).bottom = b x.bottom := rfl

variable (g : TriangularModule k R F M N φ →ₗ[Triangular R F] TriangularModule k R F M' N' ψ)

theorem top_of_map (x : TriangularModule k R F M N φ) :
    (g ⟨x.top, 0⟩).top = (g x).top := by
  have h := congrArg TriangularModule.top (g.map_smul (⟨1, 0, 0⟩ : Triangular R F) x)
  have he : (⟨1, 0, 0⟩ : Triangular R F) • x = ⟨x.top, 0⟩ := by ext <;> simp
  rw [he] at h
  simpa using h

theorem bottom_of_map (x : TriangularModule k R F M N φ) :
    (g ⟨0, x.bottom⟩).bottom = (g x).bottom := by
  have h := congrArg TriangularModule.bottom (g.map_smul (⟨0, 1, 0⟩ : Triangular R F) x)
  have he : (⟨0, 1, 0⟩ : Triangular R F) • x = ⟨0, x.bottom⟩ := by ext <;> simp
  rw [he] at h
  simpa using h

def topMap : M →ₗ[R] M' where
  toFun m := (g ⟨m, 0⟩).top
  map_add' m n := by
    have h : (⟨m + n, 0⟩ : TriangularModule k R F M N φ) = ⟨m, 0⟩ + ⟨n, 0⟩ := by
      ext <;> simp
    rw [h]
    rw [g.map_add]
    rfl
  map_smul' r m := by
    have h := congrArg TriangularModule.top
      (g.map_smul (⟨r, 0, 0⟩ : Triangular R F) ⟨m, 0⟩)
    have he : (⟨r, 0, 0⟩ : Triangular R F) •
        (⟨m, 0⟩ : TriangularModule k R F M N φ) = ⟨r • m, 0⟩ := by ext <;> simp
    rw [he] at h
    exact h

def bottomMap : N →ₗ[R] N' where
  toFun n := (g ⟨0, n⟩).bottom
  map_add' m n := by
    have h : (⟨0, m + n⟩ : TriangularModule k R F M N φ) = ⟨0, m⟩ + ⟨0, n⟩ := by
      ext <;> simp
    rw [h]
    rw [g.map_add]
    rfl
  map_smul' r n := by
    have h := congrArg TriangularModule.bottom
      (g.map_smul (⟨0, r, 0⟩ : Triangular R F) ⟨0, n⟩)
    have he : (⟨0, r, 0⟩ : Triangular R F) •
        (⟨0, n⟩ : TriangularModule k R F M N φ) = ⟨0, r • n⟩ := by ext <;> simp
    rw [he] at h
    simpa using h

@[simp] theorem topMap_apply (m : M) : topMap g m = (g ⟨m, 0⟩).top := rfl
@[simp] theorem bottomMap_apply (n : N) : bottomMap g n = (g ⟨0, n⟩).bottom := rfl

theorem compatibility (f : F) (m : M) :
    bottomMap g (φ (BalancedTensor.tmul f m)) = ψ (BalancedTensor.tmul f (topMap g m)) := by
  have h := congrArg TriangularModule.bottom
    (g.map_smul (⟨0, 0, f⟩ : Triangular R F) ⟨m, 0⟩)
  have he : (⟨0, 0, f⟩ : Triangular R F) •
      (⟨m, 0⟩ : TriangularModule k R F M N φ) = ⟨0, φ (BalancedTensor.tmul f m)⟩ := by
    ext <;> simp
  rw [he] at h
  simpa using h

end ArExplicit.TriangularModule

end OAI
end


